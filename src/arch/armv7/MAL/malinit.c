/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2021)                */
/*                                                                             */
/*  This software is a computer program whose purpose is to run a minimal,     */
/*  hypervisor relying on proven properties such as memory isolation.          */
/*                                                                             */
/*  This software is governed by the CeCILL license under French law and       */
/*  abiding by the rules of distribution of free software.  You can  use,      */
/*  modify and/ or redistribute the software under the terms of the CeCILL     */
/*  license as circulated by CEA, CNRS and INRIA at the following URL          */
/*  "http://www.cecill.info".                                                  */
/*                                                                             */
/*  As a counterpart to the access to the source code and  rights to copy,     */
/*  modify and redistribute granted by the license, users are provided only    */
/*  with a limited warranty  and the software's author,  the holder of the     */
/*  economic rights,  and the successive licensors  have only  limited         */
/*  liability.                                                                 */
/*                                                                             */
/*  In this respect, the user's attention is drawn to the risks associated     */
/*  with loading,  using,  modifying and/or developing or reproducing the      */
/*  software by the user in light of its specific status of free software,     */
/*  that may mean  that it is complicated to manipulate,  and  that  also      */
/*  therefore means  that it is reserved for developers  and  experienced      */
/*  professionals having in-depth computer knowledge. Users are therefore      */
/*  encouraged to load and test the software's suitability as regards their    */
/*  requirements in conditions enabling the security of their systems and/or   */
/*  data to be ensured and,  more generally, to use and operate it in the      */
/*  same conditions as regards security.                                       */
/*                                                                             */
/*  The fact that you are presently reading this means that you have had       */
/*  knowledge of the CeCILL license and that you accept its terms.             */
/*******************************************************************************/

#include <stdint.h>

#include "string.h"
#include "mmu.h"
#include "memlayout.h"
#include "context.h"
#include "debug.h"
#include "fpinfo.h"
#include "mal.h"
#include "elf.h"

#define MIN(a,b) ((a)<(b)?(a):(b))

/* Root partition initialisation.
 * All this code will run at startup before MMU is enabled.
 */

uint32_t nbPage = 0;

static void *user_alloc_pos = user_mem_start;

static void* mal_alloc_user(void)
{
	void* res;

	if (user_alloc_pos >= (void*)user_mem_end)
	{
		/* This may never happen, (FIXME: assert) */
		PANIC("No more page to alloc!\n");
	}
	res = user_alloc_pos;
	memset(res, 0, 0x1000);
	user_alloc_pos += 0x1000;

	return res;
}

static unsigned *mal_create_root_part(void)
{
	unsigned *part, *sh1, *sh2, *sh3, *tt;

	part = mal_alloc_user();
	tt = mal_alloc_user();
	sh1 = mal_alloc_user();
	sh2 = mal_alloc_user();
	sh3 = mal_alloc_user();
	/* TODO: fill sh3 with each indirection table */
	*sh3 = 2;

	/* Fill partition descriptor */
	part[0]	= (unsigned)part; /* Partition root */
	part[1]	= (unsigned)part;
	part[2]	= (unsigned)tt;	  /* PD */
	part[3]	= (unsigned)tt;
	part[4]	= (unsigned)sh1;  /* Shadows .. */
	part[5]	= (unsigned)sh1;
	part[6]	= (unsigned)sh2;
	part[7]	= (unsigned)sh2;
	part[8]	= (unsigned)sh3;
	part[9]	= (unsigned)sh3;
	part[10]= (unsigned)0xffffffff;	/* Parent partition */
	part[11]= (unsigned)0;

	/* TODO: do we need to map system pages somewhere ? */
	return part;
}

/* mal_map_kernel: Map kernel directory. As this mapping will never be edited (TODO: proof), we can
 * therefore map it using the *simple* mmu implementation, and avoid useless shadow pt allocations */
void mal_map_kernel(unsigned int *part)
{
	unsigned i;
	void *addr;
	unsigned *tt;

	tt = (unsigned*)part[indexPD()];

	for (addr = kernel_text_start; addr<(void*)kernel_ro_start; addr += 0x1000)
	{
		/* kernel, ro, executable, cacheable, global */
		mmu_map_small_page(tt, addr, addr, 0, 1, 0, 0, 1);
	}
	DEBUG(TRACE, "Map kernel rodata: \t%p - %p\n", kernel_ro_start, kernel_rw_start);
	for (addr = kernel_ro_start; addr<(void*)kernel_rw_start; addr += 0x1000)
	{
		/* kernel, ro, nx, cacheable, global */
		mmu_map_small_page(tt, addr, addr, 0, 1, 1, 0, 1);
	}
	DEBUG(TRACE, "Map kernel data: \t%p - %p\n", kernel_rw_start, kernel_rw_end);
	for (addr = kernel_rw_start; addr<(void*)kernel_rw_end; addr += 0x1000)
	{
		/* kernel, rw, nx, cacheable, global */
		mmu_map_small_page(tt, addr, addr, 0, 0, 1, 0, 1);
	}
	/* XXX DEBUG: runtime assert that only first index was used for kernel mappings */
	for (i=1; i<MMU_TTBR0_ENT_COUNT; i++)
	{
		if (tt[i] != 0)
		{
			PANIC("Pip model not satisfied, kernel must use first MB only");
		}
	}
}

/* mal_prepare_map:  Prepare a mapping by allocating page table & shadows */
static void mal_prepare_map(unsigned *part, unsigned *va)
{
	unsigned idx1;
	unsigned pte, *tt;
	void *pt, **sh1, **sh2, *sh1pt, *sh2pt;

	/* Get translation table & pt index */
	tt = (unsigned*)part[indexPD()];
	idx1 = ((unsigned)va >> 20) & 0x3ff;

	/* Check if it's prepared already */
	pte = tt[idx1];
	if ((pte & 3) == 1)
		return;

	/* Allocate the 3 required pages */
	pt = mal_alloc_user();
	sh1pt = mal_alloc_user();
	sh2pt = mal_alloc_user();

	DEBUG(TRACE, "mal_prepare_map( part=%08x, va=%08x) : sh1pt=%p, sh2pt=%p\n", part,va,sh1pt,sh2pt);

	/* fill the pt and its shadow versions */
	sh1=(void**)part[indexSh1()];
	sh2=(void**)part[indexSh2()];
	sh1[idx1] = sh1pt;
	sh2[idx1] = sh2pt;
	pte = (unsigned)pt | 1;
	tt[idx1] = pte;
}

/* mal_map_in_part: Map the page in the given root partition,
 * assuming mapping is already prepared */
static void mal_map_in_part(unsigned *part, void*pa, unsigned *va, uint8_t user)
{
	unsigned idx1, idx2;
	mmu_sd_pt_t *tt;
	mmu_sd_pt_t pte;
	mmu_sd_sp_t *pt;
	mmu_sd_sp_t l2;

	nbPage++;	/* FIXME: I have no idea what is a correct nbPage */

	tt = (mmu_sd_pt_t*)part[indexPD()];

	idx1 = ((unsigned)va >> 20) & 0x3ff;
	idx2 = ((unsigned)va >> 12) & 0xff;

	pte = tt[idx1];
	if ((pte.aslong & 3) != 1)
	{
		PANIC("map_mal: map not prepared!");
	}
	else{
		pt = (mmu_sd_sp_t*)(pte.aslong &~0xfff);
	}

	l2 = mmu_make_small_page(
		pa,   /* Full address of aligned(12) small page */
		user, /* User accessible */
		0,    /* Read only */
		0,    /* eXecute never */
		0,    /* not device */
		!user /* global flag*/
	);
	pt[idx2] = l2;
}

/* Load given segment in part, starting at given paddr */
static void mal_load_seg(unsigned *part, Elf32_Phdr *phdr, unsigned paddr)
{
	unsigned of, mapsize, tocopy;
	void *ppage, *vaddr;

	/* Total size of mapping */
	mapsize = phdr->p_memsz;
	mapsize = (mapsize + 0xfff) & ~0xfff;

	/* Map executable */
	for (of = 0; of < mapsize; of += 0x1000)
	{
		tocopy = 0;
		ppage = (void*)(paddr + of);
		vaddr = (void*)(phdr->p_vaddr+of);
		if (of < phdr->p_filesz)
		{
			tocopy = MIN(0x1000, phdr->p_filesz - of);
			if (tocopy < 0x1000)
			{
				ppage = mal_alloc_user();
				memcpy(ppage, (void*)(paddr + of), tocopy);
				memset(ppage+tocopy, 0, 0x1000-tocopy);
			}
			/* else map the page 1/1 */
		}
		else
		{
			ppage = mal_alloc_user();
		}
		mal_prepare_map(part, vaddr);
		/* FIXME: handle permission flags */
		DEBUG(TRACE, "map in part: %08x -> va %08x\n", ppage, vaddr);
		mal_map_in_part(part, ppage, vaddr, 1);
	}
}

/* mal_load_elf: Load an elf, segments must be page aligned
 * returns entry point address */
static void* mal_load_elf(unsigned *part, void*start, void *end)
{
	const unsigned char ELFTAG[16] = {0x7f, 'E', 'L', 'F', 1, 1, 1};
	unsigned len = end - start;
	unsigned i, seg_start, seg_end;
	Elf32_Phdr *phdr;
	Elf32_Ehdr *ehdr = (Elf32_Ehdr*)start;

	DEBUG(TRACE, "LoadElf: ehdr=%p, end=%p, size=%d\n", ehdr,end, len);
	if(end<=(void*)ehdr||len<sizeof(*ehdr) || memcmp(ehdr->e_ident, ELFTAG, sizeof(ELFTAG)))
	{
		DEBUG(ERROR, "Invalid elf\n");
		return NULL;
	}

	phdr = (Elf32_Phdr*)((void*)ehdr+ehdr->e_phoff);
	for (i=0; i<ehdr->e_phnum; i++, phdr++)
	{
		/* Check if its a load segment */
		if (phdr->p_type != 1)
		{
			continue;
		}
		if ((void*)phdr >= end || (unsigned)(end-(void*)phdr) < sizeof(Elf32_Phdr))
		{
			DEBUG(ERROR, "Invalid phdr\n");
			return NULL;
		}
		/* Check valid segment */
		seg_start = phdr->p_offset + (uint32_t)ehdr;
		seg_end = seg_start + phdr->p_filesz;
		DEBUG(TRACE, "Loading phdr %d, off=%04x: type=%08x, addr=%08x, filesize=%04x, memsize=%04x, pos=%p-%p\n", i
				, phdr->p_offset, phdr->p_type, phdr->p_vaddr, phdr->p_filesz, phdr->p_memsz, seg_start, seg_end);

		/* Sanity check the segment */
		if ( phdr->p_memsz < phdr->p_filesz
			|| phdr->p_vaddr & 0xfff
			|| (phdr->p_filesz && (
				seg_start < (uint32_t)ehdr	/* segment fits in the elf */
				||	seg_end > (uint32_t)end
				||	seg_end < seg_start			/* no overflow  */
			))
		   ){
			DEBUG(ERROR, "Invalid segment\n");
			return NULL;
		}
		mal_load_seg(part, phdr, seg_start);
	}
	return (void*)ehdr->e_entry;
}

/* mal_init_root_part: Map the root partition code, give it all user memory.
 * Also prepare the stack and the vidt. */
void mal_init_root_part(unsigned int *part)
{
	unsigned *vidt;
	void *addr, *stack, *ustart;
	void *entry_point;
	pip_fpinfo *fpinfo;
	user_ctx_t *init_ctx;
	extern void *user_alloc_pos;

	/* Prepare & map special purpose pages.
	 * Those won't be mapped 1/1 */
	stack = mal_alloc_user();
	vidt = (unsigned*)mal_alloc_user();
	fpinfo = mal_alloc_user();

	mal_prepare_map(part, (void*)STACK_VADDR);
	mal_prepare_map(part, (void*)VIDT_VADDR);
	mal_prepare_map(part, (void*)FPINFO_VADDR);

	mal_map_in_part(part, stack,  (void*)STACK_VADDR, 1);
	mal_map_in_part(part, vidt,	  (void*)VIDT_VADDR, 1);
	mal_map_in_part(part, fpinfo, (void*)FPINFO_VADDR, 1);

	/* Map root partition (not 1/1) */
	entry_point = mal_load_elf(part, root_part_start, root_part_end);
	if(!entry_point)
		PANIC("Root partition load failed!\n");

	/* We will now map all user memory left in root partition
	 * To make it 1/1 we need to prepare all mappings before actually mapping them */
	for (addr = user_alloc_pos; addr<(void*)user_mem_end; addr += 0x1000)
	{
		mal_prepare_map(part, addr);
	}
	/* Now all the rest of user allocator memory can be mapped 1/1
	 * save the low boundary of user memory & invalidate the now useless
	 * user allocator */
	ustart = user_alloc_pos;
	user_alloc_pos = user_mem_end;

	DEBUG(INFO, "user mem starts at %p\n", ustart);

	/* those mappings are garanteed to be 1/1 */
	for (addr = ustart; addr<(void*)user_mem_end; addr += 0x1000)
	{
		/* user, rw, 1/1 executable, cacheable, non-global */
		mal_map_in_part(part, addr, addr, 1);
	}

	/* fill fpinfo with start of memory info */
	fpinfo->membegin = (unsigned)ustart;
	fpinfo->memend = (unsigned)user_mem_end;

	/* Create first context on the stack */
	init_ctx = (user_ctx_t*)(stack + 0x1000 - sizeof(*init_ctx));
	init_ctx->reg[CTX_SP] = (unsigned)STACK_VADDR + 0x1000 - sizeof(*init_ctx);
	init_ctx->reg[CTX_PC] = (unsigned)entry_point;
	init_ctx->reg[CTX_R0] = (unsigned)FPINFO_VADDR;
	init_ctx->pipflags    = 0; // VCLI
	init_ctx->valid       = 1;

	/* Prepare vidt with first context address */
	vidt[0]  = init_ctx->reg[CTX_SP];
	vidt[32] = vidt[0];

	DEBUG(TRACE, "Filled vidt with &ctx=%p, pc=%08x\n", vidt[0], init_ctx->reg[CTX_PC]);

	/* Invalidate user page allocator (FIXME: debug purpose only) */
	user_alloc_pos = user_mem_end;
}


void mal_init(void)
{
	unsigned *part;

	/* Initialize root partition */
	part = mal_create_root_part();

	/* Map the kernel address space in it */
	mal_map_kernel(part);

	/* Prepare the root partition and give it all user memory */
	mal_init_root_part(part);

	updateRootPartition((unsigned)part);
}
