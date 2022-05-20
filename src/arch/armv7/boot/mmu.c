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

#include "coproc.h"
#include "reg.h"
#include "mmu.h"
#include "machine.h"
#include "string.h"
#include "debug.h"

/* ARM Architecture Reference Manual ARMv7-A: Chapter B3
 *
 *  Two descriptors format are available: short & long.
 *  Both can configure permissions on 4KB pages.
 *  Short descriptors can manage 32 bit address space, while long descriptor
 *  can manage 40 bit with Large Physical Address Extension (LPAE).
 *  We will stick to short descriptors for now.
 *
 *  Permissions can be applied on other kinds of memory regions.
 *  This intro only describes 4KB (small pages) management.
 *
 *  In short mode, two levels of translations are used:
 *      - 1: Translation table (TT): 4096 entries of 1Mb     (Aligned on 0x4000)
 *      - 2: Page Table (PT):         256 entries of 4Kb     (Aligned on 0x400)
 *
 *  ARMv7 defines two translations tables base registers: TTBR0 & TTBR1
 *  TTBR0 for low memory accesses, TTBR1 for hig memory
 *  It's meant to reduce context switching time, by using a process specific TT.
 *  The bound can be set in TTBCR.N (0 = use only TTBR0):
 *      0           -> 1<<(32-N)    : TTBR0
 *      1<<(32-N)   -> 4GB          : TTBR1
 *  (In ARMv6 compatible mode, only TTBR0 can be used, N must be to zero.)
 *
 *  When split address space is used, the TT in TTBR0 is truncated  by
 *  a factor of (1<<N).
 *
 *  Permissions: We use AP[2:0] permissions scheme with TEX & AFE disabled.
 *
 *  Translation Lookaside Buffers (TLB):
 *  The TLB maintains a cache of memory translations. Any memory access that
 *  do not cause an fault might be allocated in TLB at any time.
 *  Software must perform TLB maintenance when updating the TT entries (B3.10.1)
 *
 *  The Address Space Identifier provide per process TLB management.
 *  The current ASID is defined in the Context ID Register (CONTEXTIDR[7:0])
 *
 *  Non global mappings get cached in TLB with current ASID tagged in.
 *  On a context switch, TLB entries can be flushed as per the ASID.
 *  The TTBR shall be changed together with the ASID.
 *
 *  *****************************************
 *  *    Adapting pip design to ARM MMU     *
 *  *****************************************
 *
 *      *************************
 *      *  Configuration pages  *
 *      *************************
 *  The pip services relies on a x86 specific assumptions:
 *  - all levels of translation use the same address width,
 *  - and all MMU configuration pages occupy exactly one physical memory page,
 *
 *  The first issue requires adding an argument to getTableSize to provide
 *  per level table size.
 *
 *  The second issue is more complex. A full l1 translation table takes 16KB.
 *  createPartition should somehow check that the given child pd point to
 *  four pages in the current child va space, and are indeed mapped to
 *  four consecutive physical pages, starting on a 16KB boundary.
 *
 *  One quick & dirty way to solve alignment problem is to rely on the VA
 *  selection mechanism to truncate the TTBR0 translation table to 4KB.
 *  With this solution, only 1024 entries of 1MB can be handled by a child,
 *  effectingly limiting the addressable memory space to 1GB.
 *
 *  The TTBR1 register will be kept pointing on an empty L1 TT, causing any
 *  memory access > 0x40000000 to trigger a fault.
 *
 *  Remains the variable table wize problem, but it should not cause much
 *  trouble in the proof as long as a configuration page fits in a page.
 *  We can easily prove that the getIndexOfAddr returns a correctly bounded
 *  value.
 *
 *  Another solution to both problems could be make getTableSize return 256.
 *  This way both problems would be solved quite simply. The maximum
 *  addressable space would though be 256MB only.
 *  Both solutions share another side-effect: we must provide pip with
 *  4KB aligned pages, even if the L2 PT are only 1KB. While it is not a big
 *  issue for userland, we'll waste quite a bit of memory there.
 *
 *      *************************
 *      *   Peripheral memory   *
 *      *************************
 *  One other issue is the memory-mapped peripherals. Simply handling it to
 *  the multiplexer seems an appealing solution, that provides a natural
 *  way to multiplex hardware.
 *
 *  It can not be solved so easily, because a partition would be able to pass
 *  a peripheral page as a mmu configuration page, and summon dragons.
 *  Another issue for peripheral memory is that it requires specific cache
 *  configuration in the page table.
 *
 *  On way to handle the problem requires chaning the model/services/proof to
 *  keep track of peripheral memory pages, and forbidding its usage as configuration
 *  pages.
 *
 *  For now, the problem stays open, and I will madly hardcode cache options,
 *  and dirty-check the peripheral memory issue.
 *
 *  Another issue we will need to solve is that peripheral memory access
 *  must remain accessible to kernel if we want to allow basic functionnalities
 *  as uart debugging. We will fix it by mapping the peripheral memory in
 *  TTBR1 register, only accessible to kernel.
 *
 */

/* for TTBR1 upper memory (devices) */
static unsigned  __attribute__((aligned(0x4000))) static_tt1[MMU_TTBR1_ENT_COUNT];
/* Our TTBR0 L1 translation table */
//static unsigned __attribute__((aligned(0x1000))) static_tt0[0x400];

static struct mmu_caps_s {
	unsigned version;
	bool_t pxn;
	bool_t ltf;
} mmu_caps;

/* Static allocator for up to 256 page tables */
#if 1
#define STATIC_PT_COUNT 1
static unsigned  __attribute__((aligned(0x400))) static_pt[STATIC_PT_COUNT][MMU_L2_ENT_COUNT];

static unsigned static_pt_index = 0;

static unsigned *static_pt_alloc(void)
{
	if (static_pt_index >= STATIC_PT_COUNT)
		PANIC("No PT memory\n");

	return (unsigned*)&static_pt[static_pt_index++];
}
#endif

static void mmu_init_caps(void)
{
	reg_mmfr0_t mmfr0;

	memset(&mmu_caps, 0, sizeof(mmu_caps));
	READ_CP(mmfr0, ID_MMFR0);
	switch (mmfr0.vmsa_support)
	{
		case 2:
			mmu_caps.version = 6;
			break;
		case 3: case 4: case 5:
			mmu_caps.version = 7;
			if (mmfr0.vmsa_support >= 4)
				mmu_caps.pxn = TRUE;
			if (mmfr0.vmsa_support == 5)
				mmu_caps.ltf = TRUE;
			break;
		default:
			break;
	}
}

/*	B4.1.154 TTBR0, Translation Table Base Register 0
 *	Build translation table register */
unsigned mmu_make_ttbr (
		void * base,
		mmu_rgn_t irgn,			/* Cache inner attributes */
		mmu_rgn_t rgn,			/* Cache outer attributes */
		bool_t shareable,
		bool_t not_outer_shareable
		){
	unsigned ttbr;

	ttbr = (unsigned)base;	/* assuming the base is correctly aligned */
	ttbr |= (irgn>>1) | ((irgn&1)<<6);
	ttbr |= (rgn<<3) | (shareable<<1) | (not_outer_shareable<<5);

	return ttbr;
}

/*	B4.1.153 TTBCR, Translation Table Base Control Register, VMSA
 *	Hardcoded usage of short-format (EAE=0)	*/
static void mmu_set_ttbcr ( unsigned N)
{
	reg_ttbcr_t ttbcr = {0};

	ttbcr.N = N;
	WRITE_CP(ttbcr, ID_TTBCR);
}

/* Make a l2 (page table) short-descriptor entry
 * Assume TEX and AFE are disabled */
mmu_sd_sp_t mmu_make_small_page(
		void	*spbaddr		/* Full address of aligned(12) small page */
		, bool_t	user		/* User accessible */
		, bool_t	ro			/* Read only */
		, bool_t	xn			/* eXecute never */
		, bool_t	device
		, bool_t	global
		){
	mmu_sd_sp_t entry;
	unsigned mem_attr;

	/* B3.8.2 (without TEX remap)
	   If device is set, map page as Shareable Device.
	   Else, map as Outer and Inner Write-Back, Write-Allocate
	 */
	mem_attr = device ? (1<<2) : (3<<2)|(1<<6);

	entry.aslong = mem_attr | (
			xn
			|	(1<<1)					/* Page table */
			|	((!global)<<11)			/* nG */
			/* B3.7.1 Access permissions, assuming AFE disabled */
			|	(1<<4)					/* AP0, set to 1 */
			|	(user<<5)				/* AP1, accessible to PL1 & PL0 */
			|	(ro<<9)					/* AP2, read only */
			|	((unsigned)spbaddr & ~0xfff));	/* Physical page 4Kb */

	return entry;
}

mmu_sd_pt_t mmu_make_page_table(
		void	*ptbaddr		/* Full address of aligned(12) small page */
		){
	mmu_sd_pt_t entry;

	/*	Page table entry, domain 0 */
	entry.aslong =  1 | ((unsigned)ptbaddr &~ 0x3ff);

	return entry;
}

void mmu_debug(unsigned *tt)
{
	unsigned i, j, l1, *pt, va, pa;
	mmu_sd_sp_t l2;

	printf("Debugging Translation Table %p:\n", tt);

	for(i=0;i<MMU_TTBR0_ENT_COUNT;i++)
	{
		l1 = tt[i];
		if ((l1 & 3)==0)
			continue;
		if ((l1 & 3)!=1){
			printf("[%4d]: Not a Page Table %08x\n", i, l1);
			continue;
		}
		pt = (unsigned*)((unsigned)l1 & ~0x3ff);
		printf("[%4d]: Page Table -> %p\n", i, pt);
		for (j=0; j<MMU_L2_ENT_COUNT;j++)
		{
			l2.aslong = pt[j];
			if ((l2.aslong & 3)==0)
				continue;
			if ((l2.aslong & 2) != 2){
				printf("\t[%4d] Not a Small Page\n", j);
				continue;
			}
			va = (i<<20) | (j<<12);
			pa = l2.aslong & ~0xfff;
			printf("\t[%4d] Small Page va %p -> pa %p (user:%d)\n", j, va, pa, l2.AP1);
		}
	}
}

/* This should be called with mmu disabled or mapped 1/1
 * because we manipulate physical addresses. */
mmu_sd_sp_t mmu_virt_to_sp(unsigned pd, unsigned va_)
{
	unsigned idx1, idx2, va;
	mmu_sd_pt_t pte;
	mmu_sd_sp_t *pt, sp;

	va		= va_ & ~0xfff;

	idx1 = ((unsigned)va >> 20) & 0x3ff;
	idx2 = ((unsigned)va >> 12) & 0xff;

	/* assumes pd is correctly aligned */
	pte = ((mmu_sd_pt_t*)pd)[idx1];
	if (!(pte.aslong & 3))
		return (mmu_sd_sp_t)(unsigned)-1;

	/* Here we accept original hardware alignment */
	pt = (mmu_sd_sp_t*)(pte.aslong & ~0x3ff);
	sp = pt[idx2];

	/* Check its indeed a small page */
	if (!sp.one)
	{
		return (mmu_sd_sp_t)(unsigned)-1;
	}
	return sp;
}

/* This should be called with mmu disabled or mapped 1/1
 * because we manipulate physical addresses. */
unsigned mmu_virt_to_phys(unsigned pd, unsigned va_)
{
	unsigned offset, va, phys;
	mmu_sd_sp_t sp;

	offset	= va_ &  0xfff;
	va		= va_ & ~0xfff;

	sp = mmu_virt_to_sp(pd, va);
	if ((int)sp.aslong == -1)
	{
		return -1;
	}
	phys = (sp.aslong &~ 0xfff) | offset;
	return phys;
}

/* Map a small page (1Kb) in MMU with given addresses & attributes */
void mmu_map_small_page(
		unsigned int *tt,	/* Translation table addr*/
		void *pa, void *va, /* Physical & virtual addresses */
		bool_t user,		/* PL0 & PL1 accessible */
		bool_t ro,			/* Read only */
		bool_t xn,			/* eXecute never */
		bool_t device,		/* Set memory as shareable device */
		bool_t global		/* Mark memory as global  */
		){
	unsigned idx1, idx2, l1, l2;
	unsigned *pt;

	idx1 = ((unsigned)va >> 20) & 0xfff;
	idx2 = ((unsigned)va >> 12) & 0xff;

	/* Level 1 */
	l1 = tt[idx1];
	if (l1)
	{
		pt = (unsigned*)(l1 & ~0x3ff);
	}
	else
	{
		/* Allocate a new page table */
		pt = static_pt_alloc();
		memset(pt, 0, MMU_L2_ENT_COUNT*4);

		/* Create page table and fill l1 translation table */
		l1 = mmu_make_page_table(pt).aslong;
		tt[idx1] = l1;
	}
	/* Level 2 */
	l2 = mmu_make_small_page(pa, user, ro, xn, device, global).aslong;
	pt[idx2] = l2;
}

void mmu_map_anysection(
		unsigned int *tt,	/* Translation table addr*/
		void *pa, void *va, /* Virtual & Physical addresses */
		bool_t user,		/* PL0 & PL1 accessible */
		bool_t ro,			/* Read only */
		bool_t xn,			/* eXecute never */
		bool_t device,		/* Set memory as shareable device */
		bool_t global,		/* Mark memory as global  */
		int super			/* super section ? */
		){
	unsigned idx1, mem_attr, l1, i;

	mem_attr = device ? (1<<2) : (3<<2)|(1<<6);

	idx1 = ((unsigned)va >> 20) & 0xfff;

	/* Make a section or a supersection (most attributes overlaps) */
	l1 = mem_attr | (
			(xn<<4)
			|	(1<<1)					/* section */
			|	((!global)<<17)			/* nG */
			/* B3.7.1 Access permissions, assuming AFE disabled */
			|	(1<<10)					/* AP0, set to 1 */
			|	(user<<11)				/* AP1, accessible to PL1 & PL0 */
			|	(ro<<16)				/* AP2, read only */
			);

	if (super)
	{
		l1 |= (1<<18);		/* Super section 16MB */
		l1 |= ((unsigned)pa & ~0xffffff);
		for(i=0;i<16;i++)
			tt[idx1+i] = l1;
	}
	else
	{
		l1 |= ((unsigned)pa & ~0xfffff);	/* Section 1MB */
		/* Level 1 */
		tt[idx1] = l1;
	}
}

/* MMU initialisation function */
void mmu_init(void)
{
	unsigned reg;

	mmu_init_caps();

	/* Check if VMSA is supported */
	if (mmu_caps.version < 7)
	{
		PANIC("VMSA support unknown, bailing\n");
	}

	/* Init a translation table for addresses starting from 0x40000000.
	 * We will mirror peripheral memory there, accessible to kernel only. */
	memset(static_tt1, 0, sizeof(static_tt1));

	/* FIXME: this is very raspi2 specific */
	/* Map 16MB of control peripherals 1/1 at 40000000 */
	mmu_map_supersection(static_tt1, (void*)PERIPH_CONTROL, (void*)PERIPH_CONTROL, 0, 0, 1, 1, 1);
	/* Map 16MB of peripheral relocated from 3F000000 to 41000000 to fit in ttbr1 */
	mmu_map_supersection(static_tt1, (void*)PERIPH_BASE, (void*)PERIPH_VBASE, 0, 0, 1, 1, 1);

	/* Configure only TTBR1 to allow access peripheral memory from kernelland */
	WRITE_CP(mmu_make_ttbr(
				&static_tt1,			/* Static kernel Translation Table */
				RGN_CACHE_WBACK_WALLOC, /* Enable inner cache write-back write-alloc*/
				RGN_CACHE_WBACK_WALLOC, /* Enable outer cache write-back write-alloc*/
				0, 1					/* Non shareable */
			      ), ID_TTBR1);

	/*	B4.1.153 / B3.5.4 Configure Translation Table:
	 *	N = 2: TTBR0 is truncated to 1024 entries, allowing control of 1GB
	 *	of lower memory. TTBR1 is used for addresses above 0x40000000
	 *	EAE = 0: No extended address space
	 */
	mmu_set_ttbcr(2);

	/* Disable TEX remap & Access flag */
	READ_CP(reg, ID_SCTLR);
	reg &= ~(SCTLR_TRE | SCTLR_AFE);
	WRITE_CP(reg, ID_SCTLR);

	/* Configure Domain Access Control Register:
	 *	Domain 0: Client (check permission bits in translation table)
	 *	Other domains: No access */
	WRITE_CP(1, ID_DACR);

	/* Always use ASID 0. We will rely on the global bit to flush tlb memory */
	WRITE_CP(0, ID_CONTEXTIDR);
}
