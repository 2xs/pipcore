/*******************************************************************************/
/*  © Université Lille 1, The Pip Development Team (2015-2017)                 */
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

/**
 * \file mmu.c
 * \brief MMU early-boot configuration
 */ 

#include "mmu.h"
#include "multiboot.h"
#include <stdint.h>
#include "debug.h"
#include "mal.h"
#include "structures.h"
#include "fpinfo.h"
#include "git.h"
#include "hdef.h"
#include "mp.h"
#include <libc.h>

page_directory_t *kernelDirectories[16]; //!< The kernel's page directories, up to 16 cores supported

uint32_t maxPages = 0; //!< The maximal amount of pages available
uint32_t allocatedPages = 0; //!< The current allocated amount of pages
uint32_t ramEnd = 0; //!< End of memory
uint32_t pageCount = 0;
uint32_t mmuEnabled = 0;
uint32_t perCoreMemoryAmount = 0;

// Defined in libc.c
extern uint32_t placement_address; //!< Placement address, this should be unused.


/*!	\fn void mapPageC(uintptr_t pd, uintptr_t p, uintptr_t v)
	\brief add a mapping to a physical page p into a given page directory pd and a virtual address v.
	\param pd a page directory
	\param v a virtual address
	\param p a physical page
	\post p is mapped in pd at v
 */
void mapPageC(uintptr_t pd, uintptr_t p, uintptr_t v, uint8_t user)
{
	/*
	 * First of all : get Page Directory Entry.
	 */
	uintptr_t pdIdx = (v & 0xFFC00000) >> 22;
	uintptr_t ptEntry = (v >> 12) & 0x000003FF;
	page_table_t *pt;
	pt = (page_table_t*)(((page_directory_t*)pd)->tablesPhysical[pdIdx]);
	
	/*
	 * Let's just get the Page Table address, shall we ?
	 */
	pt = (page_table_t*)((uintptr_t)pt & 0xFFFFF000);
	
	/*
	 * Check if we have an existing Page Table here.
	 * If not, create it.
	 */
	if(!pt)
	{
		/* pt = *((uintptr_t*)list);
		 ((page_directory_t*)pd)->tablesPhysical[pd_idx] = (uintptr_t)pt | 0x7; // Page Table is present, read & write, user-mode.  */
		return;
	}
	
	/*
	 * Now we should have a Page Table. Find the corresponding Page Table Entry.
	 */
	page_table_entry_t pte = pt->pages[ptEntry];
	
	
	/*
	 * Configure it, and we're done.
	 */
	pte.accessed = 0;
	pte.dirty = 0;
	pte.frame = (uintptr_t)p >> 12;
	pte.present = 1;
	pte.rw = 1; // (writeable)?1:0;
	pte.user = user; // (kernel)?0:1;

	pt->pages[ptEntry] = pte;
}


/*!
 * \fn void prepareC(uintptr_t pd, uintptr_t v, uintptr_t* page_list)
 * \brief Prepares a Page Directory to receive a mapping by inserting the according Page Table.
 *
 * \param pd a page directory
 * \param v a virtual address
 * \param page_list
 */
void prepareC(uintptr_t pd, uintptr_t v, uintptr_t* pageList)
{
	uintptr_t pdIdx = (v & 0xFFC00000) >> 22;
	page_table_t *pt;
	pt = (page_table_t*)(((page_directory_t*)pd)->tablesPhysical[pdIdx]);
	
	pt = (page_table_t*)((uintptr_t)pt & 0xFFFFF000);
	
	if(!pt)
	{
		pt = (page_table_t*)(*((uintptr_t*)pageList));
		((page_directory_t*)pd)->tablesPhysical[pdIdx] = (uintptr_t)pt | 0x7;
		
		/* Now update mappings into the given CR3 */
		mapPageC(pd, (uintptr_t)pt, (uintptr_t)pt, 0);
	}
	return;
}

/*!	\fn uintptr_t pageCountMapPageC(uintptr_t pd, uintptr_t vaddr)
	\brief tests if there is a page table in pd at vaddr
	\param pd a page directory
	\param uintptr_t vaddr
	\return 1 if there is no page table at position pd_idx, 0 else
 */
uint32_t pageCountMapPageC(uintptr_t pd, uintptr_t vaddr)
{
	uintptr_t pdIdx = (vaddr & 0xFFC00000) >> 22;
	page_table_t *pt = (page_table_t*)(((page_directory_t*)pd)->tablesPhysical[pdIdx]);
	pt = (page_table_t*)((uintptr_t)pt & 0xFFFFF000);
	
	if(!pt)
		return 1;
	else
		return 0;
}

/**
 * \fn void mapPageWrapper(page_directory_t* dir, uint32_t paddr, uint32_t vaddr)
 * \brief Wraps the MAL calls into a single function to map a vaddr into a given page directory
 * \param dir The target page directory
 * \param paddr The source physical address
 * \param vaddr The target virtual address
 */
void mapPageWrapper(page_directory_t* dir, uint32_t paddr, uint32_t vaddr, uint8_t user)
{
    uint32_t pdAddr = (uint32_t)dir;
    uint32_t pc = pageCountMapPageC(pdAddr, vaddr);
    uint32_t list[1];
    if(pc == 1) {
	// Allocate entry for prepare, and shadowed pages
        list[0] = (uint32_t)allocPage();
    }
    
    prepareC(pdAddr, vaddr, list);
    mapPageC(pdAddr, paddr, vaddr, user);
}

/**
 * \fn void initFreePageList(multiboot_memory_map_t* mmap)
 * \brief Initializes the free page list, given a multiboot-compliant memory map
 * \param mmap The memory map given by Multiboot
 */
void initFreePageList(uintptr_t base, uintptr_t length)
{
    extern uint32_t end;
    extern uint32_t furthestPartitionCode; /* Last address for Multiboot module placement */
    uint32_t sizeToMap;
    uint32_t mappingBegin;

	DEBUG(TRACE, "Adding memory region %x length %x\n", base, length);
	extern uintptr_t __end;
	if(base >= 0x100000)
	{
        DEBUG(CRITICAL, "Last Multiboot module at %x\n", furthestPartitionCode);
		uint32_t i = 0;
		/* Add each page of free area */
		for(i = base; i < base + length; i+=0x1000)
		{
			/* Ignore kernel area */
			if((i > /* (uint32_t)&__end + 0x100000*/ furthestPartitionCode) && (i > (uint32_t)&__end)) { /* Add 0x100000 at the end of the kernel to preserve GRUB modules - TODO : clean this */
				*(uint32_t*)i = (uint32_t)firstFreePage; /* Add current page as head of list */
				firstFreePage = (uint32_t*)i;
				pageCount++;
			}
		}

		DEBUG(TRACE, "added memory region to page allocator, %d pages, first page %x, last page at %x", pageCount, base, i);
		maxPages = pageCount;
		ramEnd = i;
	} else {
		DEBUG(TRACE, "Not adding low-memory area\n");
	}
}

/**
 * \fn uint32_t* allocPage()
 * \brief Unsafe page allocator. Allocated a page.
 * \return Virtual address to a free page.
 */
uint32_t* allocPage()
{

    uint32_t* res = firstFreePage;
    firstFreePage = (uint32_t*)(*res);

    allocatedPages++;

    return res;
}

/**
 * \fn void freePage(uint32_t *page)
 * \brief Frees a page in a really unsafe way.
 * \param page The page to free.
 */
void freePage(uint32_t *page)
{
    *page = (uint32_t)firstFreePage;
    firstFreePage = (uint32_t*)page;

    allocatedPages--;
}

/**
 * \fn void dumpMmap(uint32_t *mmap_ptr, uint32_t len)
 * \brief Despite its unexplicit name, this function initializes the physical memory, preparing the page allocator as well.
 * \param mmap_ptr Pointer to a multiboot-compliant memory map
 * \param len Length of the memory map structure
 */
void dumpMmap(uint32_t *mmap_ptr, uint32_t len)
{
    // Gets size of structure
    multiboot_memory_map_t* mmap = (multiboot_memory_map_t*)mmap_ptr;
    uint32_t num = 1;

    DEBUG(TRACE, "Parsing Multiboot-provided memory map at %x\n", mmap_ptr);
    extern uint32_t code;

    // Parse each entry
    while((uint32_t*)mmap < (uint32_t*)((uint32_t)mmap_ptr + len) && mmap->size > 0)
    {
		DEBUG(CRITICAL, "region %d, addr %x, length %x\n", num, mmap->base_addr_low, mmap->length_low);
        switch(mmap->type){
        case MULTIBOOT_MEMORY_ACPI_RECLAIMABLE:
            DEBUG(TRACE, "\tACPI_RECLAIMABLE\n");
            break;
        case MULTIBOOT_MEMORY_AVAILABLE:
            DEBUG(TRACE, "\tAVAILABLE\n");
			initFreePageList(mmap->base_addr_low, mmap->length_low);
            break;
        case MULTIBOOT_MEMORY_BADRAM:
            DEBUG(TRACE, "\tBADRAM\n");
            break;
        case MULTIBOOT_MEMORY_NVS:
            DEBUG(TRACE, "\tNVS\n");
            break;
        case MULTIBOOT_MEMORY_RESERVED:
            DEBUG(TRACE, "\tRESERVED\n");
            break;
        default:
            DEBUG(TRACE, "\tUNKNOWN\n");
            break;
        }

        kprintf("\n");
        num++;
        mmap = (multiboot_memory_map_t*) ( (unsigned int)mmap + mmap->size + sizeof(unsigned int) );
    }
}

/**
 * \fn void mark_kernel_global()
 * \brief Marks the whole kernel area as global, preventing TLB invalidations
 */
void mark_kernel_global()
{
	#define GLOBAL_BIT (1 << 8)
	uint32_t pd_idx = kernelIndex();
	uint32_t kern_pt = readTableVirtual((uint32_t)kernelDirectories[coreId()], pd_idx);
	uint32_t i = 0;
	/* Mark each entry of kernel PT as global */
	for(i = 0; i < 1024; i++)
	{
		uint32_t kern_pte = readTableVirtual((uint32_t)kern_pt, i);
		if(kern_pte) {
			writeTableVirtual((uint32_t)kern_pt, i, kern_pte | GLOBAL_BIT);
		}
	}
	
	/* Mark kernel PT as global */
	writeTableVirtual((uint32_t)kernelDirectories[coreId()], pd_idx, kern_pt | GLOBAL_BIT);
	
	return;
}

/**
 * \fn void initMmu()
 * \brief Initializes the MMU, creating the kernel's page directory and switching to it.
 */
uint32_t initMmu()
{
    uint32_t multEnd = 0x0;
    DEBUG(CRITICAL, "Initializing MMU for core %d.\n", coreId());
    /* Create the Kernel Page Directory */
    kernelDirectories[coreId()] = (page_directory_t*)allocPage(); // kmalloc(sizeof(page_directory_t));
	DEBUG(TRACE, "Kernel directory is at %x\n", kernelDirectories[coreId()]);
    memset(kernelDirectories[coreId()], 0, sizeof(page_directory_t));

    /* Map the kernel space */
    uint32_t curAddr = 0;
    extern uint32_t end;

    /* Map kernel, stack up to root partition */
    while(curAddr <= 0x700000)
    {
        mapPageWrapper(kernelDirectories[coreId()], curAddr, curAddr, 0);
        curAddr += PAGE_SIZE;
    }
	
    extern pip_mboot_partition_t bootparts[4]; /* Per-core multiplexers */
	
    /* Map root partition in userland */
	curAddr = 0x700000;
	uint32_t tmpAddr;
    for(tmpAddr = bootparts[coreId()].start; tmpAddr < bootparts[coreId()].end; tmpAddr += PAGE_SIZE)
    {
        uint32_t decal = tmpAddr - bootparts[coreId()].start;
		mapPageWrapper(kernelDirectories[coreId()], tmpAddr, 0x700000 + decal, 1);
	}
    curAddr = 0x700000+(tmpAddr - bootparts[coreId()].start);
    bootparts[coreId()].vend = curAddr;
    DEBUG(CRITICAL, "Mapped root partition for core %d from %x to %x.\n", coreId(), 0x700000, curAddr);
    multEnd = (uint32_t)&end;

	/* Map each platform-specific device */
	uint32_t hid;
	
    /* Parse each specific hardware entry */
	for(hid = 0; hid < HSPEC_COUNT; hid++)
	{
		DEBUG(CRITICAL, "x86: adding mapping for %s\n", pshw[hid].name);
		uintptr_t base = pshw[hid].paddr_base;
		uintptr_t limit = pshw[hid].limit;
		uintptr_t vbase = pshw[hid].vaddr_base;
		
		uintptr_t cur_off;
		for(cur_off = 0x0; cur_off < limit; cur_off += 0x1000)
		{
			mapPageWrapper(kernelDirectories[coreId()], base + cur_off, vbase + cur_off, 1);
		}
	}
	
	mark_kernel_global();
	
	/* First, pseudo-prepare kernel directory, removing potential page tables from free page list */
	uint32_t j = 0;
	for(j = 0; j < 0xFFFFF000; j+=0x1000)
	{
		uint32_t pc = pageCountMapPageC((uintptr_t)kernelDirectories[coreId()], j);
		uint32_t list[1];
		if(pc == 1) {
			list[0] = (uint32_t)allocPage();
			memset((void*)list[0], 0x0, PAGE_SIZE);
			prepareC((uintptr_t)kernelDirectories[coreId()], j, list);
		}
	}
	
	/* Map a linear memory space using page allocator */
	curAddr = (uint32_t)&end;
	uint32_t pg;
	
    /* Map first partition info as user-accessible */
    extern pip_fpinfo* fpinfo[16];
	
	fpinfo[coreId()] = (pip_fpinfo*)allocPage();
	DEBUG(TRACE, "Allocated FpInfo to %x\n", fpinfo[coreId()]);
    uintptr_t fpInfoBegin = (uintptr_t)fpinfo[coreId()];
	
	mapPageWrapper(kernelDirectories[coreId()], (uint32_t)fpInfoBegin, (uint32_t)fpInfoBegin, 1);
	
    /* Map the first free page into our kernel's virtual address space */
    mapPageWrapper(kernelDirectories[coreId()], (uint32_t)firstFreePage, (uint32_t)firstFreePage, 0);
	
	/* TODO : check the correctness of this. The initial state of the system HAS to be correct, this is just a hackfix right now */
	
    /* Now we have to build a proper environment for main partition */
	uint32_t* partitionDescriptor = allocPage(); // Partition descriptor
	uint32_t* sh1 = allocPage();
    uint32_t* sh2 = allocPage();
    uint32_t* sh3 = allocPage();
    *sh3 = 2;
	
    for(uint32_t i = 1; i < 1024; i++)
    {
        uint32_t* ptsh1 = allocPage();
		memset(ptsh1, 0x0, PAGE_SIZE);
			
        uint32_t* ptsh2 = allocPage();
		memset(ptsh2, 0x0, PAGE_SIZE);
		
        sh1[i] = (uint32_t)ptsh1;
        sh2[i] = (uint32_t)ptsh2;
    }
	
	DEBUG(TRACE, "Page allocation ends at %x, multiplexer descriptor is %x\n", firstFreePage, partitionDescriptor);

    partitionDescriptor[0] = (uint32_t)partitionDescriptor;
    partitionDescriptor[1] = (uint32_t)partitionDescriptor;
    partitionDescriptor[2] = (uint32_t)kernelDirectories[coreId()];
    partitionDescriptor[3] = (uint32_t)kernelDirectories[coreId()];
    partitionDescriptor[4] = (uint32_t)sh1;
    partitionDescriptor[5] = (uint32_t)sh1;
    partitionDescriptor[6] = (uint32_t)sh2;
    partitionDescriptor[7] = (uint32_t)sh2;
    partitionDescriptor[8] = (uint32_t)sh3;
    partitionDescriptor[9] = (uint32_t)sh3;
    partitionDescriptor[10] = 0xFFFFFFFF;
    partitionDescriptor[11] = 0;

	/* Current partition is now our descriptor */
	extern uint32_t current_partition;
	current_partition = (uint32_t)partitionDescriptor;
	updateRootPartition((uintptr_t)partitionDescriptor);

	/* Create fake IDT at 0xFFFFF000 */
	uint32_t* virt_intv = allocPage();
	mapPageWrapper(kernelDirectories[coreId()], (uint32_t)virt_intv, 0xFFFFF000, 1);
    *virt_intv = 0x700000;
    *(virt_intv + 1) = 0xFFFFE000 - sizeof(uint32_t);
	mapPageWrapper(kernelDirectories[coreId()], (uint32_t)0xB8000, 0xFFFFE000, 1);
	
	/* Fill VIDT info */
	extern uint32_t __multiplexer;
	*virt_intv = (uint32_t)(&__multiplexer); // Multiplexer load address at VIDT[0].EIP
	
	DEBUG(TRACE, "Building linear memory space\n");
	
	/* Build a multiplexer stack */
	mapPageWrapper(kernelDirectories[coreId()], (uint32_t)allocPage(), 0xFFFFD000, 1);
	
	/* Map first partition info */
	mapPageWrapper(kernelDirectories[coreId()], (uint32_t)fpinfo[coreId()], 0xFFFFC000, 1);
	
	/* First prepare all pages : pages required for prepare should be deleted from free page list */
	/* At this point, page allocator is empty. */
	DEBUG(TRACE, "Partition environment is ready, membegin=%x, memend=%x\n", fpinfo[coreId()]->membegin, fpinfo[coreId()]->memend);

    mmuEnabled = 1;

    return multEnd;
}

void prepareAllocatorRelease()
{
    if(perCoreMemoryAmount == 0)
        perCoreMemoryAmount = (maxPages - allocatedPages)/(coreCount());
}

void fillMmu(uint32_t begin)
{
    uint32_t pg, curAddr;
    curAddr = begin;
    uint32_t pgAmount = perCoreMemoryAmount;
    uint32_t i;
    DEBUG(CRITICAL, "Giving some memory starting at %x (%d pages, %d total, ~%dMb) for multiplexer core %d.\n", begin, pgAmount, (maxPages - allocatedPages), (pgAmount * 4096) /* bytes */ / 1024 /* kb */ / 1024 /* mb */, coreId());
	for(i=0; i<pgAmount; i++)
    {
        pg = (uint32_t)allocPage();
        mapPageC((uintptr_t)kernelDirectories[coreId()], pg, curAddr, 1);
		curAddr += 0x1000;
	}
    DEBUG(CRITICAL, "Available memory ends at %x.\n", curAddr);
	extern pip_fpinfo* fpinfo[16];
	/* Fix first partition info */
	fpinfo[coreId()]->membegin = begin;
	fpinfo[coreId()]->memend = curAddr;
	fpinfo[coreId()]->magic = FPINFO_MAGIC;
	strcpy(fpinfo[coreId()]->revision, GIT_REVISION);
    DEBUG(CRITICAL, "Done.\n");
}

void coreEnableMmu()
{
    activate((uint32_t)kernelDirectories[coreId()]);
}
