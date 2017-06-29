/*******************************************************************************/
/*  © Université Lille 1, The Pip Development Team (2015-2016)                 */
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
#include <libc.h>

page_directory_t *kernelDirectory=0; //!< The kernel's page directory

uint32_t maxPages = 0; //!< The maximal amount of pages available
uint32_t allocatedPages = 0; //!< The current allocated amount of pages
uint32_t ramEnd = 0; //!< End of memory

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

    pte.present = 1;
    pte.rw = 1;
    pte.user = user;
    pte.write = 1;
    pte.cache = 1;
    pte.dirty = 0;
    pte.unused = 0;
    pte.avail = 0;
    pte.frame = (uintptr_t)p / PAGE_SIZE;

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

        //DEBUG(TRACE,"Now update mappings into with pd = %x, the given CR3\n\t\r",pd);
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

static uint8_t mapped = 0;
/**
 * \fn void initFreePageList(multiboot_memory_map_t* mmap)
 * \brief Initializes the free page list, given a multiboot-compliant memory map
 * \param mmap The memory map given by Multiboot
 */
void initFreePageList(multiboot_memory_map_t* mmap)
{
    if(mapped)
        return;

    extern uint32_t end;
    uint32_t sizeToMap;
    uint32_t mappingBegin;
    uint32_t pageCount = 0;
    // Kernel is located in our area ? Make sure we don't overwrite our Haskell heap though
    if(&end > (uint32_t*)(mmap->base_addr_low) && &end < (uint32_t*)(mmap->base_addr_low + mmap->length_low)){
        mappingBegin = (unsigned int)(/* &end RAM_END */ 0x1000000 + 0x1000) & 0xFFFFF000;
        sizeToMap = mmap->length_low - (mappingBegin - mmap->base_addr_low);
    } else {
        mappingBegin = (mmap->base_addr_low + 0x1000) & 0xFFFFF000;
        sizeToMap = mmap->length_low - (mappingBegin - mmap->base_addr_low);
    }

    DEBUG(TRACE, "mapping begins at %x and the size is %d \n", mappingBegin,sizeToMap);

    uint32_t cur = mappingBegin;

    // Our first free page shall be this.
    firstFreePage = (uint32_t*)mappingBegin;

    while(cur < mappingBegin + sizeToMap)
    {
        // Set page contents as next free page address
        *(unsigned int*)cur = cur + PAGE_SIZE;

        // Jump to next page
        cur += PAGE_SIZE;
        pageCount++;
    }

    DEBUG(INFO, "paging initialization complete, %d pages, last page at %x\n", pageCount, cur);
    maxPages = pageCount;
    ramEnd = cur - PAGE_SIZE;
    mapped = 1;
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

    extern uint32_t code;

    // Parse each entry
    while((uint32_t*)mmap < (uint32_t*)((uint32_t)mmap_ptr + len) && mmap->size > 0)
    {

        DEBUG(TRACE, "region %d, addr %x, length %x\n", num, mmap->base_addr_low, mmap->length_low);
        switch(mmap->type){
            case MULTIBOOT_MEMORY_ACPI_RECLAIMABLE:
                DEBUG(TRACE, "\tACPI_RECLAIMABLE\n");
                break;
            case MULTIBOOT_MEMORY_AVAILABLE:
                DEBUG(TRACE, "\tAVAILABLE\n");
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
        uint32_t *x86rambase = (uint32_t*)0x100000;
        if((uint32_t*)(mmap->base_addr_low) >= x86rambase /* &code */ && mmap->type == MULTIBOOT_MEMORY_AVAILABLE) {
            DEBUG(TRACE, "\tUSABLE\n");
            initFreePageList(mmap);
        }
        printf("\n");
        num++;
        mmap = (multiboot_memory_map_t*) ( (unsigned int)mmap + mmap->size + sizeof(mmap->size) );
    }
}

/**
 * \fn void initMmu()
 * \brief Initializes the MMU, creating the kernel's page directory and switching to it.
 */
void initMmu()
{
    /* Create the Kernel Page Directory */
    kernelDirectory = (page_directory_t*)allocPage(); // kmalloc(sizeof(page_directory_t));
    DEBUG(TRACE, "Kernel directory is at %x\n", kernelDirectory);
    memset(kernelDirectory, 0, sizeof(page_directory_t));
    DEBUG(TRACE, "Kernel directory set\n");

    /* Map the kernel space */
    uint32_t curAddr = 0;
    extern uint32_t end;

    /* Map kernel, stack up to root partition */
    while(curAddr <= (uint32_t)(/* &end */ /* RAM_END */0x700000))
    {
        mapPageWrapper(kernelDirectory, curAddr, curAddr, 0);
        curAddr += PAGE_SIZE;
    }

    /* Map root partition in userland as well as VGA device */
    curAddr = 0x700000;
    while(curAddr <= (uint32_t)(/* &end */ /* RAM_END */0xFFFFE000))
    {
        mapPageWrapper(kernelDirectory, curAddr, curAddr, 1);
        curAddr += PAGE_SIZE;
    }

    mapPageWrapper(kernelDirectory, 0xB8000, 0xB8000, 1);
    DEBUG(TRACE, "Kernel directory WRAPPED\n");

    /*
     * We'll also self-test the MMU on boot.
     * First allocate a page.
     * Write some magic inside it.
     * Map it to a random virtual address.
     * Find the magic at that virtual address then.
     */
    uint32_t *testPage = allocPage();
    DEBUG(TRACE, "testPage address is %x\n",*testPage);


    uint32_t *testPageVirt = (uint32_t*)0x0CAFE000;

    DEBUG(TRACE, "MMU self-test\n");
    *testPage = 0xDEADBEEF;
    DEBUG(TRACE, "paddr=%x, vaddr=%x\n", testPage, testPageVirt);


    mapPageWrapper(kernelDirectory, (uint32_t)testPage, (uint32_t)testPageVirt, 0);
    DEBUG(TRACE,"Kernel Directory wrapped\n");
    mapPageWrapper(kernelDirectory, (uint32_t)kernelDirectory, (uint32_t)kernelDirectory, 0);
    DEBUG(TRACE,"Kernel Directory wrapped\n");

    /* Map first partition info as user-accessible */
    extern pip_fpinfo* fpinfo;
    mapPageWrapper(kernelDirectory, (uint32_t)fpinfo, (uint32_t)fpinfo, 1);
    DEBUG(TRACE,"Map first partition info as user-accessible\n");

    // Map the first free page into our kernel's virtual address space
    mapPageWrapper(kernelDirectory, (uint32_t)firstFreePage, (uint32_t)firstFreePage, 0);
    DEBUG(TRACE,"Map the first free page into our kernel's virtual address space\n");

    /* Our Kernel Page Directory is created, write its address into CR3. */
    activate((uint32_t)kernelDirectory);


    DEBUG(TRACE,"Write the address of kernel into CR3\n");
    DEBUG(TRACE, "found value %x, expected 0xDEADBEEF\n", *testPageVirt);
    if(*testPageVirt == 0xDEADBEEF){
        DEBUG(INFO, "Self-test succeeded.\n");
    }

    DEBUG(INFO, "Reversing self-test mapping\n");
    mapPageWrapper(kernelDirectory, (uint32_t)testPageVirt, (uint32_t)testPageVirt, 1);

    DEBUG(TRACE, "Welcome to virtual memory world\n");

    /* TODO : check the correctness of this. The initial state of the system HAS to be correct, this is just a hackfix right now */

    /* Now we have to build a proper environment for main partition */
    uint32_t* partitionDescriptor = allocPage(); // Partition descriptor
    uint32_t* sh1 = allocPage();
    uint32_t* sh2 = allocPage();
    uint32_t* sh3 = allocPage(); // Allocate shadow list
    *sh3 = 2; // TODO: fill sh3 with each indirection table

    for(uint32_t i = 1; i < 1024; i++)
    {
        uint32_t* ptsh1 = allocPage();
        memset(ptsh1, 0x0, PAGE_SIZE);

        uint32_t* ptsh2 = allocPage();
        memset(ptsh2, 0x0, PAGE_SIZE);

        //*(sh1 + (uint32_t)(i * sizeof(uint32_t))) = (uint32_t)ptsh1;
        //*(sh2 + (uint32_t)(i * sizeof(uint32_t))) = (uint32_t)ptsh2;
        writePhysical((uint32_t)sh1, i, (uint32_t)ptsh1);
        writePhysical((uint32_t)sh2, i, (uint32_t)ptsh2);
    }

    DEBUG(TRACE, "Page allocation ends at %x, multiplexer descriptor is %x\n", firstFreePage, partitionDescriptor);

    writePhysical((uintptr_t)partitionDescriptor, 0, (uintptr_t)partitionDescriptor); // Store descriptor into descriptor
    writePhysical((uintptr_t)partitionDescriptor, 1, (uintptr_t)partitionDescriptor);
    writePhysical((uintptr_t)partitionDescriptor, 2, (uintptr_t)kernelDirectory); // Store page directory into descriptor
    writePhysical((uintptr_t)partitionDescriptor, 3, (uintptr_t)kernelDirectory);
    writePhysical((uintptr_t)partitionDescriptor, 4, (uintptr_t)sh1); // Store shadow 1 into descriptor
    writePhysical((uintptr_t)partitionDescriptor, 5, (uintptr_t)sh1);
    writePhysical((uintptr_t)partitionDescriptor, 6, (uintptr_t)sh2); // Store shadow 2 into descriptor
    writePhysical((uintptr_t)partitionDescriptor, 7, (uintptr_t)sh2);
    writePhysical((uintptr_t)partitionDescriptor, 8, (uintptr_t)sh3); // Store shadow 3 into descriptor
    writePhysical((uintptr_t)partitionDescriptor, 9, (uintptr_t)sh3);
    writePhysical((uintptr_t)partitionDescriptor, 10, (uintptr_t)0xFFFFFFFF); // Store IO mask into descriptor, allowing any IO
    writePhysical((uintptr_t)partitionDescriptor, 11, (uintptr_t)0); //parent paddr: null for multiplexer

    // Current partition is now our descriptor
    updateCurPartition((uintptr_t)partitionDescriptor);
    updateRootPartition((uintptr_t)partitionDescriptor);

    // Create fake IDT at 0xFFFFF000
    uint32_t* virt_intv = allocPage();
    mapPageWrapper(kernelDirectory, (uint32_t)virt_intv, 0xFFFFF000, 1);

    // Fill Virtu. IDT info
    extern uint32_t __multiplexer;
    *virt_intv = (uint32_t)(&__multiplexer); // Multiplexer load addr

    DEBUG(INFO, "Partition environment is ready\n");
}
