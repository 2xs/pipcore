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
 * \file boot.c
 * \brief C entrypoint for the kernel
 * \author Quentin B.
 */

/* This is provided by freestanding GCC libraries */
#include <stdint.h>

/* This is provided by our hardware abstraction layers */
#include "mal.h"
#include "ial.h"
#include "git.h"
#include "fpinfo.h"

/* Some debugging output if PIPDEBUG is set */
#include "debug.h"
#include "serial.h"

/* Multiboot header info */
#include "multiboot.h"

/* MMU configuration */
#include "mmu.h"

/* Pseudo-libC include */
#include "libc.h"

/* GDT configuration */
#include "gdt.h"
#include "syscall.h"

/* Include serial only if we're in debug mode */
#ifdef PIPDEBUG
#include "serial.h"
#endif

#include "apic.h"
#include "smp-imps.h"

/* SMP */
#include "mp.h"
#include "lock.h"

/* Bootup stage spinlock */
static spinlock_t lock_cores = 0;
static spinlock_t mmu_init_spinlock = 0;

uint32_t initializedCores = 0;
int mp_model = MPMODEL_SINGLETHREAD;

/* MP stacks */
extern void* mp_stack_base;
unsigned char* mp_stacks;

/**
 * \brief Virtual address at which to load the multiplexer.
 */
extern uint32_t __multiplexer;
#define MULTIPLEXER_LOAD_ADDR (uint32_t)&__multiplexer

uint32_t nextFreeCoreStack = 0;
uint32_t cores = 0; /* Only BSP until APs boot */
pip_fpinfo* fpinfo[16];

pip_mboot_partition_t bootparts[4]; /* Per-core multiplexers */
uint32_t furthestPartitionCode;

void preparePartitions(struct multiboot *mboot_ptr)
{
    extern uint32_t __multiplexer, __end;
    /* First partition, embedded into Pip */
    uint32_t i;
    bootparts[0].start = (uint32_t)&__multiplexer; 
    bootparts[0].end = (uint32_t)&__end;
    
    /* Update first partition address in furthest partition code */
    furthestPartitionCode = bootparts[0].end;

    uint32_t modc = mboot_ptr->mods_count;
    if(modc < (coreCount() - 1)) {
        DEBUG(CRITICAL, "Expected %d modules, found %d. Switching to full multithread model.\n", coreCount() - 1, modc);
        mp_model = MPMODEL_MULTITHREAD;
        return;
    }

    multiboot_module_t* modi = (multiboot_module_t*)mboot_ptr->mods_addr;
    for(i=0; i<modc; i++)
    {
        bootparts[i+1].start = modi->mod_start;
        bootparts[i+1].end = modi->mod_end;
        furthestPartitionCode = modi->mod_end;
        modi++;
    }
    for(i=0; i<4;i++)
        DEBUG(CRITICAL, "Root partition for core %d: %x -> %x\n", i, bootparts[i].start, bootparts[i].end);
}

/**
 * \fn void spawn_first_process()
 * \brief Spawns the multiplexer.
 *
 * Spawns the multiplexer given into the first partition space.
 */ 
void spawnFirstPartition()
{
    if(IS_MPMT && coreId() > 0)
    {
        DEBUG(CRITICAL, "MultiThread: Core %d ready, waiting for BSP's dispatch() request\n", coreId());
        return;
    }
	uint32_t multiplexer_cr3 = readPhysicalNoFlags(getRootPartition(), indexPD()+1);

	// Prepare kernel stack for multiplexer
	uint32_t *usrStack = (uint32_t*)0xFFFF0000 - sizeof(uint32_t), *krnStack = (uint32_t*)(0x300000 - 4*PAGE_SIZE*coreId());
	setKernelStack((uint32_t)krnStack);

	/* Find virtual interrupt vector for partition */
	uintptr_t ptVirq = readPhysicalNoFlags((uintptr_t)multiplexer_cr3, getTableSize() - 1);
	uintptr_t virq = readPhysicalNoFlags(ptVirq, getTableSize() - 1);
	
	/* Set VCLI flag ! */
	writePhysicalNoFlags(virq, getTableSize()-1, 0x1);
	IAL_DEBUG(CRITICAL, "Root VIDT at %x has set flags at %x to 0x1.\n", virq, virq + 0xFFC);
	
	/* Send virtual IRQ 0 to partition */
	dispatch2(getRootPartition(), 0, 0, 0xFFFF1000, 0);
}

/**
 * \fn uintptr_t fillFpInfo()
 * \brief Creates and fills in the first partition info structure
 */
uintptr_t fillFpInfo()
{
	extern uint32_t __end;
	extern uint32_t ramEnd;

	DEBUG(TRACE, "FPInfo now at %x\n", fpinfo[coreId()]);
	
	return (uintptr_t)fpinfo[coreId()];
}

void fixFpInfo()
{
	fpinfo[coreId()]->membegin = (uint32_t)firstFreePage;
}

uint32_t multEnd;

void safe_mp_boot_part()
{
    /* Wait for all cores to be ready and kernel to idle */
    while(initializedCores < coreCount());

    DEBUG(CRITICAL, "-> Starting up root partition.\n");
    spawnFirstPartition();
    for(;;);
}

void safe_mp_finish_bootstrap()
{
    MP_LOCK(mmu_init_spinlock);
    DEBUG(CRITICAL, "-> Filling virtual memory space for core %d.\n", coreId());
    fillMmu(bootparts[coreId()].vend);
    DEBUG(CRITICAL, "-> Done. Enabling MMU.\n");
    coreEnableMmu();
    initializedCores++;
    MP_UNLOCK(mmu_init_spinlock);
    DEBUG(CRITICAL, "-------------------------------\n");
    safe_mp_boot_part();
}

void safe_mp_c_main()
{
    DEBUG(CRITICAL, "-> Entered safe AP core bootup stage.\n");
    DEBUG(CRITICAL, "-> Initializing CPU%d.\n", cores);
    initInterrupts();
    DEBUG(CRITICAL, "-> Initializing GDT.\n");
    gdtInstall();
    DEBUG(CRITICAL, "-> Initializing SYSENTER\n");
    init_sysenter(coreId());
    DEBUG(CRITICAL, "-> Initializing MMU.\n");
    multEnd = initMmu();
    DEBUG(CRITICAL, "-> MMU for core %d is configured!\n", coreId());
    DEBUG(CRITICAL, "-> Releasing spinlock.\n");
    initializedCores++;
    MP_UNLOCK(lock_cores);
    DEBUG(CRITICAL, "-------------------------------\n");
    safe_mp_finish_bootstrap();
}

int mp_c_main()
{
    extern void give_safe_stack();
    /* Initialize core per core : lock and go */
    MP_LOCK(lock_cores);
    cores++;
    DEBUG(CRITICAL, "MP stacks were at %x\n", mp_stacks);
    mp_stacks -= 0x1000; /* Give sum stack */
    DEBUG(CRITICAL, "-----------CPU%d BOOT-----------\n", coreId());
    DEBUG(CRITICAL, "-> Giving core %d stack %x\n", coreId(), mp_stacks);
    /* give_safe_stack(mp_stacks); */ /* Give a proper and safe stack to the current core */
    __asm volatile("MOV %0, %%ESP; MOV %%ESP, %%EBP;" :: "r"(mp_stacks));
    safe_mp_c_main();
    for(;;);
    return 1;
}

/**
 * \fn int c_main (struct multiboot *mboot_ptr)
 * \brief Entrypoint
 *
 * Entrypoint of the C kernel.
 *
 * \param boot_ptr Pointer to the multiboot structure, should be on %EBX after boot0.s
 * \return Should not return.
 */
int c_main(struct multiboot *mbootPtr)
{
	initSerial();
	DEBUG(INFO, "Pip kernel, git revision %s\n", GIT_REVISION);

    DEBUG(INFO, "Multiboot information at %x, mem_lower=%x, mem_upper=%x, flags=%x\n", mbootPtr, mbootPtr->mem_lower, mbootPtr->mem_upper, mbootPtr->flags);

    DEBUG(CRITICAL, "Initializing CPU0.\n");
   

    /* First install BSP's GDT so that our APs can use it */
	DEBUG(CRITICAL, "-> Initializing BSP's GDT.\n");
	gdtInstall();

    mp_stacks = (unsigned char*)&mp_stack_base;
    DEBUG(CRITICAL, "MP stack base at %x\n", mp_stacks); 

    /* Lock MP initialization. */
    MP_LOCK(lock_cores);
    MP_LOCK(mmu_init_spinlock);

    /* Bootup APs. */
    DEBUG(CRITICAL, "-> Initializing SMP.\n");
    init_mp();

    DEBUG(CRITICAL, "-> %d cores detected and running.\n", (uint32_t)coreCount());

    preparePartitions(mbootPtr);
    
    // Install GDT & IDT
	DEBUG(INFO, "-> Initializing ISR.\n");
	initInterrupts();
    
    // Initialize free page list
	DEBUG(INFO, "-> Initializing paging.\n");
	dumpMmap((uint32_t*)mbootPtr->mmap_addr, mbootPtr->mmap_length);

	// Install and test MMU
	DEBUG(INFO, "-> Initializing MMU.\n");
	uint32_t partEnd = initMmu();

    /* I don't know why this is required on some build hosts. I may have f**ked up something elsewhere... */
    if((uint32_t)mp_stacks >= 0x700000)
        mp_stacks = (unsigned char*)&mp_stack_base;

    DEBUG(CRITICAL, "MP stack base at %x\n", mp_stacks); 
    initializedCores++;

    DEBUG(CRITICAL, "Initializing SYSENTER\n");
    init_sysenter(0);

	/* Great. Now we can bootstrap APs correctly. */
    DEBUG(CRITICAL, "-> Releasing CPU cores.\n");
    MP_UNLOCK(lock_cores);

    /* Active wait for cores to be ready */
    while(initializedCores < coreCount());

    /* All cores have their MMU. Finish their initialization and enter userland. */
    initializedCores = 1;
    
    /* Release page allocator and enable MMU */
    prepareAllocatorRelease();
    fillMmu(bootparts[coreId()].vend);
    coreEnableMmu();

    MP_UNLOCK(mmu_init_spinlock);

    /* Wait again */
    while(initializedCores < coreCount());

    DEBUG(INFO, "-> Now spawning multiplexer in userland.\n");
   // SEND_NMIPI(0x1);
    spawnFirstPartition();

    
	DEBUG(CRITICAL, "-> Unexpected multiplexer return freezing\n");
	for(;;);
	return 0xCAFECAFE;
} 
