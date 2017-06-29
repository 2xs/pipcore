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
 * \file boot.c
 * \brief C entrypoint for the kernel
 * \author Quentin B.
 */

/* This is provided by freestanding GCC libraries */

#define mainWAIT_FOR_DEBUG_CONNECTION 1

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
#include "hardware.h"


/* Include serial only if we're in debug mode */
#ifdef PIPDEBUG
#include "serial.h"
#endif

/**
 * \brief Virtual address at which to load the multiplexer.
 */
extern uint32_t __multiplexer;
#define MULTIPLEXER_LOAD_ADDR (uint32_t)&__multiplexer

pip_fpinfo* fpinfo;

/**
 * \fn void spawn_first_process()
 * \brief Spawns the multiplexer.
 *
 * Spawns the multiplexer given into the first partition space.
 */
void spawnFirstPartition()
{
    uint32_t multiplexer_cr3 = readPhysicalNoFlags(getRootPartition(), indexPD()+1);

    DEBUG(TRACE, "multiplexer cr3 is %x\n", multiplexer_cr3);

    // Prepare kernel stack for multiplexer
    uint32_t *usrStack = /*allocPage()*/(uint32_t*)0x1E00000, *krnStack = /*allocPage()*/(uint32_t*)0x300000;
    setKernelStack((uint32_t)krnStack);

    DEBUG(TRACE, "kernel stack is %x\n", krnStack);

    // Find virtual interrupt vector for partition
    uintptr_t ptVirq = readPhysicalNoFlags((uintptr_t)multiplexer_cr3, getTableSize() - 1);
    uintptr_t virq = readPhysicalNoFlags(ptVirq, getTableSize() - 1);

    // Set user stack into virq
    uint32_t target = (uint32_t)(virq) + sizeof(uint32_t);
    *(uint32_t*)target = (uint32_t)usrStack;

    DEBUG(TRACE, "user stack is %x\n", usrStack);

    *(uint32_t*)usrStack = 0x0;

    // Send virtual IRQ 0 to partition
    dispatch2(getRootPartition(), 0, 0x1e75b007, (uint32_t)fpinfo, 0);
}

/**
 * \fn uintptr_t fillFpInfo()
 * \brief Creates and fills in the first partition info structure
 */
uintptr_t fillFpInfo()
{
    extern uint32_t __end;
    extern uint32_t ramEnd;
    // Allocate page
    DEBUG(TRACE,"THE END OF THE RAM IS : %x, and the membegin = %x",__end,(uint32_t) &__end);
    uint32_t* pgFpinfo = allocPage();

    // Fill first partition info structure
    fpinfo = (pip_fpinfo*)pgFpinfo;
    fpinfo->magic = FPINFO_MAGIC;
    fpinfo->membegin = (uint32_t)&__end;
    fpinfo->memend = ramEnd;
    strcpy(fpinfo->revision, GIT_REVISION);

    return (uintptr_t)fpinfo;
}
#define MULTIBOOT_BOOTINFO_MMAP	0x00000040
void fixFpInfo()
{
    fpinfo->membegin = (uint32_t)firstFreePage;
}

/**
 * \fn int c_main (struct multiboot *mboot_ptr)
 * \brief Entrypoint
 *
 * Entrypoint of the C kernel.
 *
 * \param mboot_ptr Pointer to the multiboot structure, should be on %EBX after boot0.s
 * \return Should not return.
 */

int c_main(uint32_t magic, struct multiboot *mbootPtr)
{


    setupHardware();
    DEBUG(INFO, "Pepin, git revision %s\n", GIT_REVISION);
    // Install GDT & IDT
    DEBUG(INFO, "-> Initializing ISR.\n");
    initInterrupts();
    DEBUG(INFO, "-> Initializing GDT.\n");
    gdtInstall();
    // Initialize free page list
    DEBUG(INFO, "-> Initializing paging.\n");
    dumpMmap((uint32_t*)mbootPtr->mmap_addr, mbootPtr->mmap_length);

    DEBUG(INFO, "-> Initializing first partition info.\n");
    uintptr_t info_str = fillFpInfo();

    // Install and test MMU
    DEBUG(INFO, "-> Initializing MMU.\n");
    initMmu();

    DEBUG(INFO, "-> Now spawning multiplexer in userland.\n");
    fixFpInfo();
    spawnFirstPartition();

    DEBUG(CRITICAL, "-> Unexpected multiplexer return freezing\n");
    for(;;);
    return 0xCAFECAFE;
}
