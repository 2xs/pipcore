/*******************************************************************************/
/*  © Université Lille 1, The Pip Development Team (2015-2018)                 */
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

/* IDT configuration */
#include "idt.h"

/* TODO Remove me once rewritten in Coq */
#include "yield_c.h"

#define STACK_TOP_ADDR 0XFFFFE000

/**
 * \brief Virtual address at which to load the multiplexer.
 */
extern void __multiplexer();
#define MULTIPLEXER_LOAD_ADDR (uint32_t)&__multiplexer

pip_fpinfo* fpinfo;


/**
 * \fn void spawn_first_process()
 * \brief Spawns the multiplexer.
 *
 * Spawns the multiplexer given into the first partition space.
 */ 
void spawnFirstPartition(void)
{
	uint32_t pageDir, pt, vidtPaddr;
	void *usrStack;
	user_ctx_t *ctx;


	// Install and test MMU
	DEBUG(INFO, "-> Initializing MMU.\n");
	initMmu();

	pageDir = readPhysicalNoFlags(getRootPartition(), indexPD()+1);

	DEBUG(TRACE, "multiplexer cr3 is %x\n", pageDir);

	// Find virtual interrupt vector for partition
	pt = readPhysicalNoFlags((uintptr_t)pageDir, getTableSize() - 1);
	vidtPaddr = readPhysicalNoFlags(pt, getTableSize() - 1);

	// Build initial execution context of multiplexer (architecture dependent)
	ctx = (user_ctx_t *)(STACK_TOP_ADDR + PAGE_SIZE - sizeof(*ctx));
	ctx->eip = (uint32_t) __multiplexer;
	ctx->pipflags = 0; // VCLI
	ctx->eflags = 0x2; // reserved (bit 1)
	// ctx is the top of the stack
	ctx->regs.esp = (uint32_t)ctx;
	ctx->regs.ebx = 0xFFFFC000; /* emulate grub behaviour: pass meminfo in ebx
       					meminfo is mapped in initMmu for now.	*/
	ctx->valid = 1;
	
	/* Write context address in vidt'0 */
	writePhysical(vidtPaddr,  0, (uint32_t)ctx);
	writePhysical(vidtPaddr, 32, (uint32_t)ctx);

	DEBUG(INFO, "Boot sequence completed - now switching to userland\n");
	switchContextCont(getRootPartition(), pageDir, 0, 0, ctx);
	for(;;);
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
int c_main(struct multiboot *mbootPtr)
{
	initSerial();
	DEBUG(INFO, "Pip kernel, git revision %s\n", GIT_REVISION);
	
	// Install GDT & IDT
	DEBUG(INFO, "-> Initializing GDT.\n");
	gdt_init();
	DEBUG(INFO, "-> Initializing interrupts.\n");

	setKernelStack(0x300000);
	idt_init();
	
	// Initialize free page list
	DEBUG(INFO, "-> Initializing paging.\n");
	dumpMmap((uint32_t*)mbootPtr->mmap_addr, mbootPtr->mmap_length);
	
	DEBUG(INFO, "-> Now spawning multiplexer in userland.\n");
	spawnFirstPartition();

	DEBUG(CRITICAL, "-> Unexpected multiplexer return freezing\n");
	for(;;);
	return 0xCAFECAFE;
} 
