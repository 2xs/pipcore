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

/* Beurk */
#include "x86int.h"

/**
 * \brief Virtual address at which to load the multiplexer.
 */
extern void __multiplexer();
#define MULTIPLEXER_LOAD_ADDR (uint32_t)&__multiplexer

pip_fpinfo* fpinfo;

#if 0
typedef struct user_ctx_s
{
	uint32_t eip;
	uint32_t pipflags;
	uint32_t eflags;
	pushad_regs_t regs;
	uint32_t valid;
	uint32_t nfu[4];
} user_ctx_t;
#endif

extern void resumeAsm(user_ctx_t *ctx);
#define loadContext resumeAsm

void updateCurPartAndActivate(uint32_t calleePartDesc, uint32_t calleePageDir) {
	DEBUG(CRITICAL, "Updating current partition to %x\n", calleePartDesc);
	updateCurPartition(calleePartDesc);
	DEBUG(CRITICAL, "Activating MMU for the current partition (page directory %x)\n", calleePageDir);
	activate(calleePageDir);	
}

void switchContext(uint32_t calleePartDesc, uint32_t calleePageDir, user_ctx_t *ctx){
	updateCurPartAndActivate(calleePartDesc, calleePageDir);
	DEBUG(CRITICAL, "Loading context into registers...\n");
	loadContext(ctx);
}

/**
 * \fn void spawn_first_process()
 * \brief Spawns the multiplexer.
 *
 * Spawns the multiplexer given into the first partition space.
 */ 
void spawnFirstPartition()
{
	uint32_t pageDir, pt, vidtPaddr;
	void *usrStack;
	user_ctx_t *ctx;


	// Install and test MMU
	DEBUG(INFO, "-> Initializing MMU.\n");
	initMmu();

	pageDir = readPhysicalNoFlags(getRootPartition(), indexPD()+1);

	DEBUG(TRACE, "multiplexer cr3 is %x\n", pageDir);

	// Prepare kernel stack for multiplexer
	usrStack = (void*)0xFFFFE000;

	// Find virtual interrupt vector for partition
	pt = readPhysicalNoFlags((uintptr_t)pageDir, getTableSize() - 1);
	vidtPaddr = readPhysicalNoFlags(pt, getTableSize() - 1);

	// Build initial execution context of multiplexer (architecture dependent)
	// Maybe we don't need to decrement the stack pointer though
	usrStack = ctx = (user_ctx_t *)(usrStack - sizeof(*ctx));
	ctx->eip = (uint32_t) __multiplexer;
	DEBUG(INFO, "__multiplexer %x\n", ctx->eip);
	ctx->pipflags = 1; // TODO
	ctx->eflags = 0;
	ctx->regs.esp = (uint32_t)usrStack;
	ctx->regs.ebx = 0xFFFFC000; /* emulate grub behaviour: pass meminfo in ebx
       					meminfo is mapped in initMmu for now.	*/
	ctx->valid = 1;
	
	/* Write context address in vidt'0 */ 
	writePhysical(vidtPaddr, 0, (uint32_t)ctx);

	DEBUG(INFO, "Calling switchContext !\n");
	switchContext(getRootPartition(), pageDir, ctx);
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
	gdtInstall();
	DEBUG(INFO, "-> Initializing interrupts.\n");

	setKernelStack(0x300000);
	initInterrupts();
	
	// Initialize free page list
	DEBUG(INFO, "-> Initializing paging.\n");
	dumpMmap((uint32_t*)mbootPtr->mmap_addr, mbootPtr->mmap_length);
	
	DEBUG(INFO, "-> Now spawning multiplexer in userland.\n");
	spawnFirstPartition();


	// Send virtual IRQ 0 to partition
//        DEBUG(TRACE, "Dispatching from boot sequence to root partition.\n");
//	dispatch2(getRootPartition(), 0, 0x1e75b007, (uint32_t)0xFFFFC000, 0);

	DEBUG(CRITICAL, "-> Unexpected multiplexer return freezing\n");
	for(;;);
	return 0xCAFECAFE;
} 
