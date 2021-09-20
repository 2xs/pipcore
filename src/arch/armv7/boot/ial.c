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

#include "context.h"
#include "Internal.h"
#include "periph.h"
#include "debug.h"
#include "mal.h"

/* Prototypes of control flow transfer services entrypoints */
#include "Services.h"

#define LOG2(x) ((sizeof(uint32_t) << 3) - __builtin_clz(x) - 1)

#define DOUBLE_FAULT_LEVEL 8

void propagateFault(page callerPartDesc, page callerPageDir, unsigned targetInterrupt, unsigned callerContextSaveIndex, unsigned nbL, interruptMask flagsOnYield, interruptMask flagsOnWake, user_ctx_t *callerInterruptedContext)
{
	int rc = getParentPartDescCont(callerPartDesc, callerPageDir, targetInterrupt, callerContextSaveIndex, nbL, flagsOnYield, flagsOnWake, callerInterruptedContext);
	switch(rc) {
		case coq_FAIL_UNAVAILABLE_CALLER_VIDT:
		case coq_FAIL_CALLER_CONTEXT_SAVE:
			if (rc == coq_FAIL_UNAVAILABLE_CALLER_VIDT) {
				DEBUG(INFO, "Faulting partition's VIDT is unavailable, can not salvage its context\n");
			}
			else {// (rc == coq_CALLER_CONTEXT_SAVE)
				DEBUG(INFO, "Faulting partition's context save address is not valid, can not salvage its context\n");
			}
			DEBUG(TRACE, "Skip saving the interrupted partition's context\n");
			getTargetVidtCont(getParent(callerPartDesc), callerPageDir, getVidtVAddr(), 0, targetInterrupt, nbL, getIndexOfAddr(getVidtVAddr(), fstLevel), flagsOnYield, flagsOnWake, 0);
			break;
		case coq_FAIL_ROOT_CALLER:
			DEBUG(ERROR, "Root partition faulted, guru meditation.\n");
			for(;;);
			break;
		default:
			DEBUG(ERROR, "Error, parent partition can not handle the fault, propagating a double fault.\n");
			// Be sure to handle the root case differently, as it has no parent
			page parentPartDesc = getParent(callerPartDesc);
			// We are still trying to save the faulting partition's context, even though it is very unlikely the partition will ever wake up again
			// TODO is it worth a try ?
			propagateFault(parentPartDesc, callerPageDir, DOUBLE_FAULT_LEVEL, callerContextSaveIndex, nbL, flagsOnYield, flagsOnWake, callerInterruptedContext);
			break;
	}
}

void __attribute__((noreturn)) ial_fault_handler(gate_ctx_t *ctx, uint32_t fault_no)
{
	DEBUG(TRACE, "Received fault int n°%d\n", fault_no);

	user_ctx_t uctx;
	uctx.spsr    = ctx->spsr;
	uctx.reg[ 0] = ctx->reg[ 0];
	uctx.reg[ 1] = ctx->reg[ 1];
	uctx.reg[ 2] = ctx->reg[ 2];
	uctx.reg[ 3] = ctx->reg[ 3];
	uctx.reg[ 4] = ctx->reg[ 4];
	uctx.reg[ 5] = ctx->reg[ 5];
	uctx.reg[ 6] = ctx->reg[ 6];
	uctx.reg[ 7] = ctx->reg[ 7];
	uctx.reg[ 8] = ctx->reg[ 8];
	uctx.reg[ 9] = ctx->reg[ 9];
	uctx.reg[10] = ctx->reg[10];
	uctx.reg[11] = ctx->reg[11];
	uctx.reg[12] = ctx->reg[12];
	uctx.reg[13] = ctx->reg[13];
	uctx.reg[14] = ctx->reg[14];
	uctx.reg[15] = ctx->reg[15];
	uctx.valid   = 1;

	// TODO The below code could be written in Coq

	page currentPartDesc = getCurPartition();
	//DEBUG(TRACE, "Fault interrupt handler - Got current partition : %x\n", currentPartDesc);
	interruptMask currentPartitionIntState = get_self_int_state();
	unsigned saveIndex;
	if (currentPartitionIntState == 0) {
		//DEBUG(TRACE, "Fault interrupt handler - Partition is VCLI'd, saving its context in index %x\n", CLI_SAVE_INDEX);
		saveIndex = CLI_SAVE_INDEX;
	}
	else {
		//DEBUG(TRACE, "Fault interrupt handler - Partition is VSTI'd, saving its context in index %x\n", STI_SAVE_INDEX);
		saveIndex = STI_SAVE_INDEX;
	}
	//DEBUG(TRACE, "Fault interrupt handler - Retrieved interrupt state from current partition : %d\n", currentPartitionIntState);
	page currentPageDir  = getPd(currentPartDesc);
	//DEBUG(TRACE, "Fault interrupt handler - Got current page dir : %x\n", currentPageDir);
	propagateFault(currentPartDesc, currentPageDir, fault_no, saveIndex, getNbLevel(), currentPartitionIntState, currentPartitionIntState, &uctx);
	for (;;);
}

void __attribute__((noreturn)) ial_irq_handler(gate_ctx_t *ctx)
{
	/* Quad-A7 control
	 * 4.10 Core interrupt sources
	 *
	 * The cores can get an interrupt or fast interrupt from many
	 * places. In order to speed up interrupt processing the
	 * interrupt source registers shows what the source bits are for
	 * the IRQ/FIQ. As is usual there is a register for each
	 * processor.
	 */
	uint32_t int_no = LOG2(*CORE0_IRQ_SOURCE);

	DEBUG(TRACE, "Received hardware int n°%d\n", int_no);

	/* Quad-A7 control
	 * 4.11 Local timer
	 *
	 * The interrupt flag is clear by writing bit 31 high of the
	 * local timer IRQ clear & reload register.
	 *
	 * The IRQ clear & reload registerhas one extra bit: when
	 * writing bit 30 high, the local timer is immediately reloaded
	 * without generating an interrupt. As such it can also be used
	 * as a watchdog timer.
	 */
	*LOCAL_TIMER_WRITE_FLAGS = ((1 << 31) | (1 << 30));

	user_ctx_t uctx;
	uctx.spsr    = ctx->spsr;
	uctx.reg[ 0] = ctx->reg[ 0];
	uctx.reg[ 1] = ctx->reg[ 1];
	uctx.reg[ 2] = ctx->reg[ 2];
	uctx.reg[ 3] = ctx->reg[ 3];
	uctx.reg[ 4] = ctx->reg[ 4];
	uctx.reg[ 5] = ctx->reg[ 5];
	uctx.reg[ 6] = ctx->reg[ 6];
	uctx.reg[ 7] = ctx->reg[ 7];
	uctx.reg[ 8] = ctx->reg[ 8];
	uctx.reg[ 9] = ctx->reg[ 9];
	uctx.reg[10] = ctx->reg[10];
	uctx.reg[11] = ctx->reg[11];
	uctx.reg[12] = ctx->reg[12];
	uctx.reg[13] = ctx->reg[13];
	uctx.reg[14] = ctx->reg[14];
	uctx.reg[15] = ctx->reg[15];
	uctx.valid   = 1;

	//TODO The next few lines of code could be written in Coq

	page rootPartDesc = getRootPartition();
	//DEBUG(TRACE, "Hardware interrupt handler - Got root partition : %x\n", rootPartDesc);
	page intPartitionPartDesc = getCurPartition();
	//DEBUG(TRACE, "Hardware interrupt handler - Got interrupted partition : %x\n", intPartitionPartDesc);
	interruptMask intPartitionIntState = get_self_int_state();
	unsigned saveIndex;
	if (intPartitionIntState == 0) {
		//DEBUG(TRACE, "Hardware interrupt handler - Partition is VCLI'd, saving its context in index %x\n", CLI_SAVE_INDEX);
		saveIndex = CLI_SAVE_INDEX;
	}
	else {
		//DEBUG(TRACE, "Hardware interrupt handler - Partition is VSTI'd, saving its context in index %x\n", STI_SAVE_INDEX);
		saveIndex = STI_SAVE_INDEX;
	}
	//DEBUG(TRACE, "Hardware interrupt handler - Retrieved interrupt state from interrupted partition : %d\n", intPartitionIntState);
	page intPartitionPageDir  = getPd(intPartitionPartDesc);
	//DEBUG(TRACE, "Hardware interrupt handler - Retrieved interrupted partition page dir : %x\n", intPartitionPageDir);
	yield_checks rc = getSourceVidtCont(rootPartDesc, intPartitionPageDir, int_no, saveIndex, getNbLevel(), intPartitionIntState, intPartitionIntState, &uctx);
	switch(rc) {
		case coq_FAIL_UNAVAILABLE_CALLER_VIDT:
		case coq_FAIL_CALLER_CONTEXT_SAVE:
			if (rc == coq_FAIL_UNAVAILABLE_CALLER_VIDT) {
				DEBUG(INFO, "Interrupted partition's VIDT is unavailable, can not salvage its context\n");
			}
			else {// (rc == coq_CALLER_CONTEXT_SAVE)
				DEBUG(INFO, "Interrupted partition's context save address is not valid, can not salvage its context\n");
			}
			DEBUG(TRACE, "Skip saving the interrupted partition's context\n");
			getTargetVidtCont(rootPartDesc, intPartitionPageDir, getVidtVAddr(), 0, int_no, getNbLevel(), getIndexOfAddr(getVidtVAddr(), fstLevel), 0, 0, &uctx);
			break;
		default:
			DEBUG(ERROR, "Unrecoverable error occured during while loading the root interruption handler - guru meditation\n");
	}
	for (;;);
}

void __attribute__((noreturn)) ial_fiq_handler(gate_ctx_t *ctx)
{
	(void) ctx;
	printf("fiq handler!\n");
	for(;;);
}
