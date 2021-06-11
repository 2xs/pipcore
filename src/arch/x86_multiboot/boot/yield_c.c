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

#include "yield_c.h"
#include "pip_interrupt_calls.h"


vaddr_t getVidtVAddr() {
	return 0xFFFFF000;
}

int_mask_t readInterruptMask(page_t vidt) { //unimplemented
	return 0u;
}

bool isInterruptMasked(int_mask_t int_mask, uint32_t index) { //unimplemented
	return false;
}

vaddr_t getNthVAddrFrom(vaddr_t base, uint32_t size) {
	return ((uint32_t) base) + size;
}

/* Reads a Vaddr from userland in current partition */
vaddr_t readUserlandVAddr(page_t mpage, uint32_t index) {
	return readPhysical(mpage, index);
}

void writeContext(user_ctx_t *ctx, vaddr_t ctxSaveVAddr, int_mask_t flagsOnWake) {
	user_ctx_t *userland_save_ptr = (user_ctx_t *) ctxSaveVAddr;
	userland_save_ptr->eip      = ctx->eip;
	userland_save_ptr->pipflags = flagsOnWake;
	userland_save_ptr->eflags   = ctx->eflags;
	userland_save_ptr->regs     = ctx->regs;
	userland_save_ptr->valid    = 1;
}

void loadContext(user_ctx_t *ctx, unsigned enforce_interrupts);


yield_checks_t yieldGlue(gate_ctx_t *callerInterruptedContext, vaddr_t calleePartDescVAddr, uservalue_t userTargetInterrupt, uservalue_t userCallerContextSaveIndex, int_mask_t flagsOnYield, int_mask_t flagsOnWake);

yield_checks_t checkIntLevelCont(vaddr_t calleePartDescVAddr, uservalue_t userTargetInterrupt, uservalue_t userCallerContextSaveIndex, int_mask_t flagsOnYield, int_mask_t flagsOnWake, user_ctx_t *callerInterruptedContext);

yield_checks_t checkCtxSaveIdxCont(vaddr_t calleePartDescVAddr, unsigned targetInterrupt, uservalue_t userCallerContextSaveIndex, int_mask_t flagsOnYield, int_mask_t flagsOnWake, user_ctx_t *callerInterruptedContext);

yield_checks_t getChildPartDescCont(page_t callerPartDesc, page_t callerPageDir, vaddr_t calleePartDescVAddr, unsigned targetInterrupt, unsigned callerContextSaveIndex, unsigned nbL, int_mask_t flagsOnYield, int_mask_t flagsOnWake, user_ctx_t *callerInterruptedContext);

yield_checks_t getParentPartDescCont(page_t callerPartDesc, page_t callerPageDir, unsigned targetInterrupt, unsigned callerContextSaveIndex, unsigned nbL, int_mask_t flagsOnYield, int_mask_t flagsOnWake, user_ctx_t *callerInterruptedContext);

yield_checks_t getSourcePartVidtCont(page_t calleePartDesc, page_t callerPageDir, unsigned targetInterrupt, unsigned callerContextSaveIndex, unsigned nbL, int_mask_t flagsOnYield, int_mask_t flagsOnWake, user_ctx_t *callerInterruptedContext);

yield_checks_t getTargetPartVidtCont(page_t calleePartDesc, page_t callerPageDir, vaddr_t vidtVaddr, vaddr_t callerContextSaveVAddr, unsigned targetInterrupt, unsigned nbL, unsigned idxVidtInLastMMUPage, int_mask_t flagsOnYield, int_mask_t flagsOnWake, user_ctx_t *callerInterruptedContext);

yield_checks_t checkIntMaskCont(page_t calleePartDesc, page_t calleePageDir, page_t calleeVidt, page_t callerPageDir, page_t callerVidt, vaddr_t callerContextSaveVAddr, unsigned targetInterrupt, unsigned nbL, unsigned idxVidtInLastMMUPage, int_mask_t flagsOnYield, int_mask_t flagsOnWake, user_ctx_t *callerInterruptedContext);

yield_checks_t getTargetPartCtxCont(page_t calleePartDesc, page_t calleePageDir, page_t calleeVidt, page_t callerPageDir, vaddr_t callerContextSaveVAddr, unsigned targetInterrupt, unsigned nbL, int_mask_t flagsOnYield, int_mask_t flagsOnWake, user_ctx_t *callerInterruptedContext);

yield_checks_t saveSourcePartCtxCont(page_t calleePartDesc, page_t calleePageDir, page_t callerPageDir, vaddr_t callerContextSaveVAddr, unsigned nbL, int_mask_t flagsOnYield, int_mask_t flagsOnWake, user_ctx_t *callerInterruptedContext, user_ctx_t *targetContext);

yield_checks_t switchContextCont(page_t calleePartDesc, page_t calleePageDir, int_mask_t flagsOnYield, user_ctx_t *ctx);

yield_checks_t yieldGlue(gate_ctx_t *gate_ctx,
			 vaddr_t calleePartDescVAddr,
			 uservalue_t userTargetInterrupt,
			 uservalue_t userCallerContextSaveIndex,
			 int_mask_t flagsOnYield,
			 int_mask_t flagsOnWake){
	user_ctx_t user_ctx;
	user_ctx.regs = gate_ctx->regs;
	user_ctx.regs.esp = gate_ctx->useresp;
	user_ctx.eip = gate_ctx->eip;
	user_ctx.eflags = gate_ctx->eflags;
	user_ctx.valid = 1;

	return checkIntLevelCont(calleePartDescVAddr, userTargetInterrupt, userCallerContextSaveIndex, flagsOnYield, flagsOnWake, &user_ctx);
}

yield_checks_t checkIntLevelCont(vaddr_t calleePartDescVAddr,
				 uservalue_t userTargetInterrupt,
				 uservalue_t userCallerContextSaveIndex,
				 int_mask_t flagsOnYield,
				 int_mask_t flagsOnWake,
				 user_ctx_t *callerInterruptedContext)
{
	//check int level validity
	if (!(userTargetInterrupt < 256))
		return FAIL_INVALID_INT_LEVEL;
	unsigned char targetInterrupt = (unsigned char) userTargetInterrupt;
	return checkCtxSaveIdxCont(calleePartDescVAddr, targetInterrupt, userCallerContextSaveIndex, flagsOnYield, flagsOnWake, callerInterruptedContext);
}

yield_checks_t checkCtxSaveIdxCont(vaddr_t calleePartDescVAddr,
				   unsigned targetInterrupt,
				   uservalue_t userCallerContextSaveIndex,
				   int_mask_t flagsOnYield,
				   int_mask_t flagsOnWake,
				   user_ctx_t *callerInterruptedContext)
{
	//check save index validity
	if (!(userCallerContextSaveIndex < 256))
		return FAIL_INVALID_CTX_SAVE_INDEX;
	unsigned callerContextSaveIndex = (unsigned char) userCallerContextSaveIndex;


	page_t callerPartDesc = getCurPartition();
	page_t callerPageDir  = getPd(callerPartDesc);
	unsigned nbL = getNbLevel();

	if (calleePartDescVAddr == 0)
		return getParentPartDescCont(callerPartDesc, callerPageDir, targetInterrupt, callerContextSaveIndex, nbL, flagsOnYield, flagsOnWake, callerInterruptedContext);
	else
		return getChildPartDescCont(callerPartDesc, callerPageDir, calleePartDescVAddr, targetInterrupt, callerContextSaveIndex, nbL, flagsOnYield, flagsOnWake, callerInterruptedContext);
}

yield_checks_t getChildPartDescCont(page_t callerPartDesc,
				    page_t callerPageDir,
				    vaddr_t calleePartDescVAddr,
				    unsigned targetInterrupt,
				    unsigned callerContextSaveIndex,
				    unsigned nbL,
				    int_mask_t flagsOnYield,
				    int_mask_t flagsOnWake,
				    user_ctx_t *callerInterruptedContext)
{
	page_t childPartDescLastMMUPage = getTableAddr(callerPageDir, calleePartDescVAddr, nbL);
	if (childPartDescLastMMUPage == 0)
		return FAIL_INVALID_CHILD;
	unsigned idxChildPartDesc = getIndexOfAddr(calleePartDescVAddr, fstLevel);
	if (!(readPresent(childPartDescLastMMUPage, idxChildPartDesc)))
		return FAIL_INVALID_CHILD;
	if (!(checkChild(callerPartDesc, nbL, calleePartDescVAddr)))
		return FAIL_INVALID_CHILD;
	page_t calleePartDesc = readPhyEntry(childPartDescLastMMUPage, idxChildPartDesc);
	return getSourcePartVidtCont(calleePartDesc, callerPageDir, targetInterrupt, callerContextSaveIndex, nbL, flagsOnYield, flagsOnWake, callerInterruptedContext);
}

yield_checks_t getParentPartDescCont(page_t callerPartDesc,
				     page_t callerPageDir,
				     unsigned targetInterrupt,
				     unsigned callerContextSaveIndex,
				     unsigned nbL,
				     int_mask_t flagsOnYield,
				     int_mask_t flagsOnWake,
				     user_ctx_t *callerInterruptedContext)
{
	page_t rootPartDesc = getRootPartition();
	if (callerPartDesc == rootPartDesc)
		return FAIL_ROOT_CALLER;
	page_t calleePartDesc = getParent(callerPartDesc);
	return getSourcePartVidtCont(calleePartDesc, callerPageDir, targetInterrupt, callerContextSaveIndex, nbL, flagsOnYield, flagsOnWake, callerInterruptedContext);
}

yield_checks_t getSourcePartVidtCont(page_t calleePartDesc,
				     page_t callerPageDir,
				     unsigned targetInterrupt,
				     unsigned callerContextSaveIndex,
				     unsigned nbL,
				     int_mask_t flagsOnYield,
				     int_mask_t flagsOnWake,
				     user_ctx_t *callerInterruptedContext)
{
	//retrieve vidt vaddr
	vaddr_t vidtVaddr = getVidtVAddr();
	unsigned idxVidtInLastMMUPage = getIndexOfAddr(vidtVaddr, fstLevel);

	//retrieve caller VIDT
	page_t callerVidtLastMMUPage = getTableAddr(callerPageDir, vidtVaddr, nbL);
	if (callerVidtLastMMUPage == 0)
		return FAIL_UNAVAILABLE_CALLER_VIDT;
	if (!(readPresent(callerVidtLastMMUPage, idxVidtInLastMMUPage)))
		return FAIL_UNAVAILABLE_CALLER_VIDT;
	if (!(readAccessible(callerVidtLastMMUPage, idxVidtInLastMMUPage)))
		return FAIL_UNAVAILABLE_CALLER_VIDT;
	page_t callerVidt = readPhyEntry(callerVidtLastMMUPage, idxVidtInLastMMUPage);

	//save caller context if needed
	vaddr_t callerContextSaveVAddr = readUserlandVAddr(callerVidt, callerContextSaveIndex);
	return getTargetPartVidtCont(calleePartDesc, callerPageDir, vidtVaddr, callerContextSaveVAddr, targetInterrupt, nbL, idxVidtInLastMMUPage, flagsOnYield, flagsOnWake, callerInterruptedContext);
}


yield_checks_t getTargetPartVidtCont(page_t calleePartDesc,
				     page_t callerPageDir,
				     vaddr_t vidtVaddr,
				     vaddr_t callerContextSaveVAddr,
				     unsigned targetInterrupt,
				     unsigned nbL,
				     unsigned idxVidtInLastMMUPage,
				     int_mask_t flagsOnYield,
				     int_mask_t flagsOnWake,
				     user_ctx_t *callerInterruptedContext)
{
	page_t calleePageDir = getPd(calleePartDesc);

	page_t calleeVidtLastMMUPage = getTableAddr(calleePageDir, vidtVaddr, nbL);
	if (calleeVidtLastMMUPage == 0)
		return FAIL_UNAVAILABLE_TARGET_VIDT;
	if (!(readPresent(calleeVidtLastMMUPage, idxVidtInLastMMUPage)))
		return FAIL_UNAVAILABLE_TARGET_VIDT;
	if (!(readAccessible(calleeVidtLastMMUPage, idxVidtInLastMMUPage)))
		return FAIL_UNAVAILABLE_TARGET_VIDT;
	page_t calleeVidt = readPhyEntry(calleeVidtLastMMUPage, idxVidtInLastMMUPage);
	return getTargetPartCtxCont(calleePartDesc, calleePageDir, calleeVidt, callerPageDir, callerContextSaveVAddr, targetInterrupt, nbL, flagsOnYield, flagsOnWake, callerInterruptedContext);
}

// check interrupt status of the target is now dropped as we decided that it should be the responsibility of the parent
// to check if its child is ready to be resumed
//yield_checks_t checkIntMaskCont(page_t calleePartDesc,
//				page_t calleePageDir,
//				page_t calleeVidt,
//				page_t callerPageDir,
//				page_t callerVidt,
//				vaddr_t callerContextSaveVAddr,
//				unsigned targetInterrupt,
//				unsigned nbL,
//				unsigned idxVidtInLastMMUPage,
//				int_mask_t flagsOnYield,
//				int_mask_t flagsOnWake,
//				user_ctx_t *callerInterruptedContext)
//{
//	//check if callee accepts to recieve such interrupts
//	int_mask_t calleeInterruptMask = readInterruptMask(calleeVidt);
//	if (isInterruptMasked(calleeInterruptMask, targetInterrupt))
//		return FAIL_MASKED_INTERRUPT;
//	return getTargetPartCtxCont(calleePartDesc, calleePageDir, calleeVidt, callerPageDir, callerVidt, callerContextSaveVAddr, targetInterrupt, nbL, idxVidtInLastMMUPage, flagsOnYield, flagsOnWake, callerInterruptedContext);
//}

yield_checks_t getTargetPartCtxCont(page_t calleePartDesc,
				    page_t calleePageDir,
				    page_t calleeVidt,
				    page_t callerPageDir,
				    vaddr_t callerContextSaveVAddr,
				    unsigned targetInterrupt,
				    unsigned nbL,
				    int_mask_t flagsOnYield,
				    int_mask_t flagsOnWake,
				    user_ctx_t *callerInterruptedContext)
{
	//retrieve the callee's handler context
	vaddr_t calleeContextVAddr = readUserlandVAddr(calleeVidt, targetInterrupt);
	page_t calleeContextLastMMUPage = getTableAddr(calleePageDir, calleeContextVAddr, nbL);
	if (calleeContextLastMMUPage == 0)
		return FAIL_UNAVAILABLE_TARGET_CTX;
	unsigned idxCalleeContextPageInLastMMUPage = getIndexOfAddr(calleeContextVAddr, fstLevel);
	if (!(readPresent(calleeContextLastMMUPage, idxCalleeContextPageInLastMMUPage)))
		return FAIL_UNAVAILABLE_TARGET_CTX;
	if (!(readAccessible(calleeContextLastMMUPage, idxCalleeContextPageInLastMMUPage)))
		return FAIL_UNAVAILABLE_TARGET_CTX;
	vaddr_t calleeContextEndVAddr = getNthVAddrFrom(calleeContextVAddr, contextSizeMinusOne);
	if (!(calleeContextVAddr < calleeContextEndVAddr))
		return FAIL_UNAVAILABLE_TARGET_CTX;
	page_t calleeContextEndLastMMUPage = getTableAddr(calleePageDir, calleeContextEndVAddr, nbL);
	if (calleeContextEndLastMMUPage == 0)
		return FAIL_UNAVAILABLE_TARGET_CTX;
	unsigned idxCalleeContextEndPageInLastMMUPage = getIndexOfAddr(calleeContextEndVAddr, fstLevel);
	if (!(readPresent(calleeContextEndLastMMUPage, idxCalleeContextEndPageInLastMMUPage)))
		return FAIL_UNAVAILABLE_TARGET_CTX;
	if (!(readAccessible(calleeContextEndLastMMUPage, idxCalleeContextEndPageInLastMMUPage)))
		return FAIL_UNAVAILABLE_TARGET_CTX;

	user_ctx_t *targetContext = (user_ctx_t *)calleeContextVAddr;
	// check if we should save the caller context
	if (!(callerContextSaveVAddr == 0)) {
		return saveSourcePartCtxCont(calleePartDesc, calleePageDir, callerPageDir, callerContextSaveVAddr, nbL, flagsOnYield, flagsOnWake, callerInterruptedContext, targetContext);
	} else {
		return switchContextCont(calleePartDesc, calleePageDir, flagsOnYield, targetContext);
	}
}

yield_checks_t saveSourcePartCtxCont(page_t calleePartDesc,
				     page_t calleePageDir,
				     page_t callerPageDir,
				     vaddr_t callerContextSaveVAddr,
				     unsigned nbL,
				     int_mask_t flagsOnYield,
				     int_mask_t flagsOnWake,
				     user_ctx_t *callerInterruptedContext,
				     user_ctx_t *targetContext)
{
	page_t callerCtxLastMMUPage = getTableAddr(callerPageDir, callerContextSaveVAddr, nbL);
	if (callerCtxLastMMUPage == 0)
		return FAIL_CALLER_CONTEXT_SAVE;
	unsigned idxCurrentCtxLastMMUPage = getIndexOfAddr(callerContextSaveVAddr, fstLevel);
	if (!(readPresent(callerCtxLastMMUPage, idxCurrentCtxLastMMUPage)))
		return FAIL_CALLER_CONTEXT_SAVE;
	if (!(readAccessible(callerCtxLastMMUPage, idxCurrentCtxLastMMUPage)))
		return FAIL_CALLER_CONTEXT_SAVE;
	vaddr_t callerContextEndSaveVAddr = getNthVAddrFrom(callerContextSaveVAddr, contextSizeMinusOne);
	if (!(callerContextSaveVAddr < callerContextEndSaveVAddr))
		return FAIL_CALLER_CONTEXT_SAVE;
	page_t callerCtxEndLastMMUPage = getTableAddr(callerPageDir, callerContextEndSaveVAddr, nbL);
	if (callerCtxEndLastMMUPage == 0)
		return FAIL_CALLER_CONTEXT_SAVE;
	unsigned idxCallerCtxEndInLastMMUPage = getIndexOfAddr(callerContextEndSaveVAddr, fstLevel);
	if (!(readPresent(callerCtxEndLastMMUPage, idxCallerCtxEndInLastMMUPage)))
		return FAIL_CALLER_CONTEXT_SAVE;
	if (!(readAccessible(callerCtxEndLastMMUPage, idxCallerCtxEndInLastMMUPage)))
		return FAIL_CALLER_CONTEXT_SAVE;
	writeContext(callerInterruptedContext, callerContextSaveVAddr, flagsOnWake);
	return switchContextCont(calleePartDesc, calleePageDir, flagsOnYield, targetContext);
}

void updateCurPartAndActivate(page_t calleePartDesc, page_t calleePageDir) {
	DEBUG(CRITICAL, "Updating current partition to %x\n", calleePartDesc);
	updateCurPartition(calleePartDesc);
	DEBUG(CRITICAL, "Activating MMU for the current partition (page directory %x)\n", calleePageDir);
	activate(calleePageDir);
}

yield_checks_t switchContextCont (page_t calleePartDesc,
				  page_t calleePageDir,
				  int_mask_t flagsOnYield,
				  user_ctx_t *ctx) {
	DEBUG(INFO, "Applying interrupt state from the parameters : %d\n", flagsOnYield);
	kernel_set_int_state(flagsOnYield);
	updateCurPartAndActivate(calleePartDesc, calleePageDir);
	DEBUG(INFO, "Applying interrupt state from the restored context : %d\n", ctx->pipflags);
	kernel_set_int_state(ctx->pipflags);
	// special case of the root partition that can choose to be CLI'd or not
	unsigned enforce_interrupts = 1;
	if (calleePartDesc == getRootPartition() && ctx->pipflags == 0) {
		enforce_interrupts = 0;
	}
	DEBUG(CRITICAL, "Loading context into registers...\n");
	loadContext(ctx, enforce_interrupts);
	return SUCCESS;
}

/* copies or pushes SS, ESP, EFLAGS, CS, EIP from the given context to the stack
 * and then executes an `iret` in order to go back to userland
 * see x86int.h for infos related to user_ctx_t struct */
void loadContext(user_ctx_t *ctx, unsigned enforce_interrupts) {
	asm(
	    /* retrieve user_ctx_t * in EAX register */
	    "mov %0, %%eax;"
	    "mov %1, %%ecx;"

	    /* push user ss */
	    "push %2;"

	    /* push user esp */
	    "push 0x18(%%eax);"

	    /* push eflags */
	    "push 0x8(%%eax);"

	    /* fix eflags to prevent potential security issues */
	    "orl %3, (%%esp);"
	    /* -- skip enable interrupts depending on parameter */
	    "jcxz 1f;" /* <------+ */
	    "orl %4, (%%esp);"/* | */
	    "1:;" /* <-----------+ */

	    "andl %5, (%%esp);"

	    /* push cs */
	    "push %6;"

	    /* push eip */
	    "push (%%eax);"

	    /* restore general purpose registers */
	    /* maybe we could `popad` but it seems complicated */
	    /* restore EDI */
	    "mov  0xC(%%eax), %%edi;"

	    /* restore ESI */
	    "mov 0x10(%%eax), %%esi;"

	    /* restore EBP */
	    "mov 0x14(%%eax), %%ebp;"

	    /* skipped ESP which was already pushed */

	    /* restore EBX */
	    "mov 0x1C(%%eax), %%ebx;"

	    /* restore EDX */
	    "mov 0x20(%%eax), %%edx;"

	    /* restore ECX */
	    "mov 0x24(%%eax), %%ecx;"

	    /* restore EAX */
	    "mov 0x28(%%eax), %%eax;"

	    /* switch to userland */
	    "iret;"

	    /* output operands */
	    :
	    /* input operands */
	    : "m"(ctx),
	      "m"(enforce_interrupts),
	      "i"(USER_DATA_SEGMENT_SELECTOR | USER_RING), /* TODO Correct ? Check RPL */
	    /* eflags related constants */
	    /* set bit 1 : always 1 */
	      "i"(0x2),
	    /* set bit conditional :
	     * 	       9 : interrupt enable
	     * controlled by parameter */
	      "i"(0x200),
	    /* unset bit 8 : trap flag
	     * 	     12-13 : I/O privilege level
	     *       14-32 : various system flags */
	      "i"(0xEFF),
	      "i"(USER_CODE_SEGMENT_SELECTOR | USER_RING)  /* TODO Correct ? Check RPL */
	    /* registers changed during inline assembly */
	    :
	);
}
