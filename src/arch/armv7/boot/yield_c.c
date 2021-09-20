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
#include "coproc.h"

void ial_resume_ctx(user_ctx_t* context) __attribute__((noreturn));

vaddr_t getVidtVAddr() {
	return 0x3FFFF000;
}

int_mask_t readInterruptMask(page_t vidt) { //unimplemented
	(void) vidt;
	return 0u;
}

bool isInterruptMasked(int_mask_t int_mask, uint32_t index) { //unimplemented
	(void) int_mask; (void) index;
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
	userland_save_ptr->spsr       = ctx->spsr;
	userland_save_ptr->reg[ 0]    = ctx->reg[ 0];
	userland_save_ptr->reg[ 1]    = ctx->reg[ 1];
	userland_save_ptr->reg[ 2]    = ctx->reg[ 2];
	userland_save_ptr->reg[ 3]    = ctx->reg[ 3];
	userland_save_ptr->reg[ 4]    = ctx->reg[ 4];
	userland_save_ptr->reg[ 5]    = ctx->reg[ 5];
	userland_save_ptr->reg[ 6]    = ctx->reg[ 6];
	userland_save_ptr->reg[ 7]    = ctx->reg[ 7];
	userland_save_ptr->reg[ 8]    = ctx->reg[ 8];
	userland_save_ptr->reg[ 9]    = ctx->reg[ 9];
	userland_save_ptr->reg[10]    = ctx->reg[10];
	userland_save_ptr->reg[11]    = ctx->reg[11];
	userland_save_ptr->reg[12]    = ctx->reg[12];
	userland_save_ptr->reg[13]    = ctx->reg[13];
	userland_save_ptr->reg[14]    = ctx->reg[14];
	userland_save_ptr->reg[15]    = ctx->reg[15];
	userland_save_ptr->pipflags   = flagsOnWake;
	userland_save_ptr->valid      = 1;
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
	user_ctx.spsr	 = gate_ctx->spsr;
	user_ctx.reg[ 0] = gate_ctx->reg[ 0];
	user_ctx.reg[ 1] = gate_ctx->reg[ 1];
	user_ctx.reg[ 2] = gate_ctx->reg[ 2];
	user_ctx.reg[ 3] = gate_ctx->reg[ 3];
	user_ctx.reg[ 4] = gate_ctx->reg[ 4];
	user_ctx.reg[ 5] = gate_ctx->reg[ 5];
	user_ctx.reg[ 6] = gate_ctx->reg[ 6];
	user_ctx.reg[ 7] = gate_ctx->reg[ 7];
	user_ctx.reg[ 8] = gate_ctx->reg[ 8];
	user_ctx.reg[ 9] = gate_ctx->reg[ 9];
	user_ctx.reg[10] = gate_ctx->reg[10];
	user_ctx.reg[11] = gate_ctx->reg[11];
	user_ctx.reg[12] = gate_ctx->reg[12];
	user_ctx.reg[13] = gate_ctx->reg[13];
	user_ctx.reg[14] = gate_ctx->reg[14];
	user_ctx.reg[15] = gate_ctx->reg[15];
	user_ctx.valid	 = 1;

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
	DEBUG(INFO, "Updating current partition to %x\n", calleePartDesc);
	updateCurPartition(calleePartDesc);
	DEBUG(INFO, "Activating MMU for the current partition (page directory %x)\n", calleePageDir);
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
	DEBUG(INFO, "Loading context into registers...\n");
	loadContext(ctx, enforce_interrupts);
	return SUCCESS;
}

void loadContext(user_ctx_t *ctx, unsigned enforce_interrupts) {

	/* The SPSR value MUST be validated before restoring it
	 * so clear the (A)synchronous abort disable bit, the
	 * (I)nterrupt disable bit, the (F)ast interrupt disable
	 * bit and the (M)ode field
	 */
	ctx->spsr &= ~(CPSR_A | CPSR_IRQ | CPSR_FIQ | 0x1f);

	/* Set the (M)ode field to User, the (A)synchronous
	 * abort disable bit and the (F)ast interrupt disable
	 * bit
	 */
	ctx->spsr |= ARM_MODE_USER | CPSR_A | CPSR_FIQ;

	/* Set the (I)nterrupt disable bit if and only if
	 * enforce_interrupts is equal to zero. This means that the
	 * root partition has requested to be CLI'd
	 */
	if (enforce_interrupts == 0) {
		ctx->spsr |= CPSR_IRQ;
	}

	/* Restore the validated partition context and transfer the
	 * execution flow
	 */
	ial_resume_ctx(ctx);

	/* Should never be reached */
	for (;;);
}
