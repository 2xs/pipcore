#include "yield_c.h"


vaddr_t getVidtVAddr() {
	return 0xFFFFF000;
}

int_mask_t readInterruptMask(page_t vidt) {
	return 0u;
}

bool isInterruptMasked(int_mask_t int_mask, uint32_t index) {
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
	return;
}

void loadContext(user_ctx_t *ctx);

yield_checks_t checkCtxSaveIdxCont(vaddr_t calleePartDescVAddr, unsigned targetInterrupt, uservalue_t userCallerContextSaveIndex, int_mask_t flagsOnYield, int_mask_t flagsOnWake, user_ctx_t *callerInterruptedContext);

yield_checks_t getChildPartDescCont(page_t callerPartDesc, page_t callerPageDir, vaddr_t calleePartDescVAddr, unsigned targetInterrupt, unsigned callerContextSaveIndex, unsigned nbL, int_mask_t flagsOnYield, int_mask_t flagsOnWake, user_ctx_t *callerInterruptedContext);

yield_checks_t getParentPartDescCont(page_t callerPartDesc, page_t callerPageDir, unsigned targetInterrupt, unsigned callerContextSaveIndex, unsigned nbL, int_mask_t flagsOnYield, int_mask_t flagsOnWake, user_ctx_t *callerInterruptedContext);

yield_checks_t getTargetPartVidtCont(page_t calleePartDesc, page_t callerPageDir, unsigned targetInterrupt, unsigned callerContextSaveIndex, unsigned nbL, int_mask_t flagsOnYield, int_mask_t flagsOnWake, user_ctx_t *callerInterruptedContext);

yield_checks_t checkIntMaskCont(page_t calleePartDesc, page_t calleePageDir, page_t calleeVidt, page_t callerPageDir, vaddr_t vidtVaddr, unsigned targetInterrupt, unsigned callerContextSaveIndex, unsigned nbL, unsigned idxVidtInLastMMUPage, int_mask_t flagsOnYield, int_mask_t flagsOnWake, user_ctx_t *callerInterruptedContext);

yield_checks_t getTargetPartCtxCont(page_t calleePartDesc, page_t calleePageDir, page_t calleeVidt, page_t callerPageDir, vaddr_t vidtVaddr, unsigned targetInterrupt, unsigned callerContextSaveIndex, unsigned nbL, unsigned idxVidtInLastMMUPage, int_mask_t flagsOnYield, int_mask_t flagsOnWake,  user_ctx_t *callerInterruptedContext);

yield_checks_t getSourcePartVidtCont(page_t calleePartDesc, page_t calleePageDir, page_t callerPageDir, vaddr_t vidtVaddr, unsigned callerContextSaveIndex, unsigned nbL, unsigned idxVidtInLastMMUPage, int_mask_t flagsOnYield, int_mask_t flagsOnWake, user_ctx_t *callerInterruptedContext, user_ctx_t *targetContext);

yield_checks_t saveSourcePartCtxCont(page_t calleePartDesc, page_t calleePageDir, page_t callerPageDir, page_t callerVidt, vaddr_t callerContextSaveVAddr, unsigned nbL, int_mask_t flagsOnYield, int_mask_t flagsOnWake, user_ctx_t *callerInterruptedContext, user_ctx_t *targetContext);

yield_checks_t switchContextCont(page_t callerVidt, int_mask_t flagsOnYield, page_t calleePartDesc, page_t calleePageDir, user_ctx_t *ctx);

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
	return getTargetPartVidtCont(calleePartDesc, callerPageDir, targetInterrupt, callerContextSaveIndex, nbL, flagsOnYield, flagsOnWake, callerInterruptedContext);
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
	return getTargetPartVidtCont(calleePartDesc, callerPageDir, targetInterrupt, callerContextSaveIndex, nbL, flagsOnYield, flagsOnWake, callerInterruptedContext);
}



yield_checks_t getTargetPartVidtCont(page_t calleePartDesc,
				     page_t callerPageDir,
				     unsigned targetInterrupt,
				     unsigned callerContextSaveIndex,
				     unsigned nbL,
				     int_mask_t flagsOnYield,
				     int_mask_t flagsOnWake,
				     user_ctx_t *callerInterruptedContext)
{
	page_t calleePageDir = getPd(calleePartDesc);

	//retrieve callee vidt
	vaddr_t vidtVaddr = getVidtVAddr();
	page_t calleeVidtLastMMUPage = getTableAddr(calleePageDir, vidtVaddr, nbL);
	unsigned idxVidtInLastMMUPage = getIndexOfAddr(vidtVaddr, fstLevel);
	if (calleeVidtLastMMUPage == 0)
		return FAIL_UNAVAILABLE_TARGET_VIDT;
	if (!(readPresent(calleeVidtLastMMUPage, idxVidtInLastMMUPage)))
		return FAIL_UNAVAILABLE_TARGET_VIDT;
	if (!(readAccessible(calleeVidtLastMMUPage, idxVidtInLastMMUPage)))
		return FAIL_UNAVAILABLE_TARGET_VIDT;
	page_t calleeVidt = readPhyEntry(calleeVidtLastMMUPage, idxVidtInLastMMUPage);
	return checkIntMaskCont(calleePartDesc, calleePageDir, calleeVidt, callerPageDir, vidtVaddr, targetInterrupt, callerContextSaveIndex, nbL, idxVidtInLastMMUPage, flagsOnYield, flagsOnWake, callerInterruptedContext);
}

yield_checks_t checkIntMaskCont(page_t calleePartDesc,
				page_t calleePageDir,
				page_t calleeVidt,
				page_t callerPageDir,
				vaddr_t vidtVaddr,
				unsigned targetInterrupt,
				unsigned callerContextSaveIndex,
				unsigned nbL,
				unsigned idxVidtInLastMMUPage,
				int_mask_t flagsOnYield,
				int_mask_t flagsOnWake,
				user_ctx_t *callerInterruptedContext)
{
	//check if callee accepts to recieve such interrupts
	int_mask_t calleeInterruptMask = readInterruptMask(calleeVidt);
	if (isInterruptMasked(calleeInterruptMask, targetInterrupt))
		return FAIL_MASKED_INTERRUPT;
	return getTargetPartCtxCont(calleePartDesc, calleePageDir, calleeVidt, callerPageDir, vidtVaddr, targetInterrupt, callerContextSaveIndex, nbL, idxVidtInLastMMUPage, flagsOnYield, flagsOnWake, callerInterruptedContext);
}

yield_checks_t getTargetPartCtxCont(page_t calleePartDesc,
				    page_t calleePageDir,
				    page_t calleeVidt,
				    page_t callerPageDir,
				    vaddr_t vidtVaddr,
				    unsigned callerContextSaveIndex,
				    unsigned targetInterrupt,
				    unsigned nbL,
				    unsigned idxVidtInLastMMUPage,
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
	return getSourcePartVidtCont(calleePartDesc, calleePageDir, callerPageDir, vidtVaddr, callerContextSaveIndex, nbL, idxVidtInLastMMUPage, flagsOnYield, flagsOnWake, callerInterruptedContext, (user_ctx_t *) calleeContextVAddr);
}

yield_checks_t getSourcePartVidtCont(page_t calleePartDesc,
				     page_t calleePageDir,
				     page_t callerPageDir,
				     vaddr_t vidtVaddr,
				     unsigned callerContextSaveIndex,
				     unsigned nbL,
				     unsigned idxVidtInLastMMUPage,
				     int_mask_t flagsOnYield,
				     int_mask_t flagsOnWake,
				     user_ctx_t *callerInterruptedContext,
				     user_ctx_t *targetContext)
{
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
	if (!(callerContextSaveVAddr == 0)) {
		return saveSourcePartCtxCont(calleePartDesc, calleePageDir, callerPageDir, callerVidt, callerContextSaveVAddr, nbL, flagsOnYield, flagsOnWake, callerInterruptedContext, targetContext);
	} else {
		return switchContextCont(calleePartDesc, calleePageDir, callerVidt, flagsOnYield, targetContext);
	}
}

yield_checks_t saveSourcePartCtxCont(page_t calleePartDesc,
				     page_t calleePageDir,
				     page_t callerPageDir,
				     page_t callerVidt,
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
	return switchContextCont(calleePartDesc, calleePageDir, callerVidt, flagsOnYield, targetContext);
}

void updateCurPartAndActivate(page_t calleePartDesc, page_t calleePageDir) {
	DEBUG(CRITICAL, "Updating current partition to %x\n", calleePartDesc);
	updateCurPartition(calleePartDesc);
	DEBUG(CRITICAL, "Activating MMU for the current partition (page directory %x)\n", calleePageDir);
	activate(calleePageDir);
}

yield_checks_t switchContextCont (page_t calleePartDesc,
				  page_t calleePageDir,
				  page_t callerVidt,
				  int_mask_t flagsOnYield,
				  user_ctx_t *ctx) {
	updateCurPartAndActivate(calleePartDesc, calleePageDir);
	DEBUG(CRITICAL, "Loading context into registers...\n");
	loadContext(ctx);
	return SUCCESS;
}

/* copies or pushes SS, ESP, EFLAGS, CS, EIP from the given context to the stack
 * and then executes an `iret` in order to go back to userland
 * see x86int.h for infos related to user_ctx_t struct */
void loadContext(user_ctx_t *ctx) {
	asm(
	    /* retrieve user_ctx_t * in EAX register */
	    "mov %0, %%eax;"

	    /* retrieve virtual flags from context and writes them in VIDT */
	    /* TODO Fix this when pipflags are implemented */ 
	    // "mov 0x4(%%eax), %%ebx;"
	    // "mov %%exb, (0xfffffffc);"

	    /* push user ss */
	    "push %1;"

	    /* push user esp */
	    "push 0x18(%%eax);"

	    /* push eflags */
	    "push 0x8(%%eax);"

	    /* push cs */
	    "push %2;"

	    /* push eip */
	    "push (%%eax);"

	    /* restore general purpose registers */
	    /* maybe we could `popad` but it seems complicated */
	    /* restore EDI */
	    "mov  0xc(%%eax), %%edi;"

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
	      "i"(USER_DATA_SEGMENT_SELECTOR | USER_RING), /* TODO Correct ? Check RPL */
	      "i"(USER_CODE_SEGMENT_SELECTOR | USER_RING)  /* TODO Correct ? Check RPL */
	    /* registers changed during inline assembly */
	    :
	);
}
