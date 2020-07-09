#ifndef YIELD_C_H
#define YIELD_C_H

#include "debug.h"
#include "x86int.h"
#include "maldefines.h"
#include "Internal.h"
#include "segment_selectors.h"

typedef uint32_t vaddr_t;
typedef uint32_t page_t;
typedef uint32_t uservalue_t;
typedef uint32_t int_mask_t;
typedef enum yield_checks_e {
	SUCCESS=0,
	FAIL_INVALID_INT_LEVEL=1,
	FAIL_INVALID_CTX_SAVE_INDEX=2,
	FAIL_ROOT_CALLER=3,
	FAIL_INVALID_CHILD=4,
	FAIL_UNAVAILABLE_TARGET_VIDT=5,
	FAIL_UNAVAILABLE_CALLER_VIDT=6,
	FAIL_MASKED_INTERRUPT=7,
	FAIL_UNAVAILABLE_TARGET_CTX=8,
	FAIL_CALLER_CONTEXT_SAVE=9
} yield_checks_t;

vaddr_t getVidtVAddr();

#define contextSizeMinusOne sizeof(user_ctx_t)

yield_checks_t checkIntLevelCont(vaddr_t calleePartDescVAddr, uservalue_t userTargetInterrupt, uservalue_t userCallerContextSaveIndex, int_mask_t flagsOnYield, int_mask_t flagsOnWake, user_ctx_t *callerInterruptedContext);

yield_checks_t getParentPartDescCont(page_t callerPartDesc, page_t callerPageDir, unsigned targetInterrupt, unsigned callerContextSaveIndex, unsigned nbL, int_mask_t flagsOnYield, int_mask_t flagsOnWake, user_ctx_t *callerInterruptedContext);

yield_checks_t getSourcePartVidtCont(page_t calleePartDesc, page_t callerPageDir, unsigned targetInterrupt, unsigned callerContextSaveIndex, unsigned nbL, int_mask_t flagsOnYield, int_mask_t flagsOnWake, user_ctx_t *callerInterruptedContext);

yield_checks_t getTargetPartVidtCont(page_t calleePartDesc, page_t callerPageDir, page_t callerVidt,
vaddr_t vidtVaddr, vaddr_t callerContextSaveVAddr, unsigned targetInterrupt, unsigned nbL, unsigned idxVidtInLastMMUPage, int_mask_t flagsOnYield, int_mask_t flagsOnWake, user_ctx_t *callerInterruptedContext);

yield_checks_t switchContextCont(page_t callerVidt, int_mask_t flagsOnYield, page_t calleePartDesc, page_t calleePageDir, user_ctx_t *ctx);

#endif
