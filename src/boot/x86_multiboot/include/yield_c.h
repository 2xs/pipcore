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
	SUCCESS,
	FAIL_INVALID_INT_LEVEL,
	FAIL_INVALID_CTX_SAVE_INDEX,
	FAIL_ROOT_CALLER,
	FAIL_INVALID_CHILD,
	FAIL_UNAVAILABLE_TARGET_VIDT,
	FAIL_UNAVAILABLE_CALLER_VIDT,
	FAIL_MASKED_INTERRUPT,
	FAIL_UNAVAILABLE_TARGET_CTX,
	FAIL_CALLER_CONTEXT_SAVE
} yield_checks_t;


#define contextSizeMinusOne sizeof(user_ctx_t)

yield_checks_t checkIntLevelCont(vaddr_t calleePartDescVAddr, uservalue_t userTargetInterrupt, uservalue_t userCallerContextSaveIndex, int_mask_t flagsOnYield, int_mask_t flagsOnWake, user_ctx_t *callerInterruptedContext);

yield_checks_t getParentPartDescCont(page_t callerPartDesc, page_t callerPageDir, unsigned targetInterrupt, unsigned callerContextSaveIndex, unsigned nbL, int_mask_t flagsOnYield, int_mask_t flagsOnWake, user_ctx_t *callerInterruptedContext);

yield_checks_t getSourcePartVidtCont(page_t calleePartDesc, page_t callerPageDir, unsigned targetInterrupt, unsigned callerContextSaveIndex, unsigned nbL, int_mask_t flagsOnYield, int_mask_t flagsOnWake, user_ctx_t *callerInterruptedContext);

yield_checks_t switchContextCont(page_t callerVidt, int_mask_t flagsOnYield, page_t calleePartDesc, page_t calleePageDir, user_ctx_t *ctx);

#endif
