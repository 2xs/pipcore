#include "gdt_entrypoints_glue.h"
#include "maldefines.h"
#include "x86int.h"
#include "Services.h"

yield_checks yieldGlue(gate_ctx_t *gate_ctx,
                       vaddr calleePartDescVAddr,
                       userValue userTargetInterrupt,
                       userValue userCallerContextSaveIndex,
                       interruptMask flagsOnYield,
                       interruptMask flagsOnWake){
	user_ctx_t user_ctx;
	user_ctx.regs = gate_ctx->regs;
	user_ctx.regs.esp = gate_ctx->useresp;
	user_ctx.eip = gate_ctx->eip;
	user_ctx.eflags = gate_ctx->eflags;
	user_ctx.valid = 1;

	return checkIntLevelCont(calleePartDescVAddr, userTargetInterrupt, userCallerContextSaveIndex, flagsOnYield, flagsOnWake, &user_ctx);
}
