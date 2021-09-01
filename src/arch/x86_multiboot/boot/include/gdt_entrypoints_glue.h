#ifndef __GDT_ENTRYPOINTS_GLUE_H__
#define __GDT_ENTRYPOINTS_GLUE_H__

#include "maldefines.h"
#include "x86int.h"

yield_checks yieldGlue(gate_ctx_t *gate_ctx,
                       vaddr calleePartDescVAddr,
                       userValue userTargetInterrupt,
                       userValue userCallerContextSaveIndex,
                       interruptMask flagsOnYield,
                       interruptMask flagsOnWake);

#endif
