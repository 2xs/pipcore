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

#include "svc.h"
#include "stdio.h"
#include "maldefines.h"
#include "debug.h"

/* Prototypes of control flow transfer services entrypoints */
#include "pip_interrupt_calls.h"
#include "Services.h"

yield_checks yieldGlue(gate_ctx_t *gate_ctx,
                       vaddr calleePartDescVAddr,
                       userValue userTargetInterrupt,
                       userValue userCallerContextSaveIndex,
                       interruptMask flagsOnYield,
                       interruptMask flagsOnWake){
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

	return checkIntLevelCont(calleePartDescVAddr, userTargetInterrupt, userCallerContextSaveIndex,
		flagsOnYield, flagsOnWake, &user_ctx);
}

void c_svc_handler(uint32_t svc_number, gate_ctx_t *ctx)
{
	uint32_t result;

	switch (svc_number)
	{
		case SVC_CREATEPARTITION:
			result = createPartition(
				ctx->reg[CTX_R0],
				ctx->reg[CTX_R1],
				ctx->reg[CTX_R2],
				ctx->reg[CTX_R3],
				ctx->reg[CTX_R4]
			);
			break;

		case SVC_COUNTTOMAP:
			result = countToMap(
				ctx->reg[CTX_R0],
				ctx->reg[CTX_R1]
			);
			break;

		case SVC_PREPARE:
			result = prepare(
				ctx->reg[CTX_R0],
				ctx->reg[CTX_R1],
				ctx->reg[CTX_R2]
			);
			break;

		case SVC_ADDVADDR:
			result = addVAddr(
				ctx->reg[CTX_R0],
				ctx->reg[CTX_R1],
				ctx->reg[CTX_R2],
				ctx->reg[CTX_R3],
				ctx->reg[CTX_R4],
				ctx->reg[CTX_R5]
			);
			break;

		case SVC_GET_INT_STATE:
			result = get_int_state(
				ctx->reg[CTX_R0]
			);
			break;

		case SVC_SET_INT_STATE:
			set_int_state(
				ctx,
				ctx->reg[CTX_R0]
			);
			result = 1;
			break;

		case SVC_REMOVEVADDR:
			result = removeVAddr(
				ctx->reg[CTX_R0],
				ctx->reg[CTX_R1]
			);
			break;

		case SVC_MAPPEDINCHILD:
			result = mappedInChild(
				ctx->reg[CTX_R0]
			);
			break;

		case SVC_DELETEPARTITION:
			result = deletePartition(
				ctx->reg[CTX_R0]
			);
			break;

		case SVC_COLLECT:
			result = collect(
				ctx->reg[CTX_R0],
				ctx->reg[CTX_R1]
			);
			break;

		case SVC_YIELD:
			result = yieldGlue(
				ctx,
				ctx->reg[CTX_R0],
				ctx->reg[CTX_R1],
				ctx->reg[CTX_R2],
				ctx->reg[CTX_R3],
				ctx->reg[CTX_R4]
			);
			break;

		case SVC_PUTCHAR:
			result = putchar(
				ctx->reg[CTX_R0]
			);
			break;

		default:
			DEBUG(WARNING, "Invalid SVC number: %d\n", svc_number);
			result = SVC_INVALID_NUMBER;
	}

	ctx->reg[CTX_R0] = result;
}
