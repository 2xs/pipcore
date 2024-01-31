/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2024)                */
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

#include "coproc.h"
#include "fault.h"

.extern ial_fault_handler
.extern ial_irq_handler
.extern ial_fiq_handler

#define CTX_SIZE		(4+16*4)
#define CTX_PC_OF	(CTX_SIZE-4)

.section .text

/* ial_resume_ctx: restore the given context and jump to userland
 * r0: arm_ctx_t context structure
 * Preconditions:
 *	- Partition must be activated
 *	- context must be mapped in child
 *	- context->spsr must have been validated by kernel */
.global ial_resume_ctx
ial_resume_ctx:
	/* FIXME: this way to restore SVC stack looks kind of crude */
	ldr sp, =svc_stack   @ Reset SVC stack

	/* Restore spsr */
	ldmia r0!, {r1}
	msr spsr_cxsf, r1    @ restore user cpsr

	/* Restore gp registers registers and go back to userland */
	ldm r0, {sp, lr}^		@ restore user banked registers
	add r0, r0, #8
	ldm r0, {r0-r12, pc}^		@ restore rest

/* Entry stub for hw interrupts. Switch back to SVC & push the current context on the stack */
.macro exception_entry, mode, pc_offset
	@ save user spsr, {sp, lr}^, r0, pc in scratch stack
	str r0, [sp, #12]			@ store orig r0
	sub r0, lr, #\pc_offset		@ adjust return PC
	str r0, [sp, #16]			@ store orig pc
	add r0, sp, #4
	stm r0, {sp, lr}^			@ store orig sp, lr
	mrs r0, spsr
	str r0, [sp]				@ store orig cpsr

	mrs r0, cpsr				@ prepare for svc
	eor r0, #(\mode ^ ARM_MODE_SVC)
	msr spsr_cxsf, r0

	mov r0, sp					@ keep pointer to scratch registers
	subs pc, pc, #0				@ switch to svc mode

	sub sp, sp, #4				@ make room for pc
	stmfd sp!, {r1-r12}			@ save gp registers
	ldm r0, {r0-r4}				@ restore spsr, sp, lr, r0, pc from prev stack
	stmfd sp!, {r0-r3}
	str r4, [sp, #CTX_PC_OF]
	mov r0, sp					@ points r0 to the full current arm_ctx_t
.endm

.macro exception_handler, name, pc_offset, mode, num
.global ial_\name\()_handler
ial_\name\()_handler:
	exception_entry \mode, \pc_offset
	mov r1, #\num
	b ial_fault_handler
.endm

exception_handler data_abort	,	8,	ARM_MODE_ABORT, FAULT_DATA_ABORT
exception_handler prefetch_abort,	4,	ARM_MODE_ABORT, FAULT_PREFETCH_ABORT
exception_handler undef			,	0,	ARM_MODE_UNDEF, FAULT_UNDEF

.global ial_irq_handler_s
ial_irq_handler_s:
	exception_entry ARM_MODE_IRQ,	4
	b ial_irq_handler

.global ial_fiq_handler_s
ial_fiq_handler_s:
	exception_entry ARM_MODE_FIQ,	4
	b ial_fiq_handler
