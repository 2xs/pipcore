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

.extern kernel_start
.extern svc_entrypoint
.extern ial_undef_handler
.extern ial_prefetch_abort_handler
.extern ial_data_abort_handler
.extern ial_irq_handler_s
.extern ial_fiq_handler_s

.set MASK_BITS, CPSR_FIQ|CPSR_IRQ|CPSR_A

.code 32
.section .text.start
.global vector_table
vector_table:
	ldr pc, =boot_reset
	ldr pc, =ial_undef_handler
	ldr pc, =svc_entrypoint
	ldr pc, =ial_prefetch_abort_handler
	ldr pc, =ial_data_abort_handler
	ldr pc, =boot_reserved
	ldr pc, =ial_irq_handler_s
	ldr pc, =ial_fiq_handler_s

boot_reserved:
	b .

boot_reset:
	READ_CP_ASM(r5, ID_MPIDR)
	dsb
	ands r5, #0xff
	beq .core0
1:
	wfe
	b 1b

.core0:
	/* Go supervisor, interrupt masked */
	ldr r5, =(ARM_MODE_SVC|CPSR_FIQ|CPSR_IRQ)
	msr cpsr, r5

	ldr r5, =vector_table               @ Setup VBAR
	WRITE_CP_ASM(r5, ID_VBAR)

	ldr sp, =svc_stack                  @ Setup SVC stack

	ldr r5, =(ARM_MODE_ABORT|MASK_BITS) @ Set Abort stack
	msr cpsr_fc, r5
	ldr sp, =abort_stack

	ldr r5, =(ARM_MODE_UNDEF|MASK_BITS) @ Set undef stack
	msr cpsr_fc, r5
	ldr sp, =undef_stack

	ldr r5, =(ARM_MODE_IRQ|MASK_BITS)   @ Set irq stack
	msr cpsr_fc, r5
	ldr sp, =irq_stack

	ldr r5, =(ARM_MODE_FIQ|MASK_BITS)   @ Set fiq stack
	msr cpsr_fc, r5
	ldr sp, =fiq_stack

	ldr r5, =(ARM_MODE_SVC|MASK_BITS)   @ back to SVC
	msr cpsr_fc, r5

	blx kernel_start
loop:
	wfe
	b loop

/* TODO: right stacks */
.section .bss.kstack
.align(4)
stack_base:
.org .+0x1000
.global svc_stack
svc_stack:
/* Fake stacks for 5 registers */
abort_stack:
.org .+20
undef_stack:
.org .+20
irq_stack:
.org .+20
fiq_stack:
.org .+20
