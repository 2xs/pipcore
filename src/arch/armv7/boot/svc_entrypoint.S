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

#define GATE_CTX_T_SIZE (4+16*4)

.global svc_entrypoint

svc_entrypoint:
	push       {r0-r12,lr}

	ldr        r0, [lr,#-4]         /* Calculate address of SVC instruction and load it into R0 */
	bic        r0, r0, #0xFF000000  /* Mask off top 8 bits of instruction to give SVC number */

	stmfd   sp, {sp, lr}^           /* Save banked registers, then manually adjust */
	sub     sp, #8                  /* sp because write-back is unpredictable here */

	mrs     r12, SPSR               /* Writes the contents of the CP15 coprocessor register SCTLR into R12 */
	stmfd   sp!, {r12}              /* Save the previous spsr */
	mov     r1, sp                  /* Points r1 to the full current gate_ctx_t */

	bl      c_svc_handler           /* Call handler with r0 pointing on the context */

	mov     r0, sp                  /* Now resume the context, assuming r0 has been */
                                        /* updated with the syscall return value */
	add     sp, #GATE_CTX_T_SIZE    /* Adjust the stack */
	b       ial_resume_ctx          /* Return to user context */
