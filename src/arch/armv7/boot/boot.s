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

.equ MODE_FIQ, 0x11
.equ MODE_IRQ, 0x12
.equ MODE_SVC, 0x13
.equ MODE_MON, 0x16
.equ MODE_ABT, 0x17
.equ MODE_UND, 0x1b
.equ MODE_SYS, 0x1f

.global start
.extern main

.section .text.vector_table

start:
vector_table_base_address:
    b       reset_handler
    b       .
    b       .
    b       .
    b       .
    nop     // Reserved vector
    b       .
    b       .

.section .text.reset_handler

/*
 * This execption occurs when the reset button is pressed.
 */

reset_handler:

     /*
      * Only core 0 performs initialization. Other cores branch to idle.
      */

     mrc    p15, 0, r1, c0, c0, 5   // Read Multiprocessor Affinity Register
     and    r1, r1, #0x3            // Extract CPU ID bits
     cmp    r1, #0                  // Are we on core 0?
     bne    idle                    // If not, branch to idle

core0:

    /*
     * Initializing the Vector Base Address Register (VBAR).
     */

    ldr     r1, =vector_table_base_address
    mcr     p15, 0, r1, c12, c0, 0

    /*
     * Initializing the stack pointer registers.
     */

    msr     cpsr_c, MODE_SVC
    ldr     sp, =_svc_stack_base

    /*
     * Initializing bss segment.
     */

    mov     r0, #0
    ldr     r1, =_bss_start
    ldr     r2, =_bss_end

clear_bss:
    cmp     r1, r2
    strlt   r0, [r1], #4
    blt     clear_bss

    /*
     * Branch to C main.
     */

    bl      main

idle:
    wfi
    b       idle
