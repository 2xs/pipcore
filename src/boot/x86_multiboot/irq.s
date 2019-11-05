;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  © Université Lille 1, The Pip Development Team (2015-2018)                 ;
;                                                                             ;
;  This software is a computer program whose purpose is to run a minimal,     ;
;  hypervisor relying on proven properties such as memory isolation.          ;
;                                                                             ;
;  This software is governed by the CeCILL license under French law and       ;
;  abiding by the rules of distribution of free software.  You can  use,      ;
;  modify and/ or redistribute the software under the terms of the CeCILL     ;
;  license as circulated by CEA, CNRS and INRIA at the following URL          ;
;  "http://www.cecill.info".                                                  ;
;                                                                             ;
;  As a counterpart to the access to the source code and  rights to copy,     ;
;  modify and redistribute granted by the license, users are provided only    ;
;  with a limited warranty  and the software's author,  the holder of the     ;
;  economic rights,  and the successive licensors  have only  limited         ;
;  liability.                                                                 ;
;                                                                             ;
;  In this respect, the user's attention is drawn to the risks associated     ;
;  with loading,  using,  modifying and/or developing or reproducing the      ;
;  software by the user in light of its specific status of free software,     ;
;  that may mean  that it is complicated to manipulate,  and  that  also      ;
;  therefore means  that it is reserved for developers  and  experienced      ;
;  professionals having in-depth computer knowledge. Users are therefore      ;
;  encouraged to load and test the software's suitability as regards their    ;
;  requirements in conditions enabling the security of their systems and/or   ;
;  data to be ensured and,  more generally, to use and operate it in the      ;
;  same conditions as regards security.                                       ;
;                                                                             ;
;  The fact that you are presently reading this means that you have had       ;
;  knowledge of the CeCILL license and that you accept its terms.             ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

extern unsupportedHandler

[GLOBAL irq_unsupported]
irq_unsupported:
	cli
	push 0x2A
	; save & go kernel land
	pusha
	push esp
	mov si, ds
	mov ax, 0x10
	mov ds, ax
	mov es, ax
	mov fs, ax
	mov gs, ax
; call c handler (&ctx)
	call unsupportedHandler
	add esp, 4
; restore - assuming a common data segment for ds es fs gs
	mov ds, si
	mov es, si
	mov fs, si
	mov gs, si
	popa
; skip err_code & int_no
	add esp, 8
	iret

extern testHandler

[GLOBAL irq_test]
irq_test:
	cli
	; push err_code=0, intno = 1
	push 0
	push 1
	; save & go kernel land
	pusha
	push esp
	; TODO : should we force ss to 0x10 ? 
; call c handler (&ctx)
	call testHandler
; FIXME : testHandler now never returns !

	add esp, 4
; restore - assuming a common data segment for ds es fs gs
	mov ds, 0x10
	mov es, 0x10 
	mov fs, 0x10 
	mov gs, 0x10 
	popa
; skip err_code & int_no
	add esp, 8
	iret


; extern timerHandler
extern irqHardwareHandler

[GLOBAL irq_timer]
irq_timer:
	cli
	; push err_code=0, intno = 32
	push 0	
	push 32	
	; push user registers
	pusha
	push esp
	; TODO : should we force ss to 0x10 ? 
; call c handler (&ctx)
	call irqHardwareHandler

	/* This code is mandatory if irqHardwareHandler returns,
	 * for instance if irq occured in kernel-land. */
	add esp, 4
; restore - assuming a common data segment for ds es fs gs
	mov ds, 0x10
	mov es, 0x10 
	mov fs, 0x10 
	mov gs, 0x10 
	popa
; skip err_code & int_no
	add esp, 8
	iret


