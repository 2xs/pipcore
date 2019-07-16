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

; Generic fault handler, without any error code pushed
%macro ISR_NOERRCODE 1
global isr%1
isr%1:
	cli
	push byte 0
	push %1
	jmp isrCommonStub
%endmacro

; Generic fault handler, with an error code pushed
%macro ISR_ERRCODE 1
global isr%1
isr%1:
	cli
	push %1
	jmp isrCommonStub
%endmacro

; Generic IRQ handler
%macro IRQ_STUB 2
global irq%1
irq%1:
	cli
	push byte 0
	push byte %2
	jmp irqCommonStub
%endmacro

; Define generic interrupt handler as part of C code
extern genericHandler

; Generic handlers for any kind of interrupt (same behavior)
%macro DEFINE_HANDLER 1

; Common stub for interrupt : push registers, switch to kernel land, call to the C-level handler, restore the registers, fix the stack and get back to business
%1CommonStub:
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
	call genericHandler
	add esp, 4
; restore
	mov ds, si
	mov es, si
	mov fs, si
	mov gs, si
	popa
; skip err_code & int_no
	add esp, 8
	iret
%endmacro

; Declaration of the stubs for IRQ and fault handlers
DEFINE_HANDLER irq
DEFINE_HANDLER isr

[GLOBAL readCR2]
readCR2:
	mov eax, cr2
	ret

[GLOBAL dispatchAsm]
dispatchAsm:
	; (eip, esp, data1, data2, caller)
	cli
	mov	ebp, esp
	; user data segment
	mov	ax, 0x23
	mov	ds, ax
	mov	es, ax
	mov	fs, ax
	mov	gs, ax
	push	0x23
	; user stack
	mov	eax, [ebp+8]
	push	eax
	; push flags
	pushf
	; set int enable flag
	or	dword [esp], 0x200
	; user code segment
	push	0x1B
	; interrupt handler
	push	dword [ebp+4]
	; set register args
	mov	eax, [ebp+0xC]
	mov	ebx, [ebp+0x10]
	mov	ecx, [ebp+0x14]
	; TODO clobber others registers
	; jump to userland
	iret

[GLOBAL resumeAsm]
resumeAsm:
; (user_ctx_s *ctx)
	mov	eax, [esp+4]
; restore vflags for user
	mov	ebx, [eax+4]
	mov	dword [0xfffffffc], ebx
; (userland segments )
	mov	bx, 0x23
	mov	ds, bx
	mov	es, bx
	mov	fs, bx
	mov	gs, bx
	push	0x23
; (userland esp)
	push	dword [eax+0x18]
; eflags + restore interrupts
	push	dword [eax+8]
	or	dword [esp], 0x200
; user eip:cs
	push	0x1b
	push	dword [eax]
; registers (bwarg)
	mov	edi, [eax+0xc]
	mov	esi, [eax+0x10]
	mov	ebp, [eax+0x14]
	mov	ebx, [eax+0x1C]
	mov	edx, [eax+0x20]
	mov	ecx, [eax+0x24]
	mov	eax, [eax+0x28]
	; switch to context
	iret

; Definition of each interrupt handler for x86 (0-31 : faults, 32-47 : IRQ)
ISR_NOERRCODE 0
ISR_NOERRCODE 1
ISR_NOERRCODE 2
ISR_NOERRCODE 3
ISR_NOERRCODE 4
ISR_NOERRCODE 5
ISR_NOERRCODE 6
ISR_NOERRCODE 7
ISR_ERRCODE   8
ISR_NOERRCODE 9
ISR_ERRCODE   10
ISR_ERRCODE   11
ISR_ERRCODE   12
ISR_ERRCODE   13
ISR_ERRCODE   14
ISR_NOERRCODE 15
ISR_NOERRCODE 16
ISR_NOERRCODE 17
ISR_NOERRCODE 18
ISR_NOERRCODE 19
ISR_NOERRCODE 20
ISR_NOERRCODE 21
ISR_NOERRCODE 22
ISR_NOERRCODE 23
ISR_NOERRCODE 24
ISR_NOERRCODE 25
ISR_NOERRCODE 26
ISR_NOERRCODE 27
ISR_NOERRCODE 28
ISR_NOERRCODE 29
ISR_NOERRCODE 30
ISR_NOERRCODE 31
IRQ_STUB 0 , 32
IRQ_STUB 1 , 33
IRQ_STUB 2 , 34
IRQ_STUB 3 , 35
IRQ_STUB 4 , 36
IRQ_STUB 5 , 37
IRQ_STUB 6 , 38
IRQ_STUB 7 , 39
IRQ_STUB 8 , 40
IRQ_STUB 9 , 41
IRQ_STUB 10 , 42
IRQ_STUB 11 , 43
IRQ_STUB 12 , 44
IRQ_STUB 13 , 45
IRQ_STUB 14 , 46
IRQ_STUB 15 , 47

; Generate remaining ISR handlers
%assign i 48
%rep 208
ISR_NOERRCODE i
%assign i i+1
%endrep
