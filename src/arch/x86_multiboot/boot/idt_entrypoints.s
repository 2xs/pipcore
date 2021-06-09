;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  © Université de Lille, The Pip Development Team (2015-2021)                ;
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

;----------------------------------------------------------------------
;          Intel IA-32 Architectures Software Developers Manual
;                Vol. 3a - Section 6.12.1 - Figure 6-4
; Stack Usage on Transfers to Interrupt and Exception-Handling Routines
;----------------------------------------------------------------------

;                           No privilege level change
;                (might happen when executing on callgate's `cli`)
;                                       ;
;-------------;                         ;
;             ; <- ESP before transfer  ;
;-------------;                         ;
;    EFLAGS   ;                         ;
;-------------;                         ;
;      CS     ;                         ;
;-------------;                         ;
;     EIP     ;  <- ESP after transfer  ;
;-------------;                         ;
;(Error  Code);( <- ESP after transfer) ;
;-------------;           (*)           ;
;     |||     ;                         ;
;---- vvv ----;                         ;


;                         With privilege level change to #
;                           (only to ring 0 in our case)
;                                       ;
;     Interrupted procedure's stack     ;             Handler's stack
;-------------;                         ;-------------;
;             ;<- SS:ESP before transfer;             ;  <- SS#:ESP# in TSS
;-------------;    |  |                 ;-------------;
;             ;    |--+---------------> ;      SS     ;
;-------------;       |                 ;-------------;
;             ;       |---------------> ;     ESP     ;
;-------------;                         ;-------------;
;             ;                         ;    EFLAGS   ;
;-------------;                         ;-------------;
;             ;                         ;      CS     ;
;-------------;                         ;-------------;
;             ;                         ;     EIP     ;  <- SS:ESP after transfer
;-------------;                         ;-------------;
;             ;                         ;(Error  code); (<- SS:ESP after transfer)
;-------------;                         ;-------------;            (*)
;     |||     ;                         ;     |||     ;
;-----vvv-----;                         ;---- vvv ----;


;---------------------------------------------------------
; (*) : Interrupt that generate an error code are described
; in the Intel IA-32 Architectures Software Developers Manual
;          Vol. 3a - Section 6.3.1 - Table 6-1
;        Protected-Mode Exceptions and Interrupts
;
;              (and also later in this file)
;---------------------------------------------------------




; TL;DR no `cli` needed in an interrupt gate
;---------------------------------------------------------
;   Intel IA-32 Architectures Software Developers Manual
;              Vol. 3a - Section 6.12.1.2
; Flag Usage By Exception- or Interrupt-Handler Procedure
;---------------------------------------------------------
; [...] When accessing an exception- or interrupt-handling
; procedure through an interrupt gate, the processor clears
; the IF flag to prevent other interrupts from interfering
; with the current interrupt handler.
;---------------------------------------------------------


;---------------------------------------------------
; Fault interrupt assembly wrapper, for faults that
; *do not* push an error code on the stack
;---------------------------------------------------
; First arg  (%1) : fault mnemonic (abbreviated name)
; Second arg (%2) : Interrupt level associated to the fault
;---------------------------------------------------
%macro FAULT_INT_NOERRCODE 2
[GLOBAL fault_%1_asm]
fault_%1_asm:
	; push a fake error code to unify behaviour with the other faults
	push 0
	; push int_no
	push %2
	jmp fault_common_code
%endmacro


;---------------------------------------------------
; Fault interrupt assembly wrapper, for faults that
; push an error code on the stack
;---------------------------------------------------
; First arg  (%1) : fault mnemonic (abbreviated name)
; Second arg (%2) : Interrupt level associated to the fault
;---------------------------------------------------
%macro FAULT_INT_ERRCODE 2
[GLOBAL fault_%1_asm]
fault_%1_asm:
	; no need to push an error code, CPU already did
	; push int_no
	push %2
	jmp fault_common_code
%endmacro



;---------------------------------------------------
; Hardware interrupt assembly wrapper
;---------------------------------------------------
; First arg  (%1) : Hardware int mnemonic (abbreviated name)
; Second arg (%2) : Interrupt level associated to the interrupt
;---------------------------------------------------
%macro HARDWARE_INT 2
[GLOBAL hardware_%1_asm]
hardware_%1_asm:
	; push a fake error code to unify behaviour with some faults
	push 0
	; push int_no
	push %2
	jmp hardware_common_code
%endmacro

;---------------------------------------------------
; Software interrupt assembly wrapper
;---------------------------------------------------
; First arg (%1) : Interrupt level associated to the interrupt
;---------------------------------------------------
%macro SOFTWARE_INT 1
[GLOBAL software_%1_asm]
software_%1_asm:
	; push a fake error code to unify behaviour with some faults
	push 0
	; push int_no
	push %1
	jmp software_common_code
%endmacro

%macro INTERRUPT_TYPE 1
extern %1InterruptHandler
%1_common_code:
	; push general purpose registers
	pusha
	; the int_ctx_t struct is now complete
        ; ESP holds a pointer to it.
	push esp

	; conditional assembly, only if %1 == hardware
	; https://www.nasm.us/doc/nasmdoc4.html#section-4.4.5
	; see later in this file why we need to check the stack
	%ifidni %1,hardware
		; stack sanity check
		STACK_SANITY_CHECK
	%endif

	; call c handler (int_ctx_t *ctx)
	call %1InterruptHandler
	; should not return, likely a bug
;
;	; skip the pointer to the context
;	add esp, 4
;	; restore the general purpose registers
;	popa
;	; skip err_code & int_no
;	add esp, 8
;	iret
%endmacro

; About the stack sanity check in hardware_common_code
; --------------------------------------------------------------
; It might happen that, at the very first instruction of a callgate,
; an interrupt occurs, thus receiving an interrupt in kernelland.
; There is no way to prevent that. Nonetheless, no stack switch would
; occur in that case, because we are already on ring 0. Thus, the
; calling (userland) context of the callgate would still be accessible.
; What we could do is to ignore the far call, as if userland was about
; to execute the far call when the interrupt occured, and handle the
; interrupt as usual.
; Then, we can modify the userland context's EIP in order to roll it
; back by a single instruction as if the far call never occured.
; Hence when executing IRET, the userland context would be restored a
; single instruction back, and execute the far call
;
;                Handler's stack
;                ;-------------;
;                ;             ;  <-- SS0:ESP0 in TSS
;            +---;-------------;
;            |   ; userland SS ;
;            |   ;-------------;
;            |   ; userland ESP;
;            |   ;-------------;-+
;            |   ;     argn    ; |
;            |   ;-------------; |
;  callgate -+   ;     ...     ; +-- Args copied by the callgate
;            |   ;-------------; |
;            |   ;     arg1    ; |
;            |   ;-------------;-+
;            |   ; userland CS ;
;            |   ;-------------;
;            |   ; userland EIP; <-- SS:ESP before interrupt occured
;            >---;-------------;
;            |   ;uland EFLAGS ; <-- Note : the interrupt flag has been cleared
;            |   ;-------------;
; interrupt -+   ; callgate CS ;
;    gate    |   ;-------------;
;            |   ; callgate EIP; <-- SS:ESP right after interrupt
;            >---;-------------;
;            |   ;      0      ;
;            |   ;-------------;
;            |   ;    int_no   ;
;            |   ;-------------;
;  assembly -+   ;             ;
;    code    |   ; General regs;
;            |   ;             ;
;            |   ;-------------;
;            |   ; int_ctx_t * ; <-- SS:ESP
;            +---;-------------;
;                ;     |||     ;
;                ;---- vvv ----;

; Mimicking the tss C struct to get the offsets
struc tss_t
	.prev_tss  resw 1 ; 16 bits
	.reserved0 resw 1 ; 16 bits
	.esp0      resd 1 ; 32 bits
; ------ end of the struct is omitted here
endstruc

struc crooked_stack
	.ctx_ptr   resd 1 ; 32 bits
	.regs      resd 8 ; 8 * 32 bits
	.int_no    resd 1 ; 32 bits
	.err_code  resd 1 ; 32 bits
	.cg_eip    resd 1 ; 32 bits
	.cg_cs     resd 1 ; 32 bits
	.eflags    resd 1 ; 32 bits
	.ul_eip    resd 1 ; 32 bits
	.ul_cs     resd 1 ; 32 bits
; ----- callgate args (variable size)
; ----- .ul_esp    resd 1 ; 32 bits
; ----- .ul_ss     resd 1 ; 32 bits
endstruc


; --------------------------------------------------
; Accessing a global variable declared in C code
; https://www.nasm.us/doc/nasmdo10.html#section-10.1.3
; --------------------------------------------------
; Though here we don't need the underscore to access
; the variable we are trying to access ¯\_(ツ)_/¯
; --------------------------------------------------
extern tss
%macro STACK_SANITY_CHECK 0
	; get cs of interrupted context in eax
	mov eax, [esp + crooked_stack.cg_cs]
	;---------------------------------------------------------
	;   Intel IA-32 Architectures Software Developers Manual
	;                 Vol. 3a - Section 5.5
	;                    Privilege levels
	;---------------------------------------------------------
	; filter out RPL (Requested privilege level)
	and eax, ~0b11
	; compare eax to KERNEL_CODE_SEGMENT
	cmp eax, 8
	; jump if cs != KERNEL_CODE_SEGMENT
	jne %%stack_ok

	; stack is crooked
	; cs must be retrieved from early callgate pushes
	mov eax, [esp + crooked_stack.ul_cs]
	mov [esp + crooked_stack.cg_cs], eax

	; eip must be retrieved from early callgate pushes
	mov eax, [esp + crooked_stack.ul_eip]
	; and fixed so that the far call is executed again
	sub eax, 7
	mov [esp + crooked_stack.cg_eip], eax

	; restore the interrupt flags in eflags
	or dword[esp + crooked_stack.eflags], 0x200

	; remember the current stack top
	mov eax, esp

	; move to the bottom of the stack to retrieve ss and esp
	mov esp, [tss + tss_t.esp0]

	; place the stack pointer above esp / ss
	sub esp, 8

	; store userland esp in edx
	pop edx
	; store userland ss in ecx
	pop ecx

	; go back to the initial stack top
	mov esp, eax

	; replace saved ss and esp at their correct location
	mov [esp + crooked_stack.ul_cs] , ecx
	mov [esp + crooked_stack.ul_eip], edx

; Macro-local labels
; https://www.nasm.us/doc/nasmdoc4.html#section-4.3.2
%%stack_ok:
%endmacro

INTERRUPT_TYPE fault
INTERRUPT_TYPE hardware
INTERRUPT_TYPE software

; Faults interrupt assembly declaration
; Intel Reserved interrupt levels have a single definition #15
;---------------------------------------------------------
; see Intel IA-32 Architectures Software Developers Manual
;            Vol. 3a - Section 6.3.1 - Table 6-1
;          Protected-Mode Exceptions and Interrupts
;---------------------------------------------------------

FAULT_INT_NOERRCODE  DE  ,0
FAULT_INT_NOERRCODE  DB  ,1
FAULT_INT_NOERRCODE  NMI ,2
FAULT_INT_NOERRCODE  BP  ,3
FAULT_INT_NOERRCODE  OF  ,4
FAULT_INT_NOERRCODE  BR  ,5
FAULT_INT_NOERRCODE  UD  ,6
FAULT_INT_NOERRCODE  NM  ,7
FAULT_INT_ERRCODE    DF  ,8
FAULT_INT_NOERRCODE  CSO ,9
FAULT_INT_ERRCODE    TS  ,10
FAULT_INT_ERRCODE    NP  ,11
FAULT_INT_ERRCODE    SS  ,12
FAULT_INT_ERRCODE    GP  ,13
FAULT_INT_ERRCODE    PF  ,14
FAULT_INT_NOERRCODE  RES ,15
FAULT_INT_NOERRCODE  MF  ,16
FAULT_INT_ERRCODE    AC  ,17
FAULT_INT_NOERRCODE  MC  ,18
FAULT_INT_NOERRCODE  XM  ,19
FAULT_INT_NOERRCODE  VE  ,20
;FAULT_INT_NOERRCODE  RES 21
;FAULT_INT_NOERRCODE  RES 22
;FAULT_INT_NOERRCODE  RES 23
;FAULT_INT_NOERRCODE  RES 24
;FAULT_INT_NOERRCODE  RES 25
;FAULT_INT_NOERRCODE  RES 26
;FAULT_INT_NOERRCODE  RES 27
;FAULT_INT_NOERRCODE  RES 28
;FAULT_INT_NOERRCODE  RES 29
;FAULT_INT_NOERRCODE  RES 30
;FAULT_INT_NOERRCODE  RES 31

HARDWARE_INT ALRM ,32
HARDWARE_INT KEYB ,33
HARDWARE_INT CASC ,34
HARDWARE_INT COM2 ,35
HARDWARE_INT COM1 ,36
HARDWARE_INT LPT2 ,37
HARDWARE_INT FLPD ,38
HARDWARE_INT SPUR ,39
HARDWARE_INT RTC  ,40
HARDWARE_INT PER1 ,41
HARDWARE_INT PER2 ,42
HARDWARE_INT PER3 ,43
HARDWARE_INT PS2M ,44
HARDWARE_INT FPU  ,45
HARDWARE_INT PHD  ,46
HARDWARE_INT SHD  ,47

%assign i 48
%rep 208
SOFTWARE_INT i
%assign i i+1
%endrep
