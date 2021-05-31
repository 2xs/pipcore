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

;%macro INTERRUPT_TYPE 1
;extern %1InterruptHandler
;%1_common_code:
;	; push general purpose registers
;	pusha
;	; the int_ctx_t struct is now complete
;        ; ESP holds a pointer to it.
;	; temporarily storing it in EAX register
;        mov eax, esp
;	; push current data segment to restore it
;	; in case the handler returns
;	; (assumes a common data segment for DS ES FS GS)
;	; `push ds` pushes 4 bytes (instead of expected 2 bytes)
;	push ds
;        ; push the pointer stored in EAX for the C handler
;	push eax
;
;	; TODO Use KERNEL_DATA_SEGMENT macro instead of 0x10
;	mov ds, 0x10
;	mov es, 0x10
;	mov fs, 0x10
;	mov gs, 0x10
;
;
;	; call c handler (user_ctx_t *ctx)
;	call %1InterruptHandler
;	; should not return but...
;	; in case an interrupt occurred at the very
;	; first instruction of any callgate (`cli`)
;	; we just return for now
;	; TODO see possible fix described in idt.c
;
;
;	; skip the pointer to the context
;	add esp, 4
;	; restore the data segments
;	; (assuming a common data segment for DS ES FS GS)
;	pop eax
;	mov ds, ax
;	mov es, ax
;	mov fs, ax
;	mov gs, ax
;	; restore the general purpose registers
;	popa
;	; skip err_code & int_no
;	add esp, 8
;	iret
;%endmacro

%macro INTERRUPT_TYPE 1
extern %1InterruptHandler
%1_common_code:
	; push general purpose registers
	pusha
	; the int_ctx_t struct is now complete
        ; ESP holds a pointer to it.
	push esp

	; call c handler (int_ctx_t *ctx)
	call %1InterruptHandler
	; should not return but...
	; in case an interrupt occurred at the very
	; first instruction of any callgate (`cli`)
	; we just return for now
	; TODO see possible fix described in idt.c


	; skip the pointer to the context
	add esp, 4
	; restore the general purpose registers
	popa
	; skip err_code & int_no
	add esp, 8
	iret
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
