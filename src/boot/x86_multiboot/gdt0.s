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

; Configuration of the x86 Global Descriptor Table and Task State Segment.
%macro CG_GLUE_NOARG 1
extern %1
global cg_%1
cg_%1:
	cli
 	call %1
	sti
	retf
%endmacro

; Callgate stack layout: 
;	usereip
;	cs
;	args, ...
;	useresp
;	ss
%macro CG_GLUE 2
extern %1
global cg_%1
cg_%1:
	cli
; save resume eip:cs
	pop esi
	pop edi
; call pip function
 	call %1
; restore eip:cs
	push edi
	push esi
; back to userland
	sti
	retf (4*%2)
%endmacro

%macro CG_GLUE_CTX 2
extern %1
global cg_%1
cg_%1:
	cli
; push user registers
	pusha
; useresp
	mov eax, dword [0x20+esp+8+4*%2]
; skip call arguments in saved esp
	add eax, 4*%2
; fix useresp in regs
	mov [esp+12], eax
; push &ctx
	push esp
; push callGlue arguments
%rep %2
	push dword [0x24+esp+8+4*(%2-1)]
%endrep
	call %1
	add esp, 0x24+4*%2
; back to userland
	sti
	retf (4*%2)
%endmacro

;          Stack switch from userland to kernelland through a call gate
;
;            Userland's stack           ;             Handler's stack
;-------------;                         ;-------------;
;             ;                         ;             ;  <- SS0:ESP0 in TSS
;-------------;                         ;-------------;
;             ;     |------------------>;      SS     ;
;-------------;     |                   ;-------------;
;             ;     |  |--------------->;     ESP     ;
;-------------;-+   |  |              +-;-------------;
;     arg1    ; |   |  |              | ;     arg1    ;
;-------------; |   |  |              | ;-------------;
;     ...     ; |---|--|------------->| ;     ...     ;
;-------------; |   |  |              | ;-------------;
;     argN    ;<-- SS:ESP before call | ;     argN    ;
;-------------;-+                     +-;-------------;
;     |||     ;                         ;      CS     ;
;-----vvv-----;                         ;-------------;
                                        ;     EIP     ;  <- SS:ESP after transfer
                                        ;-------------;
                                        ;     |||     ;
                                        ;-----vvv-----;

;------------------------------------------------------
; The idea behind the below macro is to copy the call
; gate arguments higher on the stack, in order to free
; some space where we can place an iretable structure,
; plus the general purpose registers.
; We want to use `iret` because of the infamous race
; condition where an interrupt occurs between the
; execution of a far call and its subsequent `cli`,
; creating a kernelland interrupt. The same race
; condition could happen between the execution of a
; `sti` and a `retf`, and would not occur with a `iret`
;------------------------------------------------------
; see awesome ASCII art below for visual representation
; of the kernel stack after this assembly code
;------------------------------------------------------


;             Handler's stack
;-------------;
;             ;  <- SS0:ESP0 in TSS
;-------------;-+
;      SS     ; |
;-------------; |
;     ESP     ; |
;-------------; |
;    eflags   ; |-- iretable structure
;-------------; |
;      CS     ; |
;-------------; |
;     EIP     ; |
;-------------;-+
;     ...     ; |
;   general   ; |
;   purpose   ; |-- 8 * 4 bytes (pusha struct)
;  registers  ; |
;     ...     ; |
;-------------;-+
;     arg1    ;
;-------------;
;     ...     ;
;-------------;
;     argn    ;  <- SS:ESP after assembly
;-------------;
;     |||     ;
;-----vvv-----;


%macro CG_GLUE_CTX 2
extern %1
global cg_%1
cg_%1:
	; interrupts are not cleared upon call gate entry.
	; this might create a situation where an interrupt
	; occurs in kernelland
	; retf doesn't restore eflags either.
	; that is why we use `iret`, in order to prevent
	; the same problem between a `sti` and a `retf`
	cli

	; first, copy the arguments higher on the stack

	; set esp where the args should be copied
	; we need 11 dword free
	; stack top is currently at %2 + cs + eip
	; so we add 11-(%2+2) dwords to ESP
	sub esp, (11 - (%2 + 2)) * 4
	; repeat for each arg + cs + eip
	%rep (%2+2)
		;copy the current dword (11 dword before stack top) to the stack top 
		push dword [esp + 11 * 4]
	%endrep
	; our args and cs:eip are now copied farther in the stack

	; setting ESP to the first argument pushed by CPU
	; we have pushed %2 args + cs + eip and we have to leap another
	; 11 dwords (pusha (8) + cs:eip (2) + eflags (1)) so 13 + %2 dwords
	add esp, (%2 + 13) * 4
	; push EFLAGS, filling the last dummy argument
	pushf
	; set Interrupt Enable flag in EFLAGS
	; otherwise userland would never be interrupted after `iret`
	or [esp], 0x0200

	; push CS, filling the first dummy arg
	push dword [esp - (%2+11) * 4]
	; push EIP, filling the second dummy argument
	push dword [esp - (%2+11) * 4]
	; push general purpose registers (8 * 4 bytes)
	; completing the gate_ctx_t
	pushad

	; set ESP to the top of the stack (after last arg)
	; %2  -> number of args to skip
	; * 4 -> size of args (4 bytes)
	sub esp, %2 * 4
	; push a pointer to the gate_ctx_t
	push esp + (%2 * 4)

	; call C handler (arg1, ..., arg%2, gate_ctx_t *)
	call %1

	; skip pointer to the context and args
	add esp, (%2 + 1) * 4
	; restore the general purpose registers
	popa
	; we are left with the iretable structure
	iret
%endmacro

; These functions might trigger a call to dispatchGlue
; therefore they need a reference to calling context (regs + eip)
; in order to save it if needed
CG_GLUE_CTX outbGlue		, 2
CG_GLUE_CTX inbGlue		, 1
CG_GLUE_CTX outwGlue		, 2
CG_GLUE_CTX inwGlue		, 1
CG_GLUE_CTX outlGlue 		, 2
CG_GLUE_CTX inlGlue 		, 1
CG_GLUE_CTX outaddrlGlue 	, 2
;CG_GLUE_CTX dispatchGlue	, 5
;CG_GLUE_CTX yieldGlue		, 5

; Those ones won't trigger a fault in caller
CG_GLUE createPartition		, 5
CG_GLUE countToMap  		, 2
CG_GLUE prepare 			, 4
CG_GLUE addVAddr    		, 6
;CG_GLUE resume		    	, 2
CG_GLUE removeVAddr 		, 2
CG_GLUE	mappedInChild   	, 1
CG_GLUE	deletePartition 	, 1
CG_GLUE	collect 			, 2

CG_GLUE_NOARG  timerGlue
