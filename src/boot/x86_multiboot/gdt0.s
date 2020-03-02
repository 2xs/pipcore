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
; The idea behind the below macros is to copy the call
; gate arguments higher on the stack, in order to free
; some space where we can place an iretable structure,
; and the general purpose registers in case we want a
; context.
; We want to use `iret` because of the infamous race
; condition where an interrupt occurs between the
; execution of a far call and its subsequent `cli`,
; creating a kernelland interrupt. The same race
; condition could happen between the execution of a
; `sti` and a `retf`, and would not occur with a `iret`
;------------------------------------------------------
; see awesome ASCII art above the assembly code for a
; visual representation of the kernel stack before the
; call to the C handler
;------------------------------------------------------

;-----------------------------------------------------------------------
; According to Agner Fog on his own site https://agner.org
; in this pdf : https://www.agner.org/optimize/calling_conventions.pdf
; Last updated on 2019-11-28 which is less than 2 weeks old at this time
;             OK its not "official", throw me out of a window
;                      if you find a better source
;-----------------------------------------------------------------------
; Chapter 6 - Table 4
; Scratch registers are registers that can be used for temporary storage
; without restrictions (also called caller-save or volatile registers).
;
; Scratch registers for 32-bits Windows, Linux, BSD, MacOS are :
; EAX, ECX, EDX, ST(0)-ST(7), XMM0-XMM7, YMM0-YMM7, ZMM0-ZMM7, K0-K7
;-----------------------------------------------------------------------
; TL;DR : we are going to use EAX ECX and EDX without saving them first
;-----------------------------------------------------------------------


;             Handler's stack at `call` instruction
;                          in below macro
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
;     arg1    ;
;-------------;
;     ...     ;
;-------------;
;     argn    ;  <- SS:ESP after assembly
;-------------;
;     |||     ;
;-----vvv-----;

%macro CG_GLUE 2
extern %1
global cg_%1
cg_%1:
	; interrupts are not cleared upon call gate entry.
	; this might create a situation where an interrupt
	; occurs in kernelland
	;
	; Fortunately, this situation can be avoided on return
	; (even if we use retf which does not restore eflags)
	; since sti is only effective upon execution of the next
	; instruction.
	;
	; The reason why we are not using a retf is to unify the
	; different ways of calling a control flow transfer
	cli

	; pop eip in eax
	pop eax
	; pop cs in edx
	pop edx

	; first, copy the arguments higher on the stack

	; set esp where the args should be copied + 1 dword to save esi, edi
	; we need 3 dwords free
	; stack top is currently at %2
	; so we set esp to esp + 3 * 4
	sub esp, 3 * 4

	; we are going to modify esi, edi and eflags
	; those are not scratch registers so we need to
	; save them first
	push esi
	push edi
	pushfd

	; clear direction flag so esi and edi are incremented with movsd
	cld
	; set destination before our pushes on the stack
	lea edi, [esp + 3 * 4]
	; set source 3 dwords higher
	lea esi, [edi + 3 * 4]
	; repeat for %2 args
	mov ecx, %2
	; copy
	rep movsd

	; restore previously saved registers
	popfd
	pop edi
	pop esi

	; go down the stack to replace the args we copied
	; with eflags, cs, eip
	; hopefully it doesn't mess up eflags
	add esp, (3 + %2) * 4
	; push EFLAGS, replacing the first argument
	pushf
	; set Interrupt Enable flag in EFLAGS
	; otherwise userland would never be interrupted after `iret`
	or dword [esp], 0x0200
	; push cs
	push edx
	; push eip
	push eax

	; go back to the stack top
	sub esp, %2 * 4
	; call C handler (arg1, ..., arg%2, gate_ctx_t *)
	call %1

	; skip pointer to the context and args
	add esp, %2 * 4
	; we are left with the iretable structure
	iret
%endmacro

;             Handler's stack at `call` instruction
;                          in below macro
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
;   general   ; |
;   purpose   ; |-- 8 dwords
;  registers  ; |
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
	;
	; Fortunately, this situation can be avoided on return
	; (even if we use retf which does not restore eflags)
	; since sti is only effective upon execution of the next
	; instruction.
	;
	; The reason why we are not using a retf is to unify the
	; different ways of calling a control flow transfer
	cli

	; pop eip in eax
	pop eax
	; pop cs in edx
	pop edx

	; first, copy the arguments higher on the stack

	; set esp where the args should be copied in order to save esi, edi
	; we need 11 dwords free (eflags + cs + eip + pusha 8 dwords + ctx_ptr )
	; stack top is currently at ss + esp + %2
	; so we set esp to esp + 12 * 4
	sub esp, 12 * 4

	; we are going to modify esi, edi and eflags
	; those are not scratch registers so we need to
	; save them first
	push esi
	push edi
	pushfd

	; clear direction flag so esi and edi are incremented with movsd
	cld
	; set destination before our pushes on the stack
	lea edi, [esp + 3 * 4]
	; set source 12 dwords higher
	lea esi, [edi + 12 * 4]
	; repeat for %2 args
	mov ecx, %2
	; copy
	rep movsd

	; restore previously saved registers
	popfd
	pop edi
	pop esi

	; go down the stack to replace the args we copied
	; hopefully it doesn't mess up eflags
	add esp, (12 + %2) * 4
	; push EFLAGS, replacing the first argument
	pushf
	; set Interrupt Enable flag in EFLAGS
	; otherwise userland would never be interrupted after `iret`
	or dword [esp], 0x0200
	; push cs
	push edx
	; push eip
	push eax
	; push general purpose registers (8 dwords)
	pushad
	; push ctx ptr
	push esp
	; go back to the stack top
	sub esp,  %2 * 4

	; call C handler (arg1, ..., arg%2, gate_ctx_t *)
	call %1

	; skip pointer to the context and args
	add esp, (%2 + 1) * 4
	; restore general purpose registers
	popad
	; we are left with the iretable structure
	iret
%endmacro

; These functions might trigger a call to dispatchGlue
; therefore they need a reference to calling context (regs + eip)
; in order to save it if needed
CG_GLUE_CTX outbGlue            , 2
CG_GLUE_CTX inbGlue             , 1
CG_GLUE_CTX outwGlue            , 2
CG_GLUE_CTX inwGlue             , 1
CG_GLUE_CTX outlGlue            , 2
CG_GLUE_CTX inlGlue             , 1
CG_GLUE_CTX outaddrlGlue        , 2
CG_GLUE_CTX yieldGlue           , 5

; Those ones won't trigger a fault in caller
CG_GLUE createPartition         , 5
CG_GLUE countToMap              , 2
CG_GLUE prepare                 , 4
CG_GLUE addVAddr    		, 6
CG_GLUE removeVAddr             , 2
CG_GLUE	mappedInChild           , 1
CG_GLUE	deletePartition         , 1
CG_GLUE	collect                 , 2
CG_GLUE set_int_state           , 1
CG_GLUE get_int_state           , 1

;CG_GLUE_NOARG  timerGlue
