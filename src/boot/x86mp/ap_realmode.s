;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  © Université Lille 1, The Pip Development Team (2015-2017)                 ;
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

[GLOBAL patch_code_start]
[GLOBAL patch_code_end]
[EXTERN gp] ; x86 GDT pointer, already set-up by BSP
[EXTERN apboot]

; Yeah, some real-mode stuff. :(
[BITS 16]

; Patch code that shall be copied to 0x70000
; Only jumps to 0xB000, 16-bits real-mode EP
patch_code_start:
	mov bx, 0xB00
	mov es, bx
	mov bx, 0x0
	mov eax, 0xB000
	jmp eax
patch_code_end:

; 0xB000 : Real-mode entrypoint for APs
[GLOBAL real_mode_ep]
section .apentry
real_mode_ep:
	; Disable interrupts
	cli
	
	; Write stuff to tell our BSP that we booted
	mov bx, 0x1000
    mov es, bx
    mov bx, 0x0
    mov dword [es:bx], 0xCAFE

    ; Now that we booted, let's switch to protected mode
    ; First load the GDT
    lgdt [APGDTPointer]
    
	; Enable protected mode
    mov eax, cr0
    or al, 1
    mov cr0, eax

    ; Jump to 32 bits PM EP
    jmp APGDT.Code:0xC000
    jmp $

; x86 protected mode static GDT for APs
[GLOBAL APGDT]
[GLOBAL GDTEnd]
[GLOBAL APGDTPointer]
[GLOBAL aptr]
aptr:
   dd 0
   dd 0
APGDT:
    .Null: equ $ - APGDT
    dw 0    ; Limit (low)
    dw 0    ; Base (low)
    db 0    ; Base (middle)
    db 0    ; Access
    db 0    ; Granularity
    db 0    ; Base (high)
    .Code: equ $ - APGDT
    dw 0xFFFF   ; Limit to 0xFFFFF granularity 4kb
    dw 0
    db 0
    db 10011010b
    db 11001111b     ; Higher : granularity 4kb, 32 bits protected mode segment; lower : Limit 0xF
    db 0
    .Data: equ $ - APGDT
    dw 0xFFFF
    dw 0
    db 0
    db 10010010b
    db 11001111b
    db 0
    .UserCode: equ $ - APGDT
    dw 0xFFFF
    dw 0
    db 0
    db 11111010b
    db 11001111b
    db 0
    .UserData: equ $ - APGDT
    dw 0xFFFF
    dw 0
    db 0
    db 11110010b
    db 11001111b
    db 0
GDTEnd:
APGDTPointer:
    dw $ - APGDT - 1
    dd APGDT


