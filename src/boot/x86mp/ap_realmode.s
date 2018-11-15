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


