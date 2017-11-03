[GLOBAL patch_code_start]
[GLOBAL patch_code_end]

; Yeah, some real-mode stuff. :(
[BITS 16]

patch_code_start:
    mov bx, 0x1000
    mov es, bx
    mov bx, 0x0
    mov dword [es:bx], 0xCAFE
    jmp $
patch_code_end:
