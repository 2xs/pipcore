[BITS 32]
[EXTERN mp_c_main]
section .apentry32
    ; Out of the 16 bits nightmare! Yay.
    cli
    
    ; Flush segments
    mov ax, 0x10
    mov ds, ax
    mov es, ax
    mov fs, ax
    mov gs, ax
    mov ss, ax

    ; Get a stack for each core
    mov esp, _mp_stack   ; u want sum stack ?
    mov ebp, esp
    
    mov eax, mp_c_main
    call eax
    jmp $


SECTION .bss
mpstack:   resb    16384 ; Allocate 16kb in the BSS for the kernel stack
_mp_stack:
    
