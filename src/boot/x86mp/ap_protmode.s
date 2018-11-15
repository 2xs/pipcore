[BITS 32]
[EXTERN mp_c_main]
[EXTERN gp] ; GDT ptr
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
	
	; Put sum stack in low-memory (where we probably don't have anything important)
	mov esp, 0x4000	; yolo
	mov ebp, esp	; double yolo

	; Enable A20 - should not be required, A20 should be enabled by BSP
	; status update : it is not
	call enable_A20_kb

	; At this point, A20 line is enabled. Reload GDT from BSP
	; It shouldn't hang. If it does, I'm done
	lgdt [gp]
	
	; Flush segments
	mov ax, 0x10
	mov ds, ax
	mov es, ax
	mov fs, ax
	mov gs, ax
	mov ss, ax

	; Move on.
	jmp 0x08:move_on

move_on:
    ; Get a stack for each core
    ; mov esp, _mp_stack
    ; mov ebp, esp
   
	mov eax, mp_c_main
    call eax
    jmp $

[GLOBAL give_safe_stack]
[EXTERN safe_mp_c_main]
; Gives each core a separate stack (called from C code).
; This should not be called concurrently... spin to win.
give_safe_stack:
    mov eax, [esp + 4]  ; Get parameter : new stack address
    mov esp, eax        ; Setup stack
    mov ebp, esp
    call safe_mp_c_main ; Enter boot stage 2 with proper stack
    jmp $

; Check A20 line status
is_A20_on:   
	pushad
	mov edi,0x112345  ;odd megabyte address.
	mov esi,0x012345  ;even megabyte address.
	mov [esi],esi     ;making sure that both addresses contain diffrent values.
	mov [edi],edi     ;(if A20 line is cleared the two pointers would point to the address 0x012345 that would contain 0x112345 (edi)) 
	cmpsd             ;compare addresses to see if the're equivalent.
	popad
	jne A20_on        ;if not equivalent , A20 line is set.
	mov eax, 0
	ret
A20_on:
	mov eax, 1
	ret

; Enable A20 line - Fast A20 way
; TODO : use this as a last resource, we should be using keyboard instead
enable_A20:
		in al, 0x92
		or al, 2
		out 0x92, al	
		ret

; Enable A20 line through keyboard controller
; Thanks Intel :))
enable_A20_kb:
        call    a20wait
        mov     al,0xAD
        out     0x64,al
 
        call    a20wait
        mov     al,0xD0
        out     0x64,al
 
        call    a20wait2
        in      al,0x60
        push    eax
 
        call    a20wait
        mov     al,0xD1
        out     0x64,al
 
        call    a20wait
        pop     eax
        or      al,2
        out     0x60,al
 
        call    a20wait
        mov     al,0xAE
        out     0x64,al
 
        call    a20wait
        ret

; Wait for PS2 controller COMMAND completion
a20wait:
        in      al,0x64
        test    al,2
        jnz     a20wait
        ret
 
; Wait for PS2 controller DATA completion
a20wait2:
        in      al,0x64
        test    al,1
        jz      a20wait2
        ret

SECTION .bss

[GLOBAL mp_stack_base]

mpstack:   resb    4096 ; Allocate 4kb in the BSS for the kernel stack
_mp_stack:
stackpool:  resb    0x10000;  Per-core stacks
mp_stack_base:

