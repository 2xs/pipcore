[BITS 32]
[EXTERN mp_c_main]
[EXTERN gp] ; GDT ptr
section .apentry32
	; Out of the 16 bits nightmare! Yay.
    cli
    
	; Print stuff on VGA terminal (first check to see whether we're alive or not)
	mov eax, 0xB8000
	mov dword [eax], 0x414F414F

	; Flush segments
    mov ax, 0x10
    mov ds, ax
    mov es, ax
    mov fs, ax
    mov gs, ax
    mov ss, ax
	
	; Put sum stack in low-memory (where we don't have anything important)
	; Under 1mb : A20 line is not enabled yet
	; TODO : well fuck
	mov esp, 0x4000
	mov ebp, esp

	; Enable A20 - should not be required, A20 should be enabled by BSP
	call enable_A20_kb

	; At this point, A20 line is enabled. Reload GDT from BSP
	; Reload the BSP's GDT (with callgates and stuff)
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
    mov esp, _mp_stack   ; u want sum stack ?
    mov ebp, esp
   
	mov eax, mp_c_main
    call eax
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
 
a20wait:
        in      al,0x64
        test    al,2
        jnz     a20wait
        ret
 
a20wait2:
        in      al,0x64
        test    al,1
        jz      a20wait2
        ret

SECTION .bss
mpstack:   resb    16384 ; Allocate 16kb in the BSS for the kernel stack
_mp_stack:
    
