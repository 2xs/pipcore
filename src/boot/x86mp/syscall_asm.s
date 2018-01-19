[GLOBAL init_msr]
[EXTERN syscall_table]
[EXTERN sysenter_c_ep]
sysenter_ep:
    ; Save caller info
    push edx ; User EIP
    push ecx ; User ESP

    ; Find call number from User ESP - last argument is last value pushed so we should get it right now
    mov ebx, ecx
    add ebx, 0xc
    mov ebx, [ebx]
    
    ; Prepare for syscall
    std             ; Set direction flag

    mov esi, ecx    ; Copy from user-land ESP
    add esi, 0x18   ; We copy downwards : fix user esp so we get our arguments
    mov ecx, 0x6    ; 6 parameters maximum
    mov edi, esp    ; Copy to our stack, decrementing using direction flag
    sub edi, 0x4    ; Start copy as we are pushing something
    rep movsd       ; Copy dword parameters (32 bits)

    cld             ; Clear direction flag
    mov esp, edi    ; Fix ESP to take into account our parameters

    ; At this point our ESP has all parameters onto it : call the Pipcall
    ; EBX : system call id
    mov ecx, syscall_table
    mov eax, 0x4    ; Per-call offset
    mul ebx         ; EDX:EAX = total offset
    add ecx, eax    ; Get the system call address
    mov ecx, [ecx]  ; Dereference to get call pointer
    call ecx       ; Do the system call

    ; At this point, EAX is the system call's return value

    ; Fix stack by virtually pop'ing the 6 parameters
    add esp, 0x1C

    ; Restore caller info
    pop ecx ; Retrieve user EIP
    pop edx ; Retrieve user ESP
    sysexit

init_msr:
    ; Setup SYSENTER code segment
    mov ecx, 0x174 ; IA32_SYSENTER_CS
    mov edx, 0x0
    mov eax, 0x08
    wrmsr

    ; Setup SYSENTER stack
    mov ecx, 0x175 ; IA32_SYSENTER_ESP
    mov edx, 0x0
    mov eax, 0x300000
    wrmsr

    ; Setup SYSENTER entrypoint
    mov ecx, 0x176 ; IA32_SYSENTER_EIP
    mov edx, 0
    mov eax, sysenter_ep
    wrmsr

    ret
