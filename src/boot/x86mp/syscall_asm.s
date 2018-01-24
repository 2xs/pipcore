[GLOBAL init_msr]
[EXTERN syscall_table]
[EXTERN sysenter_c_ep]
[EXTERN saveCallgateCaller]
[EXTERN api_lock]
[EXTERN api_unlock]
[GLOBAL acquire]
[GLOBAL release]

api_spinlock: dd 0

acquire:
    mov eax, api_spinlock       ; Spinlock address
    bt dword [eax], 0            ; Check spinlock state
    jc acquire                  ; If not, spin
    lock bts dword [eax], 0      ; Lock
    jc acquire                  ; Locking failed, spin
acquire_ret:
    ret

release:
    mov eax, api_spinlock
    btr dword [eax], 0           ; Release lock
    ret

sysenter_ep:
    ; Save caller info
    push edx ; User EIP
    push ecx ; User ESP

sysenter_lock:
    ; Spinlock
    ;call acquire

sysenter_save_caller:
    ; Save caller info
    push edx            ; gate_ctx_t->eip
    pusha               ; gate_ctx_t->regs
    mov [esp + 12], ecx ; Fix ESP
    push esp            ; gate_ctx_t pointer
    call saveCallgateCaller
    add esp, 0x4        ; Fix "push esp"
    popa                ; Fix "pusha"
    add esp, 0x4        ; Fix "push edx"

sysenter_start_call:
    ; Save general registers excepted EAX
    push ebx
    push esi
    push edi

    ; Find call number from User ESP - last argument is last value pushed so we should get it right now
    mov ebx, ecx
    mov ebx, [ebx + 0x8] ; First parameter
    
    ; Check system call number
    cmp ebx, 0x13   ; Check our syscall number doesn't exceed maximum system call id
    mov eax, 0x0    ; "Zero" default return value
    jae back_to_userland    ; If higher or equal, get back to userland

    ; Check user stack bounds
    cmp ecx, 0x701000    ; Check we are indeed in a userland stack
    jbe back_to_userland ; If we're not, cancel call at once

sysenter_copy:
    ; Prepare for syscall
    std             ; Set direction flag

    mov esi, ecx    ; Copy from user-land ESP
    add esi, 0x20   ; We copy downwards : fix user esp so we get our arguments
    mov ecx, 0x8    ; 6 parameters maximum + EBP and return address
    mov edi, esp    ; Copy to our stack, decrementing using direction flag
    sub edi, 0x4    ; Start copy as we are pushing something
    rep movsd       ; Copy dword parameters (32 bits)

    cld             ; Clear direction flag
    mov esp, edi    ; Fix ESP to take into account our parameters
    add esp, 0xC    ; Ignore caller's EBP & return address & syscall number

sysenter_find_call:
    ; At this point our ESP has all parameters onto it : call the Pipcall
    ; EBX : system call id
    mov ecx, syscall_table
    mov eax, 0x4    ; Per-call offset
    mul ebx         ; EDX:EAX = total offset
    add ecx, eax    ; Get the system call address
    mov ecx, [ecx]  ; Dereference to get call pointer

sysenter_call:
    call ecx       ; Do the system call

    ; At this point, EAX is the system call's return value

    ; Fix stack by virtually pop'ing the 6 parameters
    add esp, 0x18 

back_to_userland:
    ; Restore caller info
    pop edi
    pop esi
    pop ebx
    pop ecx ; Retrieve user EIP
    pop edx ; Retrieve user ESP
    ;push eax
    ;call release
    ;pop eax
    sti
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
    mov eax, [esp + 0x4] ; 0x300000 ; [ebp + 0x8]    ; Stack address given as parameter
    wrmsr

    ; Setup SYSENTER entrypoint
    mov ecx, 0x176 ; IA32_SYSENTER_EIP
    mov edx, 0
    mov eax, sysenter_ep
    wrmsr

    ret
