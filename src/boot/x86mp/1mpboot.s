[GLOBAL delay_EAX_microseconds]
delay_EAX_microseconds:
   pusha

   mov   ecx,eax
   mov   eax,100000
   xor   edx, edx
   div   ecx

   mov   ecx,eax
   mov   eax,1193182
   xor   edx, edx
   div   ecx

   out   0x42,al
   xchg al, ah
   out   0x42,al

.T0:   in   al,0x61
   test al,0x20
   jz   .T0

   popa
   ret

[GLOBAL delay]
delay:
    pop eax
    push eax
    call delay_EAX_microseconds
    ret

[GLOBAL disable_pic]
disable_pic:
    mov al, 0xff
    out 0xa1, al
    out 0x21, al
