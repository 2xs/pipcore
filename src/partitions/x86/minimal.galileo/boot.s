.section .text
.global boot
.extern main
.extern vcli
boot:
    push %ebx
    call vcli
    call main

loop:
    jmp loop
