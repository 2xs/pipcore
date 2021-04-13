.section .text
.global boot
.extern _main
boot:
    call _main

loop:
    jmp loop
