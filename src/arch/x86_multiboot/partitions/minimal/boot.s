.section .text
.global start
.extern _main
start:
    call _main

loop:
    jmp loop
