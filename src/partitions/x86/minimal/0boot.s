#define __ASSEMBLY__
#include <pip/vidt.h>
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


INTERRUPT_HANDLER(asmInterrupt14,interrupt14)
INTERRUPT_HANDLER(asmInterrupt15,interrupt15)

INTERRUPT_HANDLER(asmInterrupt33,interrupt33)
INTERRUPT_HANDLER(asmInterrupt40,interrupt40)
INTERRUPT_HANDLER(asmInterrupt44,interrupt44)
