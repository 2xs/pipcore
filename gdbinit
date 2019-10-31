target remote localhost:1234
symbol-file build/x86_multiboot/pip.elf
break resumeAsm
continue
stepi
set $ctx=(user_ctx_t*)$eax
print *$x
