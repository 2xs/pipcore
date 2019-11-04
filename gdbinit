target remote localhost:1234
symbol-file build/x86_multiboot/pip.elf
set print pretty
break resumeAsm
break *(&(__multiplexer))
continue
stepi
set $ctx=(user_ctx_t *)$eax
print/x *$ctx
