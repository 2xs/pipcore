target remote localhost:1234
symbol-file build/x86mp/meso.bin
b *0x10031e
command
    printf "-> System call %d, handler at %x\n",$ebx,$ecx
    continue
end
c
