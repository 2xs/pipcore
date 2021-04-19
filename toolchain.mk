DIGGER_DIR=tools/digger
DIGGER=$(DIGGER_DIR)/digger

# GNU Make
MAKE=make

# Coq Proof Assistant
COQ_MAKEFILE=coq_makefile
COQ=coq

# GNU C Compiler
CC=gcc

# Netwide assembler
NASM=nasm

# GNU Linker
LD=ld

# Qemu (for 32 bits architectures)
QEMU=qemu-system-i386

# GNU Debugger
GDB=gdb

######################### Compilation options ###################

TARGET=x86_multiboot
PARTITION=minimal

CFLAGS=-m32 -Wall -W -Wextra -Werror -nostdlib -fno-builtin -std=gnu99 -ffreestanding -c -g -Wno-unused-variable -trigraphs -Wno-trigraphs -march=pentium -Wno-unused-but-set-variable -DPIPDEBUG -Wno-unused-parameter -fno-stack-protector -fno-pic -no-pie -DLOGLEVEL=TRACE

NASMFLAGS=-f elf
LDFLAGS=-m elf_i386


######################### Execution options ###################


GDBARGS=-x gdbinit # -iex "target remote localhost:1234" -iex "symbol-file $(BUILD_DIR)/$(TARGET)/$(KERNEL_ELF)" 

QEMUARGS=-cpu Haswell -m 64
QEMUARGS+=-nographic -kernel
#QEMUARGS+= -S -s


