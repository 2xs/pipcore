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
AS=nasm

# GNU Linker
LD=ld

# Qemu (for 32 bits architectures)
QEMU=qemu-system-i386

# GNU Debugger
GDB=gdb

######################### Compilation options ###################

TARGET=x86_multiboot
PARTITION=minimal

# Arch related options
ARCH_CFLAGS=-march=pentium -m32
ARCH_LDFLAGS=-m elf_i386
ARCH_ASFLAGS=-f elf

# Debug related options
DEBUG_CFLAGS=-g -DPIPDEBUG -DLOGLEVEL=TRACE

DEBUG=ENABLED

######################### Execution options ###################


GDBARGS=-iex "target remote localhost:1234" -iex "symbol-file $(PARTITION).elf"

QEMUARGS=-cpu Haswell -m 64
QEMUARGS+=-nographic -kernel

QEMU_DEBUG_ARGS= -S -s
