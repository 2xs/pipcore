
###############################################################################
#  © Université Lille 1, The Pip Development Team (2015-2016)                 #
#                                                                             #
#  This software is a computer program whose purpose is to run a minimal,     #
#  hypervisor relying on proven properties such as memory isolation.          #
#                                                                             #
#  This software is governed by the CeCILL license under French law and       #
#  abiding by the rules of distribution of free software.  You can  use,      #
#  modify and/ or redistribute the software under the terms of the CeCILL     #
#  license as circulated by CEA, CNRS and INRIA at the following URL          #
#  "http://www.cecill.info".                                                  #
#                                                                             #
#  As a counterpart to the access to the source code and  rights to copy,     #
#  modify and redistribute granted by the license, users are provided only    #
#  with a limited warranty  and the software's author,  the holder of the     #
#  economic rights,  and the successive licensors  have only  limited         #
#  liability.                                                                 #
#                                                                             #
#  In this respect, the user's attention is drawn to the risks associated     #
#  with loading,  using,  modifying and/or developing or reproducing the      #
#  software by the user in light of its specific status of free software,     #
#  that may mean  that it is complicated to manipulate,  and  that  also      #
#  therefore means  that it is reserved for developers  and  experienced      #
#  professionals having in-depth computer knowledge. Users are therefore      #
#  encouraged to load and test the software's suitability as regards their    #
#  requirements in conditions enabling the security of their systems and/or   #
#  data to be ensured and,  more generally, to use and operate it in the      #
#  same conditions as regards security.                                       #
#                                                                             #
#  The fact that you are presently reading this means that you have had       #
#  knowledge of the CeCILL license and that you accept its terms.             #
###############################################################################

# This file is included by the main Makefile, located in Pip's root directory.

UNAME_S := $(shell uname -s)

# Use /usr/bin packages in Linux, MacPorts in Darwin
ifeq ($(UNAME_S),Linux)
AS=nasm
CC=gcc
LD=ld
AR=ar
QEMU=qemu-system-i386
GDB=gdb
EXTRACTOR=tools/extractor/Extractor.Linux64
endif
ifeq ($(UNAME_S),Darwin)
AS=/opt/local/bin/nasm
CC=/opt/local/bin/i386-elf-gcc
LD=/opt/local/bin/i386-elf-ld
AR=/opt/local/bin/i386-elf-ar
#QEMU=/opt/local/bin/qemu-system-i386
QEMU=~/QEMUDebug/bin/qemu-system-i386
GDB=i386-elf-gdb
EXTRACTOR=tools/extractor/Extractor.OSX
endif

GDBARGS=-iex "target remote localhost:1234" -iex "symbol-file $(BUILD_DIR)/$(TARGET)/meso.bin" 

QEMUARGS=-kernel $(BUILD_DIR)/$(TARGET)/meso.bin -serial stdio -m 1024 -vga std -net nic,model=rtl8139 -net dump,file=./netdump.pcap -net user 
#QEMUARGS=-kernel $(BUILD_DIR)/$(TARGET)/meso.bin -serial stdio -m 1024 -vga std -netdev user,id=mynet0 -device rtl8139,netdev=mynet0,mac=FF:CA:FE:CA:FE:FF

LIBGCC=/usr/lib/gcc/x86_64-linux-gnu/4.9/32/

ASFLAGS=-felf
CFLAGS=-m32 -Wall -W -Werror -nostdlib -fno-builtin -fno-stack-protector -std=gnu99 -ffreestanding -c -g -Wno-unused-variable -trigraphs -Wno-trigraphs -march=pentium -Wno-unused-but-set-variable -DPIPDEBUG -Wno-unused-parameter
LDFLAGS=-L$(LIBGCC) -melf_i386 -lgcc 
PLATFORM=galileo
ARCHITECTURE=x86
