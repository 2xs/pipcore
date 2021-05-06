#!/bin/sh
#################################################################################
#   © Université Lille 1, The Pip Development Team (2015-2021)                  #
#                                                                               #
#   This software is a computer program whose purpose is to run a minimal,      #
#   hypervisor relying on proven properties such as memory isolation.           #
#                                                                               #
#   This software is governed by the CeCILL license under French law and        #
#   abiding by the rules of distribution of free software.  You can  use,       #
#   modify and/ or redistribute the software under the terms of the CeCILL      #
#   license as circulated by CEA, CNRS and INRIA at the following URL           #
#   "http://www.cecill.info".                                                   #
#                                                                               #
#   As a counterpart to the access to the source code and  rights to copy,      #
#   modify and redistribute granted by the license, users are provided only     #
#   with a limited warranty  and the software's author,  the holder of the      #
#   economic rights,  and the successive licensors  have only  limited          #
#   liability.                                                                  #
#                                                                               #
#   In this respect, the user's attention is drawn to the risks associated      #
#   with loading,  using,  modifying and/or developing or reproducing the       #
#   software by the user in light of its specific status of free software,      #
#   that may mean  that it is complicated to manipulate,  and  that  also       #
#   therefore means  that it is reserved for developers  and  experienced       #
#   professionals having in-depth computer knowledge. Users are therefore       #
#   encouraged to load and test the software's suitability as regards their     #
#   requirements in conditions enabling the security of their systems and/or    #
#   data to be ensured and,  more generally, to use and operate it in the       #
#   same conditions as regards security.                                        #
#                                                                               #
#   The fact that you are presently reading this means that you have had        #
#   knowledge of the CeCILL license and that you accept its terms.              #
#################################################################################

printf "###################################################\\n"
printf "Pipcore Configuration Script.\\n"
printf "###################################################\\n"

# Check available RAM

printf "Checking the total amount of RAM memory available ... "
available_ram_kb=$(head -1 /proc/meminfo | sed -e 's/^MemTotal:\s*//' -n -e 's/ .*$//p')
if [ "$available_ram_kb" -le "8388604" ];
then
    printf "\\nWARNING: pipcore required more than 8GB of RAM in order to compile proofs ...\\n"
else
    printf "Ok\\n"
fi

# Check toolchain

printf "Checking GNU Make ... "
make_binary_path=$(command -v make)
while :
do
    make_version=$($make_binary_path -v 2>/dev/null | head -1 | sed -n -e 's/^GNU Make //p')
    case "$make_version" in
        4.[3-9]*|4.[1-9][0-9]*|[5-9].*|[1-9][0-9].*)
            printf "Ok (%s)\\n" "$make_version"
            break;;
        ?*)
            printf "\\nWARNING: GNU Make versions below 4.3 may not support required features.\\n"
            printf "Would you like to provide an absolute path to a valid GNU Make? (y/N) "
            read -r choice
            case "$choice" in
                [Yy])
                    printf "Provide an absolute path to a valid GNU Make: "
                    read -r make_binary_path
                    continue;;
                [Nn]|*)
                    break;;
            esac;;
        "")
            printf "\\nWARNING: Either GNU Make was not found, or it is not GNU Make.\\n"
            printf "Would you like to provide an absolute path to a valid GNU Make? (y/N) "
            read -r choice
            case "$choice" in
                [Yy])
                    printf "Provide an absolute path to a valid GNU Make: "
                    read -r make_binary_path
                    continue;;
                [Nn]|*)
                    make_binary_path="make"
                    break;;
            esac
    esac
done

printf "Checking Coq ... "
coq_binary_path=$(command -v coqc)
while :
do
    coq_version=$($coq_binary_path -v 2>/dev/null | sed -n -e 's/The Coq Proof Assistant, version \([^ ]*\).*$/\1/p')
    case "$coq_version" in
        8.13.1)
            printf "Ok (%s)\\n" "$coq_version"
            break;;
        ?*)
            printf "\\nWARNING: Coq Compiler versions below 8.13.1 are not supported.\\n"
            printf "Would you like to provide an absolute path to a valid Coq Compiler? (y/N) "
            read -r choice
            case "$choice" in
                [Yy])
                    printf "Provide an absolute path to a valid Coq Compiler: "
                    read -r coq_binary_path
                    continue;;
                [Nn]|*)
                    break;;
            esac;;
        "")
            printf "\\nWARNING: Coq Compiler was not found.\\n"
            printf "Would you like to provide an absolute path to a valid Coq Compiler? (y/N) "
            read -r choice
            case "$choice" in
                [Yy])
                    printf "Provide an absolute path to a valid Coq Compiler: "
                    read -r coq_binary_path
                    continue;;
                [Nn]|*)
                    coq_binary_path="coqc"
                    break;;
            esac
    esac
done

printf "Checking Coq Makfile ... "
coq_makefile_binary_path=$(command -v coq_makefile)
while :
do
    if [ -z "$coq_makefile_binary_path" ]; then
        printf "\\nWARNING: Coq Makefile was not found.\\n"
        printf "Would you like to provide an absolute path to a valid Coq Makfile? (y/N) "
        read -r choice
        case "$choice" in
            [Yy])
                printf "Provide an absolute path to a valid Coq Makfile: "
                read -r coq_makefile_binary_path
                continue;;
            [Nn]|*)
                coq_makefile_binary_path="coq_makefile"
                break;;
        esac
    fi
    printf "Ok\\n"
    break
done

printf "Checking GNU C Compiler ... "
gcc_binary_path=$(command -v gcc)
while :
do
    gcc_version=$($gcc_binary_path --version 2>/dev/null | head -1 | sed -n -e 's/^.* //p')
    case "$gcc_version" in
        8.[3-9]*|8.[1-9][0-9]*|9.*|[1-9][0-9].*)
            printf "Ok (%s)\\n" "$gcc_version"
            break;;
        ?*)
            printf "\\nWARNING: GNU C Compiler versions below 8.3.0 are untested.\\n"
            printf "Would you like to provide an absolute path to a valid GNU C Compiler? (y/N) "
            read -r choice
            case "$choice" in
                [Yy])
                    printf "Provide an absolute path to a valid GNU C Compiler: "
                    read -r gcc_binary_path
                    continue;;
                [Nn]|*)
                    break;;
            esac;;
        "")
            printf "\\nWARNING: GNU C Compiler was not found.\\n"
            printf "Would you like to provide an absolute path to a valid GNU C Compiler? (y/N) "
            read -r choice
            case "$choice" in
                [Yy])
                    printf "Provide an absolute path to a valid GNU C Compiler: "
                    read -r gcc_binary_path
                    continue;;
                [Nn]|*)
                    gcc_binary_path="gcc"
                    break;;
            esac
    esac
done

printf "Checking Netwide assembler ... "
nasm_binary_path=$(command -v nasm)
while :
do
    nasm_version=$($nasm_binary_path -v 2>/dev/null | sed -n -e 's/^NASM version //p')
    case "$nasm_version" in
        2.1[4-9]*|2.[2-9][0-9]*|[3-9].*|[1-9][0-9].*)
            printf "Ok (%s)\\n" "$nasm_version"
            break;;
        ?*)
            printf "\\nWARNING: Netwide assembler versions below 2.14 are untested.\\n"
            printf "Would you like to provide an absolute path to a valid Netwide assembler? (y/N) "
            read -r choice
            case "$choice" in
                [Yy])
                    printf "Provide an absolute path to a valid Netwide assembler: "
                    read -r nasm_binary_path
                    continue;;
                [Nn]|*)
                    break;;
            esac;;
        "")
            printf "\\nWARNING: Netwide assembler was not found.\\n"
            printf "Would you like to provide an absolute path to a valid Netwide assembler? (y/N) "
            read -r choice
            case "$choice" in
                [Yy])
                    printf "Provide an absolute path to a valid Netwide assembler: "
                    read -r nasm_binary_path
                    continue;;
                [Nn]|*)
                    nasm_binary_path="nasm"
                    break;;
            esac
    esac
done

printf "Checking GNU Linker ... "
ld_binary_path=$(command -v ld)
while :
do
    ld_version=$($ld_binary_path -v 2>/dev/null | sed -n -e 's/^.* //p')
    case "$ld_version" in
        2.3[1-9]*|2.[4-9][0-9]*|[3-9].*|[1-9][0-9].*)
            printf "Ok (%s)\\n" "$ld_version"
            break;;
        ?*)
            printf "\\nWARNING: GNU Linker versions below 2.31.1 are untested.\\n"
            printf "Would you like to provide an absolute path to a valid GNU Linker? (y/N) "
            read -r choice
            case "$choice" in
                [Yy])
                    printf "Provide an absolute path to a valid GNU Linker: "
                    read -r ld_binary_path
                    continue;;
                [Nn]|*)
                    break;;
            esac;;
        "")
            printf "\\nWARNING: GNU Linker was not found.\\n"
            printf "Would you like to provide an absolute path to a valid GNU Linker? (y/N) "
            read -r choice
            case "$choice" in
                [Yy])
                    printf "Provide an absolute path to a valid GNU Linker: "
                    read -r ld_binary_path
                    continue;;
                [Nn]|*)
                    ld_binary_path="ld"
                    break;;
            esac
    esac
done

printf "Checking QEMU ... "
qemu_binary_path=$(command -v qemu-system-i386)
while :
do
    qemu_version=$($qemu_binary_path --version 2>/dev/null | head -1 | sed -e 's/^QEMU emulator version //')
    case "$qemu_version" in
        3.[1-9]*|3.[2-9][0-9]*|[4-9].*|[1-9][0-9].*)
            printf "Ok (%s)\\n" "$qemu_version"
            break;;
        ?*)
            printf "\\nWARNING: QEMU versions below 3.1.0 are untested.\\n"
            printf "Would you like to provide an absolute path to a valid QEMU? (y/N) "
            read -r choice
            case "$choice" in
                [Yy])
                    printf "Provide an absolute path to a valid QEMU: "
                    read -r qemu_binary_path
                    continue;;
                [Nn]|*)
                    break;;
            esac;;
        "")
            printf "\\nWARNING: QEMU was not found.\\n"
            printf "Would you like to provide an absolute path to a valid QEMU? (y/N) "
            read -r choice
            case "$choice" in
                [Yy])
                    printf "Provide an absolute path to a valid QEMU: "
                    read -r qemu_binary_path
                    continue;;
                [Nn]|*)
                    qemu_binary_path="qemu"
                    break;;
            esac
    esac
done

printf "Checking GNU Debugger ... "
gdb_binary_path=$(command -v gdb)
while :
do
    gdb_version=$($gdb_binary_path -v 2>/dev/null | head -1 | sed -n -e 's/^.* //p')
    case "$gdb_version" in
        8.[2-9]*|8.[3-9][0-9]*|9.*|[1-9][0-9].*)
            printf "Ok (%s)\\n" "$gdb_version"
            break;;
        ?*)
            printf "\\nWARNING: GNU Debugger versions below 8.2.1 are untested.\\n"
            printf "Would you like to provide an absolute path to a valid GNU Debugger? (y/N) "
            read -r choice
            case "$choice" in
                [Yy])
                    printf "Provide an absolute path to a valid GNU Debugger: "
                    read -r gdb_binary_path
                    continue;;
                [Nn]|*)
                    break;;
            esac;;
        "")
            printf "\\nWARNING: GNU Debugger was not found.\\n"
            printf "Would you like to provide an absolute path to a valid GNU Debugger? (y/N) "
            read -r choice
            case "$choice" in
                [Yy])
                    printf "Provide an absolute path to a valid GNU Debugger: "
                    read -r gdb_binary_path
                    continue;;
                [Nn]|*)
                    gdb_binary_path="gdb"
                    break;;
            esac
    esac
done

while :
do
    printf "Choose a target architecture (type \"list\" to list available target architectures): "
    read -r choice
    case "$choice" in
        i386)
            target_architecture="x86_multiboot"
            architecture_flags="ARCH_CFLAGS=-march=pentium -m32
ARCH_LDFLAGS=-m elf_i386
ARCH_ASFLAGS=-f elf"
            break;;
        list)
            printf "i386 (Intel 80386)\\n";;
    esac
done

while :
do
    printf "Enter the name of the partition to build: "
    read -r partition_name
    case "$partition_name" in
        ?*)
            break
    esac
done

# Generate the toolchain.mk file

cat <<EOF > toolchain.mk
DIGGER_DIR=tools/digger
DIGGER=\$(DIGGER_DIR)/digger

# GNU Make
MAKE="$make_binary_path"

# Coq Proof Assistant
COQ_MAKEFILE="$coq_makefile_binary_path"
COQ="$coq_binary_path"

# GNU C Compiler
CC="$gcc_binary_path"

# Netwide assembler
AS="$nasm_binary_path"

# GNU Linker
LD="$ld_binary_path"

# Qemu (for 32 bits architectures)
QEMU="$qemu_binary_path"

# GNU Debugger
GDB="$gdb_binary_path"

######################### Compilation options ###################

TARGET=$target_architecture
PARTITION=$partition_name

# Arch related options
$architecture_flags

# Debug related options
DEBUG_CFLAGS=-g -DPIPDEBUG -DLOGLEVEL=TRACE

DEBUG=ENABLED

######################### Execution options ###################

GDBARGS=-iex "target remote localhost:1234" -iex "symbol-file \$(PARTITION).elf" 

QEMUARGS=-cpu Haswell -m 64
QEMUARGS+=-nographic -kernel

QEMU_DEBUG_ARGS=-S -s
EOF
