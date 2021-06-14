#!/bin/sh
#################################################################################
#   © Université de Lille, The Pip Development Team (2015-2021)                 #
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

## The regular expression used to extract the total amount of available memory.
available_memory_regex='^MemTotal:[[:space:]]*\([^[:space:]]*\).*'

## The minimum amount of memory in KB required to compile proofs.
minimum_required_memory='8388604' # (8 GB)

## The minimum required version of tools.
as_minimum_version='2.14'
cc_minimum_version='8.3.0'
coqc_minimum_version='8.13.1'
doxygen_minimum_version='1.8.13'
gdb_minimum_version='8.2.1'
grub_mkrescue_minimum_version='2.02'
ld_minimum_version='2.31.1'
make_minimum_version='4.3'
pdflatex_minimum_version='3.14'
qemu_minimum_version='3.1.0'

## The regular expressions used to extract the version number.
as_regex_1='^NASM version \([^ ]*\).*$'
cc_regex_1='^gcc .* \([^ ]*\)$'
coqc_regex_1='^The Coq Proof Assistant, version \([^ ]*\).*$'
doxygen_regex_1='^\([^ ]*\)$'
gdb_regex_1='^GNU gdb .* \([^ ]*\)$'
grub_mkrescue_regex_1='^.*grub-mkrescue .* \([^ ]*\)$'
ld_regex_1='^GNU ld .* \([^ ]*\)$'
make_regex_1='^GNU Make \([^ ]*\).*$'
pdflatex_regex_1='^pdfTeX \([^ ]*\).*$'
qemu_regex_1='^QEMU emulator version \([^ ]*\).*$'

## The regular expressions used to check the validity of the version number.
as_regex_2='^2[.]14.*$|^2[.]1[5-9].*$|^2[.][2-9][0-9].*$|^[3-9][.].*$|^[1-9][0-9][.].*$'
cc_regex_2='^8[.][3-9].*$|^8[.][1-9][0-9].*$|^9[.].*$|^[1-9][0-9][.].*$'
coqc_regex_2='^8[.]13[.][1-2]$'
doxygen_regex_2='^1[.]8[.]1[3-9].*$|^1[.]8[.][2-9][0-9].*$|^1[.]9.*$|^1[.][1-9][0-9].*$|^[2-9][.].*$|^[1-9][0-9][.].*$'
gdb_regex_2='^8[.]2[.][1-9].*$|^8[.][3-9].*$|^8[.][1-9][0-9].*$|^9[.].*$|^[1-9][0-9][.].*$'
grub_mkrescue_regex_2='^2[.]0[2-9].*$|^2[.][1-9][0-9].*$|^[3-9][.].*$|^[1-9][0-9][.].*$'
ld_regex_2='^2[.]31[.][1-9].*$|^2[.]3[2-9].*$|^2[.][4-9][0-9].*$|^[3-9][.].*$|^[1-9][0-9][.].*$'
make_regex_2='^4[.][3-9].*$|^4[.][1-9][0-9].*$|^[5-9][.].*$|^[1-9][0-9][.].*$'
pdflatex_regex_2='^3[.]1[4-9].*$|^3[.][2-9][0-9].*$|^[4-9][.].*$|^[1-9][0-9][.].*$'
qemu_regex_2='^3[.][1-9].*$|^[4-9][.].*$|^[1-9][0-9][.].*$'

## Extract the version number of a tool.
## $1 The command that prints the tool version to stdout.
## $2 The regular expression to extract the version number.
## Returns the version number.
extract_version_number() {
    printf "%s\\n" "$( $1 2>/dev/null | sed -n -e 's/'"$2"'/\1/p' )"
}

## Check the validity of a version number.
## $1 The version number to be checked.
## $2 The regular expresion used to check the version number.
## Returns 1 if the version number is valid, 0 otherwise.
is_valid_version_number() {
    printf "%s\\n" "$1" | grep -E "$2" >/dev/null 2>&1
}

## Get the path of the tool if it has been found.
## $1 The name of the tool to be checked.
## $2 The argument to print the version of the tool to stdout.
## $3 The minimum required version of the tool.
## $4 A regular expression to extract the version number.
## $5 A regular expression to check the version number.
## Returns the path to the tool if it was found or an empty string otherwise.
get_tool_path_if_exists() {
    printf "Checking %s ... " "$1" >&2
    path=$(command -v "$1")
    while :
    do
        version=$(extract_version_number "$path $2" "$4")
        if is_valid_version_number "$version" "$5";
        then
            printf "OK (%s)\\n" "$version" >&2
            break
        elif is_valid_version_number "$version" "^.+$";
        then
            printf "\\nWARNING: %s versions below %s are untested.\\n" "$1" "$3" >&2
            printf "Would you like to provide a path to a valid %s? (y/N) " "$1" >&2
            read -r choice
            case "$choice" in
                [Yy])
                    printf "Provide a path to a valid %s.\\n> " "$1" >&2
                    read -r path
                    continue
                    ;;
                *)
                    break
                    ;;
            esac
        else
            printf "\\nWARNING: %s was not found.\\n" "$1" >&2
            printf "Would you like to provide a path to a valid %s? (y/N) " "$1" >&2
            read -r choice
            case "$choice" in
                [Yy])
                    printf "Provide a path to a valid %s.\\n> " "$1" >&2
                    read -r path
                    continue
                    ;;
                *)
                    path=""
                    break
                    ;;
            esac
        fi
    done
    printf "%s\\n" "$path"
}

## 1. Check the total amount of free memory.

printf "Checking memory ... "
available_memory=$(sed -n -e 's/'"$available_memory_regex"'/\1/p' /proc/meminfo)
if [ "$available_memory" -le "$minimum_required_memory" ];
then
    printf "\\nWARNING: pipcore required more than 8GB of memory \
in order to compile proofs ...\\n"
else
    printf "Ok\\n"
fi

## 2. Select the target architecture.

while :
do
    printf "Choose a target architecture (type \"list\" to \
list available target architectures).\\n> "
    read -r choice
    case "$choice" in
        i386)
            target="x86_multiboot"
            arch_cflags="-march=pentium -m32"
            arch_ldflags="-m elf_i386"
            arch_asflags="-f elf"
            break
            ;;
        list)
            printf "i386 (Intel 80386)\\n"
            ;;
    esac
done

## 3. Check the tool version.

as=$(get_tool_path_if_exists "nasm" "-v" \
        "$as_minimum_version" "$as_regex_1" "$as_regex_2")

cc=$(get_tool_path_if_exists "gcc" "--version" \
        "$cc_minimum_version" "$cc_regex_1" "$cc_regex_2")

coqc=$(get_tool_path_if_exists "coqc" "-v" \
        "$coqc_minimum_version" "$coqc_regex_1" "$coqc_regex_2")

doxygen=$(get_tool_path_if_exists "doxygen" "-v" \
        "$doxygen_minimum_version" "$doxygen_regex_1" "$doxygen_regex_2")

gdb=$(get_tool_path_if_exists "gdb" "-v" \
        "$gdb_minimum_version" "$gdb_regex_1" "$gdb_regex_2")

grub_mkrescue=$(get_tool_path_if_exists "grub-mkrescue" "--version" \
        "$grub_mkrescue_minimum_version" "$grub_mkrescue_regex_1" "$grub_mkrescue_regex_2")

ld=$(get_tool_path_if_exists "ld" "-v" \
        "$ld_minimum_version" "$ld_regex_1" "$ld_regex_2")

make=$(get_tool_path_if_exists "make" "-v" \
        "$make_minimum_version" "$make_regex_1" "$make_regex_2")

pdflatex=$(get_tool_path_if_exists "pdflatex" "-v" \
        "$pdflatex_minimum_version" "$pdflatex_regex_1" "$pdflatex_regex_2")

qemu=$(get_tool_path_if_exists "qemu-system-i386" "--version" \
        "$qemu_minimum_version" "$qemu_regex_1" "$qemu_regex_2")

if ! [ -z "$coqc" ];
then
    coqdirname=$(dirname "$coqc")
    coq_makefile="$coqdirname/coq_makefile"
    coqdep="$coqdirname/coqdep"
    coqdoc="$coqdirname/coqdoc"
    coqtop="$coqdirname/coqtop"
else
    coq_makefile=""
    coqdep=""
    coqdoc=""
    coqtop=""
fi

## 5. Select the partition name.

while :
do
    printf "Enter the name of the partition to build.\\n> "
    read -r partition
    case "$partition" in
        ?*)
            break
    esac
done

## 6. Generate toolchain.mk used to compile pipcore.

cat <<EOF > toolchain.mk
DIGGER_DIR=tools/digger
DIGGER=\$(DIGGER_DIR)/digger

# GNU Make
MAKE="$make"

# Coq Proof Assistant
COQ_MAKEFILE="$coq_makefile"
COQ_ENV=COQC = "$coqc" COQDEP = "$coqdep" COQDOC = "$coqdoc" COQTOP = "$coqtop"

# GNU C Compiler
CC="$cc"

# Netwide assembler
AS="$as"

# GNU Linker
LD="$ld"

# Qemu (for 32 bits architectures)
QEMU="$qemu"

# GNU Debugger
GDB="$gdb"

# Doxygen
DOXYGEN="$doxygen"

# Pdflatex
PDFLATEX="$pdflatex"

# GRUB rescue
GRUBMKRESCUE="$grub_mkrescue"

######################### Compilation options ###################

TARGET=$target
PARTITION=$partition

# Arch related options
ARCH_CFLAGS=$arch_cflags
ARCH_LDFLAGS=$arch_ldflags
ARCH_ASFLAGS=$arch_asflags

# Debug related options
DEBUG_CFLAGS=-g -DPIPDEBUG -DLOGLEVEL=TRACE

# If the DEBUG variable is set, the output binary will
# be in debug mode. Otherwise, if the DEBUG variable is
# not set, the output binary will be in released mode.
DEBUG=ENABLED

######################### Execution options ###################

GDBARGS=-iex "target remote localhost:1234" -iex "symbol-file \$(BUILD_DIR)/\$(TARGET)/\$(KERNEL_ELF)"

QEMUARGS=-cpu Haswell -m 64
QEMUARGS+=-nographic
#QEMUARGS+= -S -s
EOF
