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

### Regular expression used to extract the total amount of available memory
available_memory_regex='^MemTotal:[[:space:]]*\([^[:space:]]*\).*'

### Minimum amount of memory in KB required to compile proofs
minimum_required_memory="8388604" # (8 GB)

### Minimum required version of commands
nasm_minimum_version="2.14"
gcc_minimum_version="8.3.0"
coq_minimum_version="8.13.1"
doxygen_minimum_version="1.8.13"
gdb_minimum_version="8.2.1"
grub_mkrescue_minimum_version="2.02"
ld_minimum_version="2.31.1"
make_minimum_version="4.3"
pdflatex_minimum_version="3.14"
qemu_minimum_version="3.1.0"

### Regular expressions used to get the version number
nasm_regex_1='^NASM version \([^ ]*\).*$'
gcc_regex_1='^gcc .* \([^ ]*\)$'
coqc_regex_1='^The Coq Proof Assistant, version \([^ ]*\).*$'
doxygen_regex_1='^\([^ ]*\)$'
gdb_regex_1='^GNU gdb .* \([^ ]*\)$'
grub_mkrescue_regex_1='^.*grub-mkrescue .* \([^ ]*\)$'
ld_regex_1='^GNU ld .* \([^ ]*\)$'
make_regex_1='^GNU Make \([^ ]*\).*$'
pdflatex_regex_1='^pdfTeX \([^ ]*\).*$'
qemu_regex_1='^QEMU emulator version \([^ ]*\).*$'

### Regular expressions used to check if the version number is correct
nasm_regex_2='^2[.]14.*$|^2[.]1[5-9].*$|^2[.][2-9][0-9].*$|^[3-9][.].*$|^[1-9][0-9][.].*$'
gcc_regex_2='^8[.][3-9].*$|^8[.][1-9][0-9].*$|^9[.].*$|^[1-9][0-9][.].*$'
coqc_regex_2='^8[.]13[.][1-2]$'
doxygen_regex_2='^1[.]8[.]1[3-9].*$|^1[.]8[.][2-9][0-9].*$|^1[.]9.*$|^1[.][1-9][0-9].*$|^[2-9][.].*$|^[1-9][0-9][.].*$'
gdb_regex_2='^8[.]2[.][1-9].*$|^8[.][3-9].*$|^8[.][1-9][0-9].*$|^9[.].*$|^[1-9][0-9][.].*$'
grub_mkrescue_regex_2='^2[.]0[2-9].*$|^2[.][1-9][0-9].*$|^[3-9][.].*$|^[1-9][0-9][.].*$'
ld_regex_2='^2[.]31[.][1-9].*$|^2[.]3[2-9].*$|^2[.][4-9][0-9].*$|^[3-9][.].*$|^[1-9][0-9][.].*$'
make_regex_2='^4[.][3-9].*$|^4[.][1-9][0-9].*$|^[5-9][.].*$|^[1-9][0-9][.].*$'
pdflatex_regex_2='^3[.]1[4-9].*$|^3[.][2-9][0-9].*$|^[4-9][.].*$|^[1-9][0-9][.].*$'
qemu_regex_2='^3[.][1-9].*$|^[4-9][.].*$|^[1-9][0-9][.].*$'

### Global variables
check_commands=
partition_name=
architecture=
target=
arch_cflags=
arch_ldflags=
arch_asflags=
nasm_path=
gcc_path=
coq_path=
coq_makefile_path=
coqc_path=
coqdep_path=
coqdoc_path=
coqtop_path=
doxygen_path=
gdb_path=
grub_mkrescue_path=
ld_path=
make_path=
pdflatex_path=
qemu_path=

### Show the usage of this script
usage() {
    printf "\
Usage: %s [ARGUMENTS]\\n\

  This configuration script aims to check the availability and the version of
  the commands required by the project.

  This script has two execution modes:

  If no arguments are given to the script, it will run in interactive mode. In
  this mode, it will first try to search for each command in the \$PATH
  environment variable. If it fails to find it or if its version is not correct,
  it will display a message asking the user if he wants to enter a path to a
  correct version of the command.

  If at least one argument is given to the script, it will run in
  non-interactive mode. By default, the arguments given to the script, with the
  exception of the \`--architecture\` and \`--partition-name\` arguments, are
  considered correct. It is the user's responsibility to provide a path to a
  correct version of the command. To change this behavior, you can use the
  \`--check-commands\` argument. In this case, the script will fail with a
  non-zero exit code if a command was not found at the specified path or if it
  does not have a correct version. The omitted arguments are empty.

  ARGUMENTS:\\n\

    --help                    Show this message and exit\\n\

    --check-commands          Fail if a command was not found at the specified
                              path or if does not have a correct version\\n\

    --architecture=<x>        The target architecture name:\\n\
                                - \`i386\`  (Intel 80386)

    --partition-name=<x>      The name of the partition to build\\n\

    --nasm-path=<x>           A path to nasm version %s or higher\\n\

    --gcc-path=<x>            A path to gcc version %s or higher\\n\

    --coq-path=<x>            A path to the directory where coq version %s or
                              higher is installed\\n\

    --doxygen-path=<x>        A path to doxygen version %s or higher\\n\

    --gdb-path=<x>            A path to gdb version %s or higher\\n\

    --grub-mkrescue-path=<x>  A path to grub-mkrescue version %s or higher\\n\

    --ld-path=<x>             A path to ld version %s or higher\\n\

    --make-path=<x>           A path to make version %s or higher\\n\

    --pdflatex-path=<x>       A path to pdflatex version %s or higher\\n\

    --qemu-path=<x>           A path to qemu version %s or higher\\n\

" \
"$0" \
"$nasm_minimum_version" \
"$gcc_minimum_version" \
"$coq_minimum_version" \
"$doxygen_minimum_version" \
"$gdb_minimum_version" \
"$grub_mkrescue_minimum_version" \
"$ld_minimum_version" \
"$make_minimum_version" \
"$pdflatex_minimum_version" \
"$qemu_minimum_version"
}

### Generate the toolchain.mk file
generate_toolchain() {
cat <<EOF > toolchain.mk
DIGGER_DIR=tools/digger
DIGGER=\$(DIGGER_DIR)/digger

# GNU Make
MAKE="$make_path"

# Coq Proof Assistant
COQ_MAKEFILE="$coq_makefile_path"
COQ_ENV  = COQC = "$coqc_path"
COQ_ENV += COQDEP = "$coqdep_path"
COQ_ENV += COQDOC = "$coqdoc_path"
COQ_ENV += COQTOP = "$coqtop_path"

# GNU C Compiler
CC="$gcc_path"

# Netwide assembler
AS="$nasm_path"

# GNU Linker
LD="$ld_path"

# Qemu (for 32 bits architectures)
QEMU="$qemu_path"

# GNU Debugger
GDB="$gdb_path"

# Doxygen
DOXYGEN="$doxygen_path"

# Pdflatex
PDFLATEX="$pdflatex_path"

# GRUB rescue
GRUBMKRESCUE="$grub_mkrescue_path"

################# Compilation options #################

TARGET=$target
PARTITION=$partition_name

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

################## Execution options ##################

GDBARGS  = -iex "target remote localhost:1234"
GDBARGS += -iex "symbol-file \$(BUILD_DIR)/\$(TARGET)/\$(KERNEL_ELF)"

QEMUARGS=-cpu Haswell -m 64
QEMUARGS+=-nographic
#QEMUARGS+= -S -s
EOF
}

### Parse arguments provided to the script
### $@ A space-separated list of all arguments
parse_arguments() {
    for argument in "$@"
    do
        value=${argument#*=}
        flag=${argument%=*}

        case $flag in
            --help)
                usage && exit 0
                ;;
            --check-commands)
                check_commands=1
                ;;
            --architecture)
                architecture=$value
                ;;
            --partition-name)
                partition_name=$value
                ;;
            --nasm-path)
                nasm_path=$value
                ;;
            --gcc-path)
                gcc_path=$value
                ;;
            --coq-path)
                coq_path=$value
                ;;
            --doxygen-path)
                doxygen_path=$value
                ;;
            --gdb-path)
                gdb_path=$value
                ;;
            --grub-mkrescue-path)
                grub_mkrescue_path=$value
                ;;
            --ld-path)
                ld_path=$value
                ;;
            --make-path)
                make_path=$value
                ;;
            --pdflatex-path)
                pdflatex_path=$value
                ;;
            --qemu-path)
                qemu_path=$value
                ;;
        esac
    done
}

### Get the version number of the command from stdout
### $1 Command to execute to get version from stdout
### $2 Regular expression used to get the version number from stdout
### Returns 0 if the version number is set, 1 otherwise
command_get_version_number() {
    version_number="$( $1 2>/dev/null | sed -n -e 's/'"$2"'/\1/p' )"
    [ -z "$version_number" ] && retval=1 || retval=0
    printf "%s\\n" "$version_number"
    return $retval
}

### Check if the version number of the command is correct
### $1 Version number of the command
### $2 Regular expression used to check the version number
### Returns 0 if the version number is correct, 1 otherwise
command_is_correct_version() {
    printf "%s\\n" "$1" | grep -E "$2" >/dev/null 2>&1
}

### Check the version of a command from stdout
### $1 Command to execute to get version from stdout
### $2 Option to get version from stdout
### $3 Regular expression used to get the version number from stdout
### $4 Regular expression used to check the version number
### Returns 0 if the version of the command is correct, 1 if the command was
### not found at the specified path, 2 if the command has not a correct version
command_check_version() {
    version_number=$(command_get_version_number "$1 $2" "$3") || return 1
    command_is_correct_version "$version_number" "$4" || return 2
    return 0
}

### Check the commands interactively
### $1 Command to execute to get version from stdout
### $2 Option to get version from stdout
### $3 Minimum version of the command
### $4 Regular expression used to get the version number from stdout
### $5 Regular expression used to check the version number
interactive_command_check() {
    printf "Checking %s ... " "$1" >&2
    command_path=$(command -v "$1")
    while :
    do
        command_check_version "$command_path" "$2" "$4" "$5"
        case "$?" in
            0)
                printf "OK (>= %s)\\n" "$3" >&2
                break
                ;;
            1)
                printf "KO\\nWARNING: %s was not found.\\n" "$1" >&2
                printf "Would you like to provide a path to a correct %s? (y/N) " "$1" >&2
                read -r choice
                case "$choice" in
                    [Yy])
                        printf "Provide a path to a correct %s.\\n> " "$1" >&2
                        read -r command_path
                        continue
                        ;;
                    *)
                        command_path=""
                        break
                        ;;
                esac
                ;;
            2)
                printf "KO (< %s)\\nWARNING: %s versions below %s are untested.\\n" "$3" "$1" "$3" >&2
                printf "Would you like to provide a path to a correct %s? (y/N) " "$1" >&2
                read -r choice
                case "$choice" in
                    [Yy])
                        printf "Provide a path to a correct %s.\\n> " "$1" >&2
                        read -r command_path
                        continue
                        ;;
                    *)
                        break
                        ;;
                esac
        esac
    done
    printf "%s\\n" "$command_path"
}

### Run the script in interactive mode because no arguments have been provided
interactive_mode() {
    # Check the total amount of free memory
    printf "Checking memory ... "
    available_memory=$(sed -n -e 's/'"$available_memory_regex"'/\1/p' /proc/meminfo)
    if [ "$available_memory" -le "$minimum_required_memory" ]
    then
        printf "\\nWARNING: pipcore required more than 8GB of memory in order to compile proofs ...\\n"
    else
        printf "OK\\n"
    fi

    # Select the target architecture
    while :
    do
        printf "Choose a target architecture (type \"?\" to see target list).\\n> "
        read -r architecture
        case "$architecture" in
            i386)
                target="x86_multiboot"
                arch_cflags="-march=pentium -m32"
                arch_ldflags="-m elf_i386"
                arch_asflags="-f elf"
                break
                ;;
            \?)
                printf "i386  (Intel 80386)\\n"
        esac
    done

    # Check the command version
    nasm_path=$(interactive_command_check "nasm" "-v" \
        "$nasm_minimum_version" "$nasm_regex_1" "$nasm_regex_2")

    gcc_path=$(interactive_command_check "gcc" "--version" \
        "$gcc_minimum_version" "$gcc_regex_1" "$gcc_regex_2")

    coqc_path=$(interactive_command_check "coqc" "-v" \
        "$coq_minimum_version" "$coqc_regex_1" "$coqc_regex_2")

    doxygen_path=$(interactive_command_check "doxygen" "-v" \
        "$doxygen_minimum_version" "$doxygen_regex_1" "$doxygen_regex_2")

    gdb_path=$(interactive_command_check "gdb" "-v" \
        "$gdb_minimum_version" "$gdb_regex_1" "$gdb_regex_2")

    grub_mkrescue_path=$(interactive_command_check "grub-mkrescue" \
        "--version" "$grub_mkrescue_minimum_version" "$grub_mkrescue_regex_1" \
        "$grub_mkrescue_regex_2")

    ld_path=$(interactive_command_check "ld" "-v" "$ld_minimum_version" \
        "$ld_regex_1" "$ld_regex_2")

    make_path=$(interactive_command_check "make" "-v" \
        "$make_minimum_version" "$make_regex_1" "$make_regex_2")

    pdflatex_path=$(interactive_command_check "pdflatex" "-v" \
        "$pdflatex_minimum_version" "$pdflatex_regex_1" "$pdflatex_regex_2")

    qemu_path=$(interactive_command_check "qemu-system-$architecture" "--version" \
        "$qemu_minimum_version" "$qemu_regex_1" "$qemu_regex_2")

    if [ ! -z "$coqc_path" ]
    then
        coq_path=$(dirname "$coqc_path")
        coq_makefile_path="$coq_path/coq_makefile"
        coqdep_path="$coq_path/coqdep"
        coqdoc_path="$coq_path/coqdoc"
        coqtop_path="$coq_path/coqtop"
    else
        coq_makefile_path=
        coqdep_path=
        coqdoc_path=
        coqtop_path=
    fi

    # Select the partition to build
    printf "Enter the name of the partition to build.\\n> "
    read -r partition_name
    while [ ! -d "src/arch/$target/partitions/$partition_name" ]; do
        printf "WARNING: the \"%s\" partition directory was not found...\\n" "$partition_name"
        printf "Enter the name of the partition to build.\\n> "
        read -r partition_name
    done

    # Generate the toolchain.mk file.
    generate_toolchain

    return 0
}

### Run the script in non-interactive mode because arguments have been provided
non_interactive_mode() {
    # Parse command line arguments
    parse_arguments "$@"

    # Fail if the architecture name is unknown
    case "$architecture" in
        i386)
            target="x86_multiboot"
            arch_cflags="-march=pentium -m32"
            arch_ldflags="-m elf_i386"
            arch_asflags="-f elf"
            ;;
        *)
            return 1
    esac

    # Set the coq binary paths if the `--coq-path` flag is set
    if [ ! -z "$coq_path" ]
    then
        coq_makefile_path="$coq_path/coq_makefile"
        coqdep_path="$coq_path/coqdep"
        coqdoc_path="$coq_path/coqdoc"
        coqtop_path="$coq_path/coqtop"
        coqc_path="$coq_path/coqc"
    fi

    # Check the command version if the `--check-commands` flag is set
    if [ ! -z "$check_commands" ]
    then
        command_check_version "$nasm_path" "-v" "$nasm_regex_1" \
            "$nasm_regex_2" || return 1

        command_check_version "$gcc_path" "--version" "$gcc_regex_1" \
            "$gcc_regex_2" || return 1

        command_check_version "$coqc_path" "-v" "$coqc_regex_1" \
            "$coqc_regex_2" || return 1

        command_check_version "$doxygen_path" "-v" "$doxygen_regex_1" \
            "$doxygen_regex_2" || return 1

        command_check_version "$gdb_path" "-v" "$gdb_regex_1" \
            "$gdb_regex_2" || return 1

        command_check_version "$grub_mkrescue_path" "--version" \
            "$grub_mkrescue_regex_1" "$grub_mkrescue_regex_2" || return 1

        command_check_version "$ld_path" "-v" "$ld_regex_1" \
            "$ld_regex_2" || return 1

        command_check_version "$make_path" "-v" "$make_regex_1" \
            "$make_regex_2" || return 1

        command_check_version "$pdflatex_path" "-v" "$pdflatex_regex_1" \
            "$pdflatex_regex_2" || return 1

        command_check_version "$qemu_path" "--version" "$qemu_regex_1" \
            "$qemu_regex_2" || return 1
    fi

    # Exit if the partition name directory was not found in the given target
    [ -d "src/arch/$target/partitions/$partition_name" ] || return 1

    # Generate the toolchain.mk file.
    generate_toolchain

    return 0
}

### Entry point of the script
main() {
    if [ "$#" -gt 0 ]
    then
        non_interactive_mode "$@"
    else
        interactive_mode
    fi

    exit $?
}

main "$@"
