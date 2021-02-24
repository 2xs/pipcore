###############################################################################
#  © Université Lille 1, The Pip Development Team (2015-2018)                 #
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

# Default values
KERNEL_ADDR=0x100000
PARTITION_ADDR=0x700000
STACK_ADDR=0x300000
TARGET=x86_multiboot
PARTITION=nullpartition

LOGLEVEL=TRACE

# Include architecture-and-platform-dependent cross-compilation toolchain
include conf/$(TARGET).mk
include conf/toolchain.mk

BUILD_DIR=build
TARGET_DIR=$(BUILD_DIR)/$(TARGET)
KERNEL_BASENAME=pip
KERNEL_ISO=$(KERNEL_BASENAME).iso
KERNEL_ELF=$(KERNEL_BASENAME).elf
KERNEL_BIN=$(KERNEL_BASENAME).bin
SRC_DIR=src
PROOF_DIR=proof

DIGGER_DIR=tools/digger
DIGGER=$(DIGGER_DIR)/digger

COQDEP=coqdep -c
COQC=coqc -q
COQDOC=coqdoc -toc -interpolate -utf8 -html

UNAME_S := $(shell uname -s)

# Doxygen
DOC=doxygen
DOCFILE=doc/doxygen.conf

# Coq Sources
COQCODEDIRS=$(SRC_DIR)/core $(SRC_DIR)/model
COQPROOFDIRS=$(PROOF_DIR) $(PROOF_DIR)/invariants
VCODESOURCES=$(foreach dir, ${COQCODEDIRS}, $(wildcard $(dir)/*.v))
VPROOFSOURCES=$(foreach dir, ${COQPROOFDIRS}, $(wildcard $(dir)/*.v))
VSOURCES=$(VCODESOURCES) $(VPROOFSOURCES)
VOBJECTS=$(VSOURCES:.v=.vo)

# JSON files extracted from Coq
JSONS=Internal.json Services.json
EXTRACTEDCSOURCES=$(addprefix $(TARGET_DIR)/, $(JSONS:.json=.c))

# Coq options
COQOPTS=$(shell cat _CoqProject)

# C and ASM sources
CSOURCES=$(wildcard $(SRC_DIR)/boot/$(TARGET)/*.c)
CSOURCES+=$(wildcard $(SRC_DIR)/MAL/$(TARGET)/*.c)
CSOURCES+=$(wildcard $(SRC_DIR)/IAL/$(TARGET)/*.c)

FULLCSOURCES=$(CSOURCES)
FULLCSOURCES+=$(EXTRACTEDCSOURCES)

ASOURCES=$(wildcard $(SRC_DIR)/boot/$(TARGET)/*.s)
ASOURCES+=$(wildcard $(SRC_DIR)/IAL/$(TARGET)/*.s)

# Generate the subsequent list of objects
COBJ=$(FULLCSOURCES:.c=.o)
AOBJ=$(ASOURCES:.s=.o)
COBJ+=$(TARGET_DIR)/multiplexer.o

# And tamper with it
COBJ:=$(patsubst %,$(TARGET_DIR)/%, $(notdir $(COBJ)))
AOBJ:=$(patsubst %,$(TARGET_DIR)/%, $(notdir $(AOBJ)))

LINKSCRIPT := $(SRC_DIR)/boot/$(TARGET)/link.ld

# Includes
CFLAGS+=-I$(SRC_DIR)/MAL
CFLAGS+=-I$(SRC_DIR)/MAL/$(TARGET)
CFLAGS+=-I$(SRC_DIR)/IAL
CFLAGS+=-I$(SRC_DIR)/IAL/$(TARGET)
CFLAGS+=-I$(SRC_DIR)/boot/$(TARGET)/include
CFLAGS+=-I$(TARGET_DIR)/
CFLAGS+=-DLOGLEVEL=$(LOGLEVEL)
CFLAGS+=-DGIT_REVISION='"$(shell git rev-parse @)"'

all: $(TARGET_DIR)/$(KERNEL_ELF) proofs doc

kernel: $(TARGET_DIR)/$(KERNEL_ELF)

$(TARGET_DIR)/$(KERNEL_ELF): $(TARGET_DIR) $(LINKSCRIPT) makefile.dep $(COBJ) $(AOBJ)
	$(LD) $(AOBJ) $(COBJ) $(LDFLAGS) -T$(SRC_DIR)/boot/$(TARGET)/link.ld -o $@

linker: $(LINKSCRIPT)

$(LINKSCRIPT): $(LINKSCRIPT).template
	$(SED) -e "s/__KERNEL_LOAD_ADDR__/$(KERNEL_ADDR)/g"           \
	       -e "s/__MULTIPLEXER_LOAD_ADDR__/$(PARTITION_ADDR)/g"   \
	       -e "s/__KERNEL_STACK_ADDR__/$(STACK_ADDR)/g"           \
	       $< > $@

makefile.dep:
	$(CC) $(CFLAGS) -MM -MG $(CSOURCES) | $(SED) -e '/:/s|^|$(TARGET_DIR)/|' -e 's|Internal.h|$(TARGET_DIR)\/Internal.h|g' > $@

$(DIGGER):
	make -C $(DIGGER_DIR)

# Extract C code from Coq source
src/model/Extraction.vo $(JSONS): src/model/Extraction.v
	$(COQC) $(COQOPTS) -w all -w -extraction $<

extract: $(EXTRACTEDCSOURCES)

DIGGERFLAGS := -m Hardware -M coq_LLI
DIGGERFLAGS += -m Datatypes -r Coq_true:true -r Coq_false:false -r Coq_tt:tt
DIGGERFLAGS += -m MALInternal -d :MALInternal.json
DIGGERFLAGS += -m MAL -d :MAL.json
DIGGERFLAGS += -m IAL -d :IAL.json
DIGGERFLAGS += -m ADT -m Nat
DIGGERFLAGS += -q maldefines.h

$(TARGET_DIR)/Internal.c: Internal.json $(DIGGER) $(TARGET_DIR)
	$(DIGGER) $(DIGGERFLAGS) --ignore coq_N -q yield_c.h $< -o $@

$(TARGET_DIR)/Internal.h: Internal.json $(DIGGER) $(TARGET_DIR)
	$(DIGGER) $(DIGGERFLAGS) --ignore coq_N --header $< -o $@

$(TARGET_DIR)/Services.c: Services.json $(DIGGER) $(TARGET_DIR)/Internal.h
	$(DIGGER) $(DIGGERFLAGS) -m Internal -d :Internal.json -q Internal.h $< -o $@

proofs: $(VOBJECTS)

# Generate build directory
$(TARGET_DIR):
	mkdir -p $@

include makefile.dep
-include $(addsuffix .d,$(VSOURCES))

# Build boot assembly files
$(TARGET_DIR)/%.o: $(SRC_DIR)/boot/$(TARGET)/%.s
	$(AS) $(ASFLAGS) $< -o $@

# Build boot C files
$(TARGET_DIR)/%.o: $(SRC_DIR)/boot/$(TARGET)/%.c
	$(CC) $(CFLAGS) $< -o $@

$(TARGET_DIR)/%.o: $(SRC_DIR)/MAL/$(TARGET)/%.c
	$(CC) $(CFLAGS) $< -o $@

$(TARGET_DIR)/%.o: $(SRC_DIR)/IAL/$(TARGET)/%.c
	$(CC) $(CFLAGS) $< -o $@

$(TARGET_DIR)/%.o: $(SRC_DIR)/IAL/$(TARGET)/%.s
	$(AS) $(ASFLAGS) $< -o $@

# Implicit rules for Coq source files
$(addsuffix .d,$(filter-out src/model/Extraction.v,$(VSOURCES))): %.v.d: %.v
	$(COQDEP) $(COQOPTS) "$<" > "$@"

src/model/Extraction.v.d: src/model/Extraction.v
	$(COQDEP) $(COQOPTS) "$<" | $(SED) 's/Extraction.vo/Extraction.vo Internal.json Services.json/' > "$@"

%.vo: %.v
	$(COQC) $(COQOPTS) $<

$(VSOURCES:.v=.glob): %.glob: %.vo

# This rule generates and builds an object file from the given partition binary
$(TARGET_DIR)/multiplexer.o: $(TARGET_DIR)/$(PARTITION).bin
	printf "section .multiplexer\n\tINCBIN \"$<\"\n" > $(TARGET_DIR)/multiplexer.s
	$(AS) $(ASFLAGS) -o $@ $(TARGET_DIR)/multiplexer.s

$(TARGET_DIR)/$(PARTITION).bin:
	@if test "$(PARTITION)" = nullpartition; then                                        \
		echo "Warning: using a dummy empty root partition to build Pip" ;           \
		echo "  You should create a real partition and run" ;                       \
		echo "    make PARTITION=YourPartition ..." ;                               \
		echo "  to get a useful kernel image" ;                                     \
		touch $@ ;                                                                  \
	else                                                                                \
		cp $(SRC_DIR)/partitions/$(ARCHITECTURE)/$(PARTITION)/$(PARTITION).bin $@ ; \
	fi

gdb:
	gdb $(GDBARGS)

qemu:
	$(QEMU) $(QEMUARGS)

test:
	cd tests/MAL && make TARGET=$(TARGET) all

coq-enable-simulation:
	$(SED) -i                                                                            \
	       -e 's/^\( *\)(\* *BEGIN *SIMULATION *$$/\1(* BEGIN SIMULATION *)/'            \
	       -e 's/^\( *\)   END *SIMULATION *\*) *$$/\1(* END SIMULATION *)/'             \
	       -e 's/^\( *\)(\* *BEGIN *NOT *SIMULATION *\*) *$$/\1(* BEGIN NOT SIMULATION/' \
	       -e 's/^\( *\)(\* *END *NOT *SIMULATION *\*) *$$/\1   END NOT SIMULATION *)/'  \
	    $(VSOURCES)

coq-disable-simulation:
	$(SED) -i                                                                            \
	       -e 's/^\( *\)(\* *BEGIN *NOT *SIMULATION *$$/\1(* BEGIN NOT SIMULATION *)/'   \
	       -e 's/^\( *\)   END *NOT *SIMULATION *\*) *$$/\1(* END NOT SIMULATION *)/'    \
	       -e 's/^\( *\)(\* *BEGIN *SIMULATION *\*) *$$/\1(* BEGIN SIMULATION/'          \
	       -e 's/^\( *\)(\* *END *SIMULATION *\*) *$$/\1   END SIMULATION *)/'           \
	    $(VSOURCES)

doc: doc-c doc-coq gettingstarted doc/Readme.html doc/PipInternals.html

doc-c:
	cd doc && doxygen doxygen.conf

gettingstarted: 
	cd doc/GettingStarted && pdflatex GettingStarted.tex

doc-coq: $(VSOURCES) $(VSOURCES:.v=.glob)
	mkdir -p doc/coq-doc
	$(COQDOC) $(COQOPTS) -d doc/coq-doc $(VSOURCES)

coqwc:
	coqwc $(VSOURCES)

partition:
	rm -f $(TARGET_DIR)/$(PARTITION).bin
	make -C $(SRC_DIR)/partitions/$(ARCHITECTURE)/$(PARTITION)

grub:
	cp $(TARGET_DIR)/$(KERNEL_ELF) tools/grub/boot/$(KERNEL_ELF)
	grub-mkrescue -o $(TARGET_DIR)/$(KERNEL_ISO) tools/grub

update-headers:
	find -\( -name \*.[cvhsS] -o -name \*.hs -o -name \*.ld -o -name \*.ld.template -o -name Makefile -o -name \*.mk -o -name doxygen.conf -\) -print0 | xargs -0 headache -c tools/headache.conf -h tools/copyright_header

clean: clean-c clean-coq

clean-coq:
	rm -f Internal.h *.json
	rm -f $(VOBJECTS) $(VSOURCES:.v=.v.d) $(VSOURCES:.v=.glob)

clean-c:
	rm -rf $(TARGET_DIR)/

clean-mddoc:
	rm -f doc/*.html

mrproper: clean-c clean-coq
	rm -rf $(BUILD_DIR)
	rm -f makefile.dep makefile.autocoq

doc/%.html: %.md
	cat doc/mdtemplate.header > $@
	$(SED) -i -e "s/###TITLE###/$(basename $<)/g" $@
	cat $< >> $@
	cat doc/mdtemplate.footer >> $@

bochs: grub
	rm -f bochscom
	mkfifo bochscom
	cat bochscom &
	bochs -q

.PHONY: all gitinfo linker extract proofs qemu test coq-enable-simulation
.PHONY: coq-disable-simulation doc-c doc-coq doc partition grub clean mrproper
.PHONY: clean-c clean-coq kernel gettingstarted clean-mddoc bochs
