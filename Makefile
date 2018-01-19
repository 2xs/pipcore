###############################################################################
#  © Université Lille 1, The Pip Development Team (2015-2017)                 #
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
PARTITION=minimal

# Include architecture-and-platform-dependent cross-compilation toolchain
include conf/$(TARGET).mk
include conf/toolchain.mk

BUILD_DIR=build
TARGET_DIR=$(BUILD_DIR)/$(TARGET)
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
JSONS=Internal.json Services.json ServicesHandler.json
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

# Includes
CFLAGS+=-I$(SRC_DIR)/MAL
CFLAGS+=-I$(SRC_DIR)/MAL/$(TARGET)
CFLAGS+=-I$(SRC_DIR)/IAL
CFLAGS+=-I$(SRC_DIR)/IAL/$(TARGET)
CFLAGS+=-I$(SRC_DIR)/boot/$(TARGET)/include
CFLAGS+=-I$(TARGET_DIR)/

all: kernel proofs doc 

kernel: gitinfo $(TARGET_DIR) linker makefile.dep extract $(COBJ) $(AOBJ)
	$(LD) $(AOBJ) $(COBJ) $(LDFLAGS) -T$(SRC_DIR)/boot/$(TARGET)/link.ld -o $(TARGET_DIR)/meso.bin

gitinfo:
	printf "#ifndef __GIT__\n#define __GIT__\n#define GIT_REVISION \"`git rev-parse HEAD`\"\n#endif" > $(SRC_DIR)/boot/$(TARGET)/include/git.h

linker:
	$(SED) -e "s/__KERNEL_LOAD_ADDR__/$(KERNEL_ADDR)/g"           \
	       -e "s/__MULTIPLEXER_LOAD_ADDR__/$(PARTITION_ADDR)/g"   \
	       -e "s/__KERNEL_STACK_ADDR__/$(STACK_ADDR)/g"           \
	       $(SRC_DIR)/boot/$(TARGET)/link.ld.template             \
	       > $(SRC_DIR)/boot/$(TARGET)/link.ld

# Use GCC to generate rules, convert multi-lines rules to single lines, remove empty lines and use $(BUILD_DIR) as target
makefile.dep:
	$(CC) $(CFLAGS) -MM $(CSOURCES) | perl -pe 's/(\\[\r\n]+)//' | awk 'NF > 0' | $(SED) "s|^|$(TARGET_DIR)/|g" > $@

$(DIGGER):
	make -C $(DIGGER_DIR)

# Extract C code from Coq source
$(JSONS): src/model/Extraction.vo

src/model/Extraction.vo: src/model/Extraction.v
	$(COQC) $(COQOPTS) -w all $<

extract: $(DIGGER) $(TARGET_DIR) $(JSONS)
	$(DIGGER) -m Hardware -M coq_LLI                                  \
	    -m Datatypes -r Coq_true:true -r Coq_false:false -r Coq_tt:tt \
	    -m MALInternal -d :MALInternal.json                           \
	    -m MAL -d :MAL.json                                           \
	    -m ADT -m Nat                                                 \
	    -q maldefines.h                                               \
	    --ignore coq_N                                                \
	    Internal.json                                                 \
	      > $(TARGET_DIR)/Internal.c
	$(DIGGER) -m Hardware -M coq_LLI                                  \
	    -m Datatypes -r Coq_true:true -r Coq_false:false -r Coq_tt:tt \
	    -m MALInternal -d :MALInternal.json                           \
	    -m MAL -d :MAL.json                                           \
	    -m ADT -m Nat                                                 \
	    -q maldefines.h                                               \
	    --ignore coq_N                                                \
	    --header                                                      \
	    Internal.json -o $(TARGET_DIR)/Internal.h
	$(DIGGER) -m Hardware -M coq_LLI                                  \
	    -m Datatypes -r Coq_true:true -r Coq_false:false -r Coq_tt:tt \
	    -m MALInternal -d :MALInternal.json                           \
	    -m MAL -d :MAL.json                                           \
	    -m ADT -m Nat                                                 \
	    -m Internal -d :Internal.json                                 \
	    -q maldefines.h -q Internal.h                                 \
	    Services.json                                                 \
	      > $(TARGET_DIR)/Services.c
	$(DIGGER) -m Hardware -M coq_LLI                                  \
	    -m Datatypes -r Coq_true:true -r Coq_false:false -r Coq_tt:tt \
	    -m MALInternal -d :MALInternal.json                           \
	    -m MAL -d :MAL.json                                           \
	    -m ADT -m Nat                                                 \
	    -m Internal -d :Internal.json                                 \
	    -q maldefines.h -q Internal.h                                 \
		--header													  \
	    Services.json                                                 \
	      -o $(TARGET_DIR)/Services.h
	$(DIGGER) -m Hardware -M coq_LLI                                  \
	    -m Datatypes -r Coq_true:true -r Coq_false:false -r Coq_tt:tt \
	    -m MALInternal -d :MALInternal.json                           \
	    -m MAL -d :MAL.json                                           \
	    -m ADT -m Nat                                                 \
	    -q maldefines.h -q Services.h                                 \
	    --ignore coq_N                                                \
	    ServicesHandler.json                                          \
	     | $(SED) -e "s/Services_//g" > $(TARGET_DIR)/ServicesHandler.c	

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
$(addsuffix .d,$(VSOURCES)): %.v.d: %.v
	@echo COQDEP "$<"
	@$(COQDEP) $(COQOPTS) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

%.vo: %.v
	$(COQC) $(COQOPTS) $<

$(VSOURCES:.v=.glob): %.glob: %.vo

# This rule generates and builds an object file from the given partition binary
$(TARGET_DIR)/multiplexer.o: $(TARGET_DIR)/$(PARTITION).bin
	printf "section .multiplexer\n\tINCBIN \"$<\"\n" > $(TARGET_DIR)/multiplexer.s
	$(AS) $(ASFLAGS) -o $@ $(TARGET_DIR)/multiplexer.s

$(TARGET_DIR)/$(PARTITION).bin:
	cp $(SRC_DIR)/partitions/$(ARCHITECTURE)/$(PARTITION)/$(PARTITION).bin $@

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
	cp $(TARGET_DIR)/meso.bin tools/grub/boot/meso.bin
	grub-mkrescue -o $(TARGET_DIR)/meso.iso tools/grub
	@echo "Done, you can run "
	@echo "$(QEMU) -boot d -cdrom $(TARGET_DIR)/meso.iso -m 8192 -serial stdio -vga std -netdev user,id=mynet0 -device rtl8139,netdev=mynet0"
	@echo "to run the generated ISO."

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

.PHONY: all gitinfo linker extract proofs qemu test coq-enable-simulation coq-disable-simulation doc-c doc-coq doc partition grub clean mrproper clean-c clean-coq kernel gettingstarted clean-mddoc bochs
