###############################################################################
#  © Université de Lille, The Pip Development Team (2015-2021)                #
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

include toolchain.mk

# Default tools
CAT := cat
SED := sed
COQC := coqc
COQDEP := coqdep

CFLAGS=-Wall -Wextra
# -Wno-unused-variable -Wno-unused-parameter -Wno-unused-but-set-variable
CFLAGS+=-std=gnu99

# Bare metal C code, do not rely on standard library
CFLAGS+=-nostdlib -fno-builtin -ffreestanding
# No position independent code / executable
CFLAGS+=-fno-stack-protector -fno-pic

CFLAGS+=$(ARCH_CFLAGS)
ASFLAGS=$(ARCH_ASFLAGS)
LDFLAGS=$(ARCH_LDFLAGS)

# Enable debug symbols and logs
CFLAGS+=$(if $(DEBUG), $(DEBUG_CFLAGS))

COQFLAGS := $(shell $(CAT) _CoqProject)
COQCFLAGS := $(COQFLAGS) -w all,-nonprimitive-projection-syntax
COQCEXTRFLAGS := $(shell $(SED) 's/-[RQ]  */&..\//g' _CoqProject) -w all,-extraction

#####################################################################
##                      Directory variables                        ##
#####################################################################

SRC_DIR=src
GENERATED_FILES_DIR=generated
DOC_DIR=doc
C_DOC_DIR=$(DOC_DIR)/c
COQ_DOC_DIR=$(DOC_DIR)/coq

########################## Coq related dirs #########################

COQ_CORE_DIR=$(SRC_DIR)/core
COQ_MODEL_DIR=$(SRC_DIR)/model
COQ_EXTRACTION_DIR=$(SRC_DIR)/extraction

COQ_PROOF_DIR=proof
COQ_INVARIANTS_DIR=$(COQ_PROOF_DIR)/invariants

########################### C related dirs ##########################

# Architecture agnostic C dirs
C_MODEL_INTERFACE_INCLUDE_DIR=$(SRC_DIR)/interface

# Architecture dependent C dirs
ARCH_DEPENDENT_DIR=$(SRC_DIR)/arch
C_SRC_TARGET_DIR=$(ARCH_DEPENDENT_DIR)/$(TARGET)

C_TARGET_MAL_DIR=$(C_SRC_TARGET_DIR)/MAL
C_TARGET_MAL_INCLUDE_DIR=$(C_TARGET_MAL_DIR)/include

C_TARGET_BOOT_DIR=$(C_SRC_TARGET_DIR)/boot
C_TARGET_BOOT_INCLUDE_DIR=$(C_TARGET_BOOT_DIR)/include

C_GENERATED_SRC_DIR=$(GENERATED_FILES_DIR)
C_GENERATED_HEADERS_DIR=$(GENERATED_FILES_DIR)

TARGET_PARTITION_DIR=$(C_SRC_TARGET_DIR)/partitions
GENERATED_PARTITION_OBJ_DIR=$(TARGET_PARTITION_DIR)

#####################################################################
##                        Files variables                          ##
#####################################################################

############################ C files ################################

C_GENERATED_SRC=$(C_GENERATED_SRC_DIR)/Services.c $(C_GENERATED_SRC_DIR)/Internal.c
C_TARGET_BOOT_SRC=$(wildcard $(C_TARGET_BOOT_DIR)/*.c)
C_TARGET_MAL_SRC=$(wildcard $(C_TARGET_MAL_DIR)/*.c)
AS_TARGET_BOOT_SRC=$(wildcard $(C_TARGET_BOOT_DIR)/*.s)
AS_ROOTPART_BIN_WRAPPER_SRC=$(C_SRC_TARGET_DIR)/rootpart_bin_wrapper.s

C_GENERATED_HEADERS=$(C_GENERATED_HEADERS_DIR)/Internal.h
C_MODEL_INTERFACE_HEADERS=$(wildcard $(C_MODEL_INTERFACE_INCLUDE_DIR)/*.h)
C_TARGET_MAL_HEADERS=$(wildcard $(C_TARGET_MAL_INCLUDE_DIR)/*.h)
C_TARGET_BOOT_HEADERS=$(wildcard $(C_TARGET_BOOT_INCLUDE_DIR)/*.h)

C_GENERATED_OBJ=$(C_GENERATED_SRC:.c=.o)
C_TARGET_BOOT_OBJ=$(C_TARGET_BOOT_SRC:.c=.o)
C_TARGET_MAL_OBJ=$(C_TARGET_MAL_SRC:.c=.o)
AS_TARGET_BOOT_OBJ=$(AS_TARGET_BOOT_SRC:.s=.o)
AS_ROOTPART_BIN_WRAPPER_OBJ=$(GENERATED_PARTITION_OBJ_DIR)/$(PARTITION).o

########################### Coq files ###############################

# Coq source files
COQ_SRC_FILES=$(foreach dir, $(COQ_CORE_DIR)\
	                     $(COQ_MODEL_DIR)\
	                   , $(wildcard $(dir)/*.v)\
               )

# Coq file needed for extraction
COQ_EXTRACTION_FILES=$(wildcard $(COQ_EXTRACTION_DIR)/*.v)

# Coq proof files
COQ_PROOF_FILES=$(foreach dir, $(COQ_PROOF_DIR)\
                               $(COQ_INVARIANTS_DIR)\
                             , $(wildcard $(dir)/*.v)\
                 )

######################### Partition files ###########################

PARTITION_INTERMEDIATE_BIN=$(C_SRC_TARGET_DIR)/root_partition.bin
PARTITION_BIN=$(TARGET_PARTITION_DIR)/$(PARTITION)/$(PARTITION).bin

######################## Miscellaneous files ########################

TARGET_PARTITIONS_OBJ=$(wildcard $(TARGET_PARTITION_DIR)/*.o)
OBJECT_FILES=$(C_TARGET_MAL_OBJ) $(C_TARGET_BOOT_OBJ)\
             $(C_GENERATED_OBJ) $(AS_TARGET_BOOT_OBJ)\
             $(TARGET_PARTITIONS_OBJ)

# Jsons (Coq extracted AST)
JSONS=IAL.json Internal.json MAL.json MALInternal.json Services.json
JSONS:=$(addprefix $(GENERATED_FILES_DIR)/, $(JSONS))

#####################################################################
##                    Default Makefile target                      ##
#####################################################################

all : $(PARTITION).elf $(PARTITION).iso

#####################################################################
##                    Code compilation targets                     ##
#####################################################################

###################### Generation from Coq to C #####################

# Drop purely model related coq modules
DIGGERFLAGS := -m ADT -m Datatypes -m Hardware -m Nat
DIGGERFLAGS += --ignore coq_N
# Monad used in the coq code
DIGGERFLAGS += -M coq_LLI
# Dependencies of the traducted code to C interface
DIGGERFLAGS += -m MALInternal -d :$(GENERATED_FILES_DIR)/MALInternal.json
DIGGERFLAGS += -m MAL -d :$(GENERATED_FILES_DIR)/MAL.json
DIGGERFLAGS += -m IAL -d :$(GENERATED_FILES_DIR)/IAL.json
# output a #include "maldefines.h" at the beginning of the translated files
DIGGERFLAGS += -q maldefines.h

$(GENERATED_FILES_DIR)/Internal.h: $(GENERATED_FILES_DIR)/Internal.json $(JSONS)\
                                 | $(GENERATED_FILES_DIR) $(DIGGER)
	$(DIGGER) $(DIGGERFLAGS) --header\
		                 $< -o $@

$(GENERATED_FILES_DIR)/Internal.c: $(GENERATED_FILES_DIR)/Internal.json $(JSONS)\
	                           $(GENERATED_FILES_DIR)/Internal.h\
                                 | $(GENERATED_FILES_DIR) $(DIGGER)
	$(DIGGER) $(DIGGERFLAGS) -q Internal.h\
	                         $< -o $@

$(GENERATED_FILES_DIR)/Services.c: $(GENERATED_FILES_DIR)/Services.json $(JSONS)\
	                           $(GENERATED_FILES_DIR)/Internal.json\
	                           $(GENERATED_FILES_DIR)/Internal.h\
                                 | $(GENERATED_FILES_DIR) $(DIGGER)
	$(DIGGER) $(DIGGERFLAGS) -m Internal -d :$(GENERATED_FILES_DIR)/Internal.json\
	                         -q Internal.h\
				 $< -o $@

############################## Coq rules ############################

.depend.coq: $(COQ_SRC_FILES) $(COQ_PROOF_FILES) $(COQ_EXTRACTION_FILES)
	$(COQDEP) $(COQFLAGS) $^ > $@

-include .depend.coq

%.vo: %.v
	$(COQC) $(COQCFLAGS) $<

ifneq (,$(findstring grouped-target,$(.FEATURES)))
$(JSONS) src/extraction/Extraction.vo &: src/extraction/Extraction.v | $(GENERATED_FILES_DIR)
	cd $(GENERATED_FILES_DIR) && $(COQC) $(COQCEXTRFLAGS) ../$<
else
# Unfortunately, without grouped-target we cannot inherit dependencies
# computed by coqdep, so we must mv files after the fact
$(JSONS): src/extraction/Extraction.vo | $(GENERATED_FILES_DIR)
	mv $(notdir $@) $(GENERATED_FILES_DIR)
endif


########################### C object rules ##########################

# Static pattern rule for constructing object files from generated C files
$(C_GENERATED_OBJ):\
    %.o: %.c $(C_MODEL_INTERFACE_HEADERS) $(C_GENERATED_HEADERS)
	$(CC) $(CFLAGS) -I $(C_MODEL_INTERFACE_INCLUDE_DIR)\
                        -I $(C_GENERATED_HEADERS_DIR)\
                        -I $(C_TARGET_BOOT_INCLUDE_DIR)\
                        -c -o $@ $<

# Static pattern rule for constructing object files from target boot C files
$(C_TARGET_BOOT_OBJ):\
    %.o : %.c $(C_MODEL_INTERFACE_HEADERS) $(C_TARGET_MAL_HEADERS)\
              $(C_TARGET_BOOT_HEADERS) $(C_GENERATED_HEADERS)
	$(CC) $(CFLAGS) -I $(C_MODEL_INTERFACE_INCLUDE_DIR)\
                        -I $(C_TARGET_MAL_INCLUDE_DIR)\
                        -I $(C_TARGET_BOOT_INCLUDE_DIR)\
                        -I $(C_GENERATED_HEADERS_DIR)\
                        -c -o $@ $<

# Static pattern rule for constructing object files from target boot assembly files
$(AS_TARGET_BOOT_OBJ):\
    %.o : %.s
	$(AS) $(ASFLAGS) -o $@ $<

# Static pattern rule for constructing object files from target MAL C files
$(C_TARGET_MAL_OBJ):\
    %.o : %.c $(C_MODEL_INTERFACE_HEADERS) $(C_TARGET_MAL_HEADERS)\
              $(C_TARGET_BOOT_HEADERS)
	$(CC) $(CFLAGS) -I $(C_MODEL_INTERFACE_INCLUDE_DIR)\
                        -I $(C_TARGET_MAL_INCLUDE_DIR)\
                        -I $(C_TARGET_BOOT_INCLUDE_DIR)\
                        -c -o $@ $<

########################## Partition Binary #########################

$(AS_ROOTPART_BIN_WRAPPER_OBJ): $(AS_ROOTPART_BIN_WRAPPER_SRC) $(PARTITION_INTERMEDIATE_BIN)\
                              | $(GENERATED_FILES_DIR)
	$(AS) $(ASFLAGS) -o $@ $<

######################### Pip + Partition ELF #######################

# $(AS_TARGET_BOOT_OBJ) must be the first object file arg to the linker
$(PARTITION).elf: $(C_SRC_TARGET_DIR)/link.ld\
                  $(C_TARGET_BOOT_OBJ) $(AS_TARGET_BOOT_OBJ)\
		  $(C_TARGET_MAL_OBJ) $(C_GENERATED_OBJ)\
		  $(AS_ROOTPART_BIN_WRAPPER_OBJ)
	$(LD) $(LDFLAGS)\
                  $(C_TARGET_BOOT_OBJ) $(AS_TARGET_BOOT_OBJ)\
                  $(C_TARGET_MAL_OBJ) $(C_GENERATED_OBJ)\
                  $(AS_ROOTPART_BIN_WRAPPER_OBJ)\
                  -T $< -o $@

#####################################################################
##                      Proof related targets                      ##
#####################################################################

proofs: $(COQ_PROOF_FILES:.v=.vo)

####################################################################
##                        Utility targets                         ##
####################################################################

####################### Documentation targets ######################

doc: doc-c doc-coq gettingstarted

doc-c: | $(C_DOC_DIR)
	cd doc && $(DOXYGEN) doxygen.conf

doc-coq: Makefile.coq | $(GENERATED_FILES_DIR) $(COQ_DOC_DIR)
	$(MAKE) -f $< html
	# Should not be done like this but the html directory
	# is hardcoded in the Makefile.coq
	mv -f html $(COQ_DOC_DIR)

gettingstarted:
	cd doc/getting-started/ &&\
        $(PDFLATEX) getting-started.tex &&\
        $(PDFLATEX) getting-started.tex

########################### ISO targets ############################

INTERMEDIATE_ELF=tools/grub/boot/pip.elf

$(INTERMEDIATE_ELF): $(PARTITION).elf
	ln $< $@

$(PARTITION).iso: $(INTERMEDIATE_ELF)
	$(GRUBMKRESCUE) -o $@ tools/grub

########################### QEMU targets ###########################

qemu-elf: $(PARTITION).elf
	$(QEMU) $(QEMUARGS) -kernel $<

qemu-iso: $(PARTITION).iso
	$(QEMU) $(QEMUARGS) -boot d -cdrom $<

####################################################################

toolchain.mk:
	sh configure.sh

Makefile.coq: Makefile _CoqProject $(COQ_EXTRACTION_FILES) $(COQ_SRC_FILES) $(COQ_PROOF_FILES)
	$(COQ_MAKEFILE) $(COQ_ENV) -f _CoqProject -o Makefile.coq $(COQ_EXTRACTION_FILES) $(COQ_SRC_FILES) $(COQ_PROOF_FILES)

$(GENERATED_FILES_DIR) $(C_DOC_DIR) $(COQ_DOC_DIR):
	mkdir -p $@

# Using a hard link to prevent copy
$(PARTITION_INTERMEDIATE_BIN): $(PARTITION_BIN)
	ln $< $@

$(PARTITION_BIN):
	make -C $(TARGET_PARTITION_DIR)/$(PARTITION)

# Do not trigger compilation if $(PARTITION_INTERMEDIATE_BIN) is missing
# and delete $(PARTITION_INTERMEDIATE_BIN) after compilation if it was created
.INTERMEDIATE: $(PARTITION_INTERMEDIATE_BIN) $(INTERMEDIATE_ELF)

realclean: clean
	rm -rf $(COQ_DOC_DIR) $(C_DOC_DIR)
	rm -f $(DOC_DIR)/getting-started/getting-started.aux\
              $(DOC_DIR)/getting-started/getting-started.out\
              $(DOC_DIR)/getting-started/getting-started.toc\
              $(DOC_DIR)/getting-started/getting-started.log\
              $(DOC_DIR)/getting-started/getting-started.pdf

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf .lia.cache
	rm -rf $(GENERATED_FILES_DIR)
	rm -f $(OBJECT_FILES)
	rm -f $(PARTITION).elf
	rm -f $(PARTITION).iso

gdb: $(PARTITION).elf
	gdb $(GDBARGS) $<

.PHONY: all proofs doc doc-c doc-coq gettingstarted qemu-elf qemu-iso realclean clean gdb
