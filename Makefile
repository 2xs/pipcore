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

include toolchain.mk
TARGET=x86_multiboot
PARTITION=nanny_busy_beaver

MAKEFLAGS += -j

CFLAGS=-m32 -Wall -W -Wextra -Werror -nostdlib -fno-builtin -std=gnu99 -ffreestanding -c -g -Wno-unused-variable -trigraphs -Wno-trigraphs -march=pentium -Wno-unused-but-set-variable -DPIPDEBUG -Wno-unused-parameter -fno-stack-protector -fno-pic -no-pie -DLOGLEVEL=TRACE -DGIT_REVISION='"7f309a4380486a0e8fba88728aab68b6fdc85c02"'

NASMFLAGS=-f elf
LDFLAGS=-m elf_i386

#####################################################################
##                      Directory variables                        ##
#####################################################################

SRC_DIR=src
GENERATED_FILES_DIR=generated

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

INTERMEDIATE_BIN=$(C_SRC_TARGET_DIR)/root_partition.bin
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

all : $(PARTITION).elf

#####################################################################
##                    Code compilation targets                     ##
#####################################################################

####################### Jsons (AST) generation ######################

# Rely on Makefile.coq to handle dependencies of coq code and
# compile it. Extracts necessary information for generation of C files
$(JSONS) &: Makefile.coq $(COQ_SRC_FILES) | $(GENERATED_FILES_DIR)
	$(MAKE) --no-print-directory -f Makefile.coq only TGTS="$(COQ_EXTRACTION_FILES:.v=.vo)" -j

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

########################### C object rules ##########################

# Static pattern rule for constructing object files from generated C files
$(C_GENERATED_OBJ):\
    %.o: %.c $(C_MODEL_INTERFACE_HEADERS) $(C_GENERATED_HEADERS)
	$(CC) $(CFLAGS) -I $(C_MODEL_INTERFACE_INCLUDE_DIR)\
                        -I $(C_GENERATED_HEADERS_DIR)\
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
	$(NASM) $(NASMFLAGS) -o $@ $<

# Static pattern rule for constructing object files from target MAL C files
$(C_TARGET_MAL_OBJ):\
    %.o : %.c $(C_MODEL_INTERFACE_HEADERS) $(C_TARGET_MAL_HEADERS)\
              $(C_TARGET_BOOT_HEADERS)
	$(CC) $(CFLAGS) -I $(C_MODEL_INTERFACE_INCLUDE_DIR)\
                        -I $(C_TARGET_MAL_INCLUDE_DIR)\
                        -I $(C_TARGET_BOOT_INCLUDE_DIR)\
                        -c -o $@ $<

########################## Partition Binary #########################

$(AS_ROOTPART_BIN_WRAPPER_OBJ): $(AS_ROOTPART_BIN_WRAPPER_SRC) $(INTERMEDIATE_BIN)\
                              | $(GENERATED_FILES_DIR)
	$(NASM) $(NASMFLAGS) -o $@ $<

######################### Pip + Partition ELF #######################

# $(AS_TARGET_BOOT_OBJ) must be the first object file arg to the linker
$(PARTITION).elf: $(C_SRC_TARGET_DIR)/link.ld\
                  $(C_TARGET_BOOT_OBJ) $(AS_TARGET_BOOT_OBJ)\
		  $(C_TARGET_MAL_OBJ) $(C_GENERATED_OBJ)\
		  $(AS_ROOTPART_BIN_WRAPPER_OBJ)
	$(LD) $(LDFLAGS)\
                  $(AS_TARGET_BOOT_OBJ) $(C_TARGET_BOOT_OBJ)\
		  $(C_TARGET_MAL_OBJ) $(C_GENERATED_OBJ)\
		  $(AS_ROOTPART_BIN_WRAPPER_OBJ)\
                  -T $< -o $@

#####################################################################
##                      Proof related targets                      ##
#####################################################################

proofs: Makefile.coq $(COQ_SRC_FILES) $(COQ_PROOF_FILES)
	$(MAKE) -f Makefile.coq all

%.vo : Makefile.coq
	$(MAKE) --no-print-directory -f Makefile.coq only TGTS="$@" -j

####################################################################
##                        Utility targets                         ##
####################################################################

Makefile.coq: Makefile _CoqProject $(COQ_EXTRACTION_FILES) $(COQ_SRC_FILES) $(COQ_PROOF_FILES)
	coq_makefile -f _CoqProject -o Makefile.coq $(COQ_EXTRACTION_FILES) $(COQ_SRC_FILES) $(COQ_PROOF_FILES)

$(GENERATED_FILES_DIR):
	mkdir -p $@

# Using a hard link to prevent copy
$(INTERMEDIATE_BIN): $(PARTITION_BIN)
	ln $< $@

# Do not trigger compilation if $(INTERMEDIATE_BIN) is missing
# and delete $(INTERMEDIATE_BIN) after compilation if it was created
.INTERMEDIATE: $(INTERMEDIATE_BIN)

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf
	rm -rf $(GENERATED_FILES_DIR)
	rm -f $(OBJECT_FILES)
	rm -f $(PARTITION).elf

.PHONY: all proofs clean
