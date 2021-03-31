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

MAKEFLAGS += -j

#####################################################################
##                      Directory variables                        ##
#####################################################################

SRC_DIR=src
ARCH_DEPENDENT_DIR=$(SRC_DIR)/arch_dependent

COQ_CORE_DIR=$(SRC_DIR)/core
COQ_MODEL_DIR=$(SRC_DIR)/model
COQ_EXTRACTION_DIR=$(SRC_DIR)/extraction

COQ_PROOF_DIR=proof
COQ_INVARIANTS_DIR=$(COQ_PROOF_DIR)/invariants

C_SRC_TARGET_DIR=$(ARCH_DEPENDENT_DIR)/$(TARGET)

BUILD_DIR=build
BUILD_TARGET_DIR=$(BUILD_DIR)/$(TARGET)

#####################################################################
##                        Files variables                          ##
#####################################################################

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

# Jsons (Coq extracted AST)
JSONS=IAL.json Internal.json MAL.json MALInternal.json Services.json
JSONS:=$(patsubst %,$(BUILD_DIR)/%, $(JSONS))

#####################################################################
##                    Default Makefile target                      ##
#####################################################################

all : $(BUILD_DIR)/Services.c $(BUILD_DIR)/Internal.c

#####################################################################
##                    Code compilation targets                     ##
#####################################################################

####################### Jsons (AST) generation ######################

# Rely on Makefile.coq to handle dependencies of coq code and
# compile it. Extracts necessary information for generation of C files
coq_code_extraction : Makefile.coq $(BUILD_DIR)
	$(MAKE) --no-print-directory -f Makefile.coq only TGTS="src/extraction/Extraction.vo" -j

# All jsons are generated once Extraction.v is compiled
$(JSONS) &: coq_code_extraction ;

########################## Digger options ###########################

# Drop purely model related coq modules
DIGGERFLAGS := -m ADT -m Datatypes -m Hardware -m Nat
DIGGERFLAGS += --ignore coq_N
# Monad used in the coq code
DIGGERFLAGS += -M coq_LLI
# Dependencies of the traducted code to C interface
DIGGERFLAGS += -m MALInternal -d :$(BUILD_DIR)/MALInternal.json
DIGGERFLAGS += -m MAL -d :$(BUILD_DIR)/MAL.json
DIGGERFLAGS += -m IAL -d :$(BUILD_DIR)/IAL.json
# output a #include "maldefines.h" at the beginning of the translated files
DIGGERFLAGS += -q maldefines.h

##################### Traduction from Coq to C ######################

$(BUILD_DIR)/Internal.h: $(BUILD_DIR)/Internal.json $(JSONS) $(DIGGER) $(BUILD_DIR)
	$(DIGGER) $(DIGGERFLAGS) --header\
		                 $< -o $@

$(BUILD_DIR)/Internal.c: $(BUILD_DIR)/Internal.json $(JSONS) $(DIGGER) $(BUILD_DIR) $(BUILD_DIR)/Internal.h
	$(DIGGER) $(DIGGERFLAGS) -q yield_c.h\
	                         -q Internal.h\
	                         $< -o $@

$(BUILD_DIR)/Services.c: $(BUILD_DIR)/Services.json $(JSONS) $(DIGGER) $(BUILD_DIR) $(BUILD_DIR)/Internal.h
	$(DIGGER) $(DIGGERFLAGS) -m Internal -d :$(BUILD_DIR)/Internal.json\
	                         -q Internal.h\
				 $< -o $@

#####################################################################
##                      Proof related targets                      ##
#####################################################################

proofs: Makefile.coq $(BUILD_DIR) $(COQ_SRC_FILES) $(COQ_PROOF_FILES)
	$(MAKE) -f Makefile.coq all

%.vo : Makefile.coq $(BUILD_DIR)
	$(MAKE) --no-print-directory -f Makefile.coq only TGTS="$@" -j

####################################################################
##                        Utility targets                         ##
####################################################################

Makefile.coq: Makefile _CoqProject $(COQ_EXTRACTION_FILES) $(COQ_SRC_FILES) $(COQ_PROOF_FILES)
	coq_makefile -f _CoqProject -o Makefile.coq $(COQ_EXTRACTION_FILES) $(COQ_SRC_FILES) $(COQ_PROOF_FILES)

$(BUILD_DIR):
	mkdir -p $@

$(BUILD_TARGET_DIR): $(BUILD_DIR)
	mkdir -p $@

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf
	rm -rf $(BUILD_DIR)

.PHONY: all clean coq_code_extraction
