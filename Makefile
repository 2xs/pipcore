#####################################################################
##                       Directory variables                       ##
#####################################################################

# Build directory
BUILD_DIR=build

# Sources directory
SRC_DIR=src

# Coq sources directory
CORE_DIR=$(SRC_DIR)/core
MODEL_DIR=$(SRC_DIR)/model
META_MODEL_DIR=$(MODEL_DIR)/Meta
ISOLATION_MODEL_DIR=$(MODEL_DIR)/Isolation
HOLLOW_MODEL_DIR=$(MODEL_DIR)/Hollow

# Coq proofs related directories
PROOF_DIR=proof
ISOLATION_PROOF_DIR=$(PROOF_DIR)/Isolation
ISOLATION_PROOF_INVARIANTS_DIR=$(ISOLATION_PROOF_DIR)/Invariants

#####################################################################
##                      Build files variables                      ##
#####################################################################

# Coq source files
COQ_SRC_FILES=$(foreach dir, $(CORE_DIR)\
                             $(META_MODEL_DIR)\
                             $(ISOLATION_MODEL_DIR)\
                             $(HOLLOW_MODEL_DIR),\
			$(wildcard $(dir)/*.v)\
               )

# Coq file needed for extraction
COQ_EXTRACTION_FILE=$(MODEL_DIR)/Extraction.v
COQ_COMPILED_EXTRACTION_FILE=$(COQ_EXTRACTION_FILE:.v=.vo)

# Coq prooof files
COQ_PROOF_FILES=$(foreach dir, $(ISOLATION_PROOF_DIR)\
		               $(ISOLATION_PROOF_INVARIANTS_DIR),\
			$(wildcard $(dir)/*.v)\
		)

HASKELL_EXTRACTED_FILES=Ascii.hs Datatypes.hs Extraction.hs HollowModel.hs String.hs
HASKELL_EXTRACTED_FILES:=$(patsubst %,$(BUILD_DIR)/%, $(HASKELL_EXTRACTED_FILES))

#####################################################################
##                         Default target                          ##
#####################################################################

all : proofs

#####################################################################
##                       Compilation targets                       ##
#####################################################################

Makefile.coq: Makefile _CoqProject $(COQ_EXTRACTION_FILE) $(COQ_SRC_FILES) $(COQ_PROOF_FILES)
	coq_makefile -f _CoqProject -o Makefile.coq $(COQ_EXTRACTION_FILE) $(COQ_SRC_FILES) $(COQ_PROOF_FILES)

# All code extraction files are generated once Extraction.v is compiled
$(HASKELL_EXTRACTED_FILES) &: coq_code_extraction ;

$(BUILD_DIR):
	mkdir -p $@

proofs: Makefile.coq $(COQ_SRC_FILES) $(COQ_PROOF_FILES) $(COQ_EXTRACTION_FILES) | $(BUILD_DIR)
	$(MAKE) -f Makefile.coq all

coq_code_extraction : Makefile.coq $(COQ_EXTRACTION_FILE) | $(BUILD_DIR)
	$(MAKE) --no-print-directory -f Makefile.coq only TGTS="$(COQ_COMPILED_EXTRACTION_FILE)" -j

clean: | Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf *~ .*.aux *.crashcoqide
	rm -rf $(BUILD_DIR)

.PHONY: all proofs coq_code_extraction clean
