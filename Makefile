# ==============================================================================
# Configuration
# ==============================================================================

DIRS := tnum

NAMESPACE_PREFIX := bpf

# ==============================================================================
# Calculations
# ==============================================================================

COQ_INCLUDES := $(foreach d,$(DIRS),-R $(d) $(NAMESPACE_PREFIX).$(d))

VFILES := $(foreach d,$(DIRS),$(wildcard $(d)/*.v))

COQMAKEFILE := coq_makefile

# ==============================================================================
# Rules
# ==============================================================================

.PHONY: all clean

all: CoqMakefile
	@echo "Building Coq project..."
	@if [ -z "$(VFILES)" ]; then \
		echo "Error: No .v files found in directories: $(DIRS)"; \
		exit 1; \
	fi
	@$(MAKE) -f CoqMakefile all

_CoqProject:
	@echo "Generating _CoqProject..."
	@echo "$(COQ_INCLUDES)" > _CoqProject

CoqMakefile: _CoqProject $(VFILES)
	@echo "Generating build system..."
	$(COQMAKEFILE) -f _CoqProject $(VFILES) -o CoqMakefile

clean:
	@echo "Cleaning artifacts..."

	@if [ -f CoqMakefile ]; then $(MAKE) -f CoqMakefile clean; fi
	
	@rm -f _CoqProject CoqMakefile CoqMakefile.conf
	
	@find $(DIRS) \( \
		-name ".*.aux" -o \
		-name ".*.cache" -o \
		-name "*.aux" -o \
		-name "*.glob" -o \
		-name "*.vo" -o \
		-name "*.vok" -o \
		-name "*.vos" \
	\) -delete