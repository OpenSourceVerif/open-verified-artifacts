# ==============================================================================
# Configuration
# ==============================================================================

DIRS := tnum

NAMESPACE_PREFIX := bpf

# Z3 Verification Configuration
CXX := g++
CXXFLAGS := -std=c++17 -O3
LDFLAGS := -lz3 -lpthread

INTERVAL_DIR := interval
Z3_SOURCES := $(wildcard $(INTERVAL_DIR)/*.cpp)
Z3_TARGETS := $(patsubst $(INTERVAL_DIR)/%.cpp,$(INTERVAL_DIR)/%,$(Z3_SOURCES))

# ==============================================================================
# Calculations
# ==============================================================================

COQ_INCLUDES := $(foreach d,$(DIRS),-R $(d) $(NAMESPACE_PREFIX).$(d))

VFILES := $(foreach d,$(DIRS),$(wildcard $(d)/*.v))

COQMAKEFILE := coq_makefile

# ==============================================================================
# Rules
# ==============================================================================

.PHONY: all clean coq z3

all: coq z3

coq: CoqMakefile
	@echo "Building Coq project..."
	@if [ -z "$(VFILES)" ]; then \
		echo "Error: No .v files found in directories: $(DIRS)"; \
		exit 1; \
	fi
	@$(MAKE) -f CoqMakefile all

z3: $(Z3_TARGETS)
	@echo "Z3 verification programs built successfully."

$(INTERVAL_DIR)/%: $(INTERVAL_DIR)/%.cpp
	@echo "Compiling $<..."
	$(CXX) $(CXXFLAGS) $< $(LDFLAGS) -o $@

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
	
	@echo "Cleaning Z3 verification binaries..."
	@rm -f $(Z3_TARGETS)