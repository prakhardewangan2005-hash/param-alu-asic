# ============================================================================
# Makefile for Parameterized ALU Project
# Author: ASIC Design Team
# Date: February 2026
# ============================================================================

# Default parameters
WIDTH ?= 32
TEST ?= random
SEED ?= 42
NTESTS ?= 1000
SIMULATOR ?= questa

# Directories
RTL_DIR = rtl
VERIF_DIR = verif
TEST_DIR = tests
SCRIPT_DIR = scripts
SYN_DIR = syn
WORK_DIR = work

# File lists
RTL_FILES = $(RTL_DIR)/alu_pkg.sv \
            $(RTL_DIR)/param_alu.sv

VERIF_FILES = $(VERIF_DIR)/alu_tb_pkg.sv \
              $(VERIF_DIR)/alu_driver.sv \
              $(VERIF_DIR)/alu_monitor.sv \
              $(VERIF_DIR)/alu_scoreboard.sv \
              $(VERIF_DIR)/alu_coverage.sv \
              $(VERIF_DIR)/alu_assertions.sv \
              $(VERIF_DIR)/alu_tb_top.sv

TEST_FILES = $(TEST_DIR)/alu_directed_test.sv \
             $(TEST_DIR)/alu_random_test.sv

ALL_FILES = $(RTL_FILES) $(VERIF_FILES) $(TEST_FILES)

# ============================================================================
# Targets
# ============================================================================

.PHONY: all compile sim run clean help synthesis regression

# Default target
all: compile sim

# Help
help:
	@echo "============================================"
	@echo "Parameterized ALU Makefile"
	@echo "============================================"
	@echo ""
	@echo "Targets:"
	@echo "  make compile       - Compile design"
	@echo "  make sim          - Run simulation"
	@echo "  make run          - Compile and simulate"
	@echo "  make regression   - Run full regression"
	@echo "  make synthesis    - Run synthesis"
	@echo "  make clean        - Clean work directory"
	@echo "  make help         - Show this help"
	@echo ""
	@echo "Parameters:"
	@echo "  WIDTH=<8|16|32|64>     - Data width (default: 32)"
	@echo "  TEST=<directed|random|corner|all> - Test type (default: random)"
	@echo "  SEED=<number>          - Random seed (default: 42)"
	@echo "  NTESTS=<number>        - Number of tests (default: 1000)"
	@echo ""
	@echo "Examples:"
	@echo "  make compile WIDTH=32"
	@echo "  make sim TEST=directed WIDTH=16"
	@echo "  make run TEST=random SEED=123 NTESTS=5000"
	@echo "  make regression"
	@echo ""

# Compile
compile:
	@echo "Compiling design..."
	python3 $(SCRIPT_DIR)/compile_sim.py \
		--test $(TEST) \
		--width $(WIDTH) \
		--seed $(SEED) \
		--ntests $(NTESTS) \
		--clean

# Simulate
sim:
	@echo "Running simulation..."
	python3 $(SCRIPT_DIR)/compile_sim.py \
		--test $(TEST) \
		--width $(WIDTH) \
		--seed $(SEED) \
		--ntests $(NTESTS)

# Compile and run
run: compile sim

# Run with GUI
gui:
	python3 $(SCRIPT_DIR)/compile_sim.py \
		--test $(TEST) \
		--width $(WIDTH) \
		--seed $(SEED) \
		--ntests $(NTESTS) \
		--gui \
		--waves

# Run with coverage
coverage:
	python3 $(SCRIPT_DIR)/compile_sim.py \
		--test $(TEST) \
		--width $(WIDTH) \
		--seed $(SEED) \
		--ntests $(NTESTS) \
		--coverage

# Full regression
regression:
	@echo "Running full regression..."
	python3 $(SCRIPT_DIR)/run_regression.py \
		--tests all \
		--widths 8,16,32,64 \
		--seeds 10 \
		--ntests $(NTESTS) \
		--coverage

# Quick regression (fewer tests)
regression-quick:
	@echo "Running quick regression..."
	python3 $(SCRIPT_DIR)/run_regression.py \
		--tests directed corner random \
		--widths 32 \
		--seeds 3 \
		--ntests 500

# Synthesis
synthesis:
	@echo "Running synthesis..."
	cd $(SYN_DIR) && dc_shell-xg-t -f synthesis.tcl

# Summarize results
summarize:
	python3 $(SCRIPT_DIR)/summarize_results.py

# Clean
clean:
	@echo "Cleaning work directory..."
	rm -rf $(WORK_DIR)
	rm -rf transcript vsim.wlf modelsim.ini
	rm -rf coverage.ucdb coverage_report.txt coverage_html
	rm -rf regression_results
	rm -f *.log *.vcd
	@echo "Clean complete."

# Deep clean (includes synthesis)
distclean: clean
	@echo "Deep cleaning..."
	cd $(SYN_DIR) && rm -rf reports outputs *.log
	@echo "Deep clean complete."

# Check file existence
check-files:
	@echo "Checking for required files..."
	@for file in $(ALL_FILES); do \
		if [ ! -f $$file ]; then \
			echo "ERROR: Missing file: $$file"; \
			exit 1; \
		fi; \
	done
	@echo "All files present."

# Lint check (requires linter tool)
lint:
	@echo "Running lint check..."
	verilator --lint-only -Wall \
		--top-module param_alu \
		$(RTL_FILES)

# Documentation generation (requires doxygen)
docs:
	@echo "Generating documentation..."
	doxygen Doxyfile

# ============================================================================
# Test shortcuts
# ============================================================================

test-directed:
	$(MAKE) run TEST=directed WIDTH=32

test-random:
	$(MAKE) run TEST=random WIDTH=32 NTESTS=1000

test-corner:
	$(MAKE) run TEST=corner WIDTH=32

test-all:
	$(MAKE) run TEST=all WIDTH=32

# ============================================================================
# Width-specific tests
# ============================================================================

test-8bit:
	$(MAKE) run WIDTH=8 TEST=all

test-16bit:
	$(MAKE) run WIDTH=16 TEST=all

test-32bit:
	$(MAKE) run WIDTH=32 TEST=all

test-64bit:
	$(MAKE) run WIDTH=64 TEST=all
