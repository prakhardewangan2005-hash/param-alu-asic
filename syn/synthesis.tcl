# ============================================================================
# Synthesis Script for Parameterized ALU
# Tool: Synopsys Design Compiler
# Technology: TSMC 28nm HPC+
# Author: ASIC Design Team
# Date: February 2026
# ============================================================================

# ============================================================================
# Setup
# ============================================================================

# Define design name
set DESIGN_NAME "param_alu"
set WIDTH 32

# Define target library (update path to your library)
set TARGET_LIBRARY_PATH "/path/to/tsmc28hpc+/libs"
set TARGET_LIBRARY "tcbn28hpcplusbwp7t_ccs.db"

# Set search path
set_app_var search_path ". $TARGET_LIBRARY_PATH"

# Set target and link libraries
set_app_var target_library $TARGET_LIBRARY
set_app_var link_library "* $TARGET_LIBRARY"

# Set synthesis options
set_app_var compile_ultra_ungroup_dw false
set_app_var hdlin_enable_hier_naming true
set_app_var verilogout_no_tri true

# ============================================================================
# Read Design
# ============================================================================

puts ""
puts "========================================"
puts "Reading RTL Design"
puts "========================================"
puts ""

# Read package first
analyze -format sverilog ../rtl/alu_pkg.sv
elaborate alu_pkg

# Read and elaborate main design
analyze -format sverilog ../rtl/param_alu.sv
elaborate $DESIGN_NAME -parameters "WIDTH=$WIDTH"

# Link design
current_design $DESIGN_NAME
link

# Check design
check_design > reports/check_design.rpt

puts ""
puts "Design read successfully"
puts ""

# ============================================================================
# Define Constraints
# ============================================================================

puts ""
puts "========================================"
puts "Applying Constraints"
puts "========================================"
puts ""

# Clock period (500 MHz = 2.0 ns)
set CLK_PERIOD 2.0
set CLK_NAME "virtual_clk"

# Create virtual clock for I/O timing
create_clock -name $CLK_NAME -period $CLK_PERIOD

# Input delay (15% of clock period)
set INPUT_DELAY [expr $CLK_PERIOD * 0.15]
set_input_delay $INPUT_DELAY -clock $CLK_NAME [all_inputs]

# Output delay (15% of clock period)
set OUTPUT_DELAY [expr $CLK_PERIOD * 0.15]
set_output_delay $OUTPUT_DELAY -clock $CLK_NAME [all_outputs]

# Set max fanout
set_max_fanout 16 [all_inputs]

# Set driving cell (typical buffer)
set_driving_cell -lib_cell BUFX2 [all_inputs]

# Set load on outputs (typical load)
set_load 0.05 [all_outputs]

# Operating conditions
set_operating_conditions -max typical
set_wire_load_mode top

# Environmental constraints
set_max_area 0
set_max_dynamic_power 0

puts ""
puts "Constraints applied"
puts ""

# ============================================================================
# Compile Design
# ============================================================================

puts ""
puts "========================================"
puts "Compiling Design"
puts "========================================"
puts ""

# Compile ultra with optimization
compile_ultra -gate_clock -no_autoungroup

puts ""
puts "Compilation complete"
puts ""

# ============================================================================
# Optimize
# ============================================================================

puts ""
puts "========================================"
puts "Optimizing Design"
puts "========================================"
puts ""

# Additional optimization passes
optimize_netlist -area

puts ""
puts "Optimization complete"
puts ""

# ============================================================================
# Generate Reports
# ============================================================================

puts ""
puts "========================================"
puts "Generating Reports"
puts "========================================"
puts ""

# Create reports directory if it doesn't exist
file mkdir reports

# Area report
report_area -hierarchy > reports/area.rpt
report_area -designware > reports/area_designware.rpt

# Timing report
report_timing -max_paths 10 -delay_type max > reports/timing_max.rpt
report_timing -max_paths 10 -delay_type min > reports/timing_min.rpt
report_timing -loops > reports/timing_loops.rpt

# Power report
report_power -hierarchy > reports/power.rpt

# QoR (Quality of Results) report
report_qor > reports/qor.rpt
report_qor -summary > reports/qor_summary.rpt

# Constraint report
report_constraint -all_violators > reports/constraints.rpt

# Clock report
report_clock_gating > reports/clock_gating.rpt

# Cell usage
report_reference > reports/reference.rpt

# Port report
report_port -verbose > reports/ports.rpt

puts ""
puts "Reports generated in reports/ directory"
puts ""

# ============================================================================
# Write Out Netlist
# ============================================================================

puts ""
puts "========================================"
puts "Writing Output Files"
puts "========================================"
puts ""

# Create output directory
file mkdir outputs

# Write netlist
write -format verilog -hierarchy -output outputs/${DESIGN_NAME}_w${WIDTH}_synth.v
write -format ddc -hierarchy -output outputs/${DESIGN_NAME}_w${WIDTH}_synth.ddc

# Write SDC constraints
write_sdc outputs/${DESIGN_NAME}_w${WIDTH}_synth.sdc

# Write SDF for timing simulation
write_sdf outputs/${DESIGN_NAME}_w${WIDTH}_synth.sdf

puts ""
puts "Output files written to outputs/ directory"
puts ""

# ============================================================================
# Display Summary
# ============================================================================

puts ""
puts "========================================"
puts "Synthesis Summary"
puts "========================================"
puts ""

# Get area
set total_area [get_attribute [current_design] area]
puts "Total Area: [format "%.2f" $total_area] um^2"

# Get cell count
set cell_count [sizeof_collection [get_cells -hierarchical]]
puts "Total Cells: $cell_count"

# Get timing
set wns [get_attribute [get_timing_paths] slack]
if {$wns >= 0} {
    puts "Timing: MET (Slack: [format "%.3f" $wns] ns)"
} else {
    puts "Timing: VIOLATED (Slack: [format "%.3f" $wns] ns)"
}

# Get critical path delay
set critical_delay [expr $CLK_PERIOD - $wns]
puts "Critical Path Delay: [format "%.3f" $critical_delay] ns"

# Calculate max frequency
if {$critical_delay > 0} {
    set max_freq [expr 1000.0 / $critical_delay]
    puts "Maximum Frequency: [format "%.0f" $max_freq] MHz"
}

puts ""
puts "========================================"
puts "Synthesis Complete"
puts "========================================"
puts ""

# ============================================================================
# Optional: Multi-Width Synthesis
# ============================================================================

# Uncomment to synthesize multiple widths
# foreach width {8 16 32 64} {
#     puts ""
#     puts "========================================"
#     puts "Synthesizing WIDTH=$width"
#     puts "========================================"
#     puts ""
#     
#     remove_design -all
#     analyze -format sverilog ../rtl/alu_pkg.sv
#     elaborate alu_pkg
#     analyze -format sverilog ../rtl/param_alu.sv
#     elaborate $DESIGN_NAME -parameters "WIDTH=$width"
#     current_design $DESIGN_NAME
#     link
#     
#     # Apply constraints (same as above)
#     create_clock -name $CLK_NAME -period $CLK_PERIOD
#     set_input_delay $INPUT_DELAY -clock $CLK_NAME [all_inputs]
#     set_output_delay $OUTPUT_DELAY -clock $CLK_NAME [all_outputs]
#     set_max_fanout 16 [all_inputs]
#     set_driving_cell -lib_cell BUFX2 [all_inputs]
#     set_load 0.05 [all_outputs]
#     set_max_area 0
#     
#     # Compile
#     compile_ultra -gate_clock -no_autoungroup
#     
#     # Reports
#     report_qor > reports/qor_w${width}.rpt
#     report_area > reports/area_w${width}.rpt
#     report_timing > reports/timing_w${width}.rpt
#     report_power > reports/power_w${width}.rpt
#     
#     # Write outputs
#     write -format verilog -hierarchy -output outputs/${DESIGN_NAME}_w${width}_synth.v
#     write -format ddc -hierarchy -output outputs/${DESIGN_NAME}_w${width}_synth.ddc
#     write_sdc outputs/${DESIGN_NAME}_w${width}_synth.sdc
# }

# Exit Design Compiler
# quit
