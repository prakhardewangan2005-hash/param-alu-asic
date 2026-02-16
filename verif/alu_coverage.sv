// ============================================================================
// Module: alu_coverage
// Description: Functional coverage collector for ALU testbench
// Author: Verification Team
// Date: February 2026
// ============================================================================

module alu_coverage 
    import alu_pkg::*;
    import alu_tb_pkg::*;
#(
    parameter int WIDTH = 32
) (
    input  logic clk,
    input  logic rst_n,
    input  logic sample_enable,
    
    // DUT interface signals
    input  logic [WIDTH-1:0]   operand_a,
    input  logic [WIDTH-1:0]   operand_b,
    input  opcode_e            opcode,
    input  logic               signed_op,
    input  logic [WIDTH-1:0]   result,
    input  flags_t             flags
);

    // ========================================================================
    // Coverage Groups
    // ========================================================================
    
    // Operation coverage
    covergroup cg_operations @(posedge clk iff (sample_enable && rst_n));
        cp_opcode: coverpoint opcode {
            bins add = {ADD};
            bins sub = {SUB};
            bins and_op = {AND};
            bins or_op = {OR};
            bins xor_op = {XOR};
            bins sll = {SLL};
            bins srl = {SRL};
            bins cmp = {CMP};
        }
        option.per_instance = 1;
        option.name = "operation_coverage";
    endgroup
    
    // Operand value coverage
    covergroup cg_operand_values @(posedge clk iff (sample_enable && rst_n));
        cp_operand_a: coverpoint operand_a {
            bins zero = {0};
            bins small = {[1:10]};
            bins mid = {[(2**(WIDTH-1))-5:(2**(WIDTH-1))+5]};
            bins large = {[(2**WIDTH)-10:(2**WIDTH)-1]};
            bins max = {{WIDTH{1'b1}}};
        }
        
        cp_operand_b: coverpoint operand_b {
            bins zero = {0};
            bins small = {[1:10]};
            bins mid = {[(2**(WIDTH-1))-5:(2**(WIDTH-1))+5]};
            bins large = {[(2**WIDTH)-10:(2**WIDTH)-1]};
            bins max = {{WIDTH{1'b1}}};
        }
        
        option.per_instance = 1;
        option.name = "operand_value_coverage";
    endgroup
    
    // Flag coverage
    covergroup cg_flags @(posedge clk iff (sample_enable && rst_n));
        cp_zero: coverpoint flags.zero {
            bins cleared = {0};
            bins set = {1};
        }
        
        cp_carry: coverpoint flags.carry {
            bins cleared = {0};
            bins set = {1};
        }
        
        cp_overflow: coverpoint flags.overflow {
            bins cleared = {0};
            bins set = {1};
        }
        
        cp_negative: coverpoint flags.negative {
            bins cleared = {0};
            bins set = {1};
        }
        
        option.per_instance = 1;
        option.name = "flag_coverage";
    endgroup
    
    // Operation-specific coverage for arithmetic
    covergroup cg_arithmetic @(posedge clk iff (sample_enable && rst_n && (opcode inside {ADD, SUB})));
        cp_signed_mode: coverpoint signed_op {
            bins unsigned_mode = {0};
            bins signed_mode = {1};
        }
        
        cp_overflow: coverpoint flags.overflow {
            bins no_overflow = {0};
            bins overflow_occurred = {1};
        }
        
        cp_carry: coverpoint flags.carry {
            bins no_carry = {0};
            bins carry_occurred = {1};
        }
        
        cx_signed_overflow: cross cp_signed_mode, cp_overflow {
            ignore_bins unsigned_overflow = binsof(cp_signed_mode) intersect {0} && 
                                            binsof(cp_overflow) intersect {1};
        }
        
        option.per_instance = 1;
        option.name = "arithmetic_coverage";
    endgroup
    
    // Shift operation coverage
    covergroup cg_shifts @(posedge clk iff (sample_enable && rst_n && (opcode inside {SLL, SRL})));
        cp_shift_amount: coverpoint operand_b[4:0] {
            bins zero = {0};
            bins small = {[1:7]};
            bins medium = {[8:23]};
            bins large = {[24:31]};
        }
        
        cp_shift_direction: coverpoint opcode {
            bins shift_left = {SLL};
            bins shift_right = {SRL};
        }
        
        cx_shift: cross cp_shift_amount, cp_shift_direction;
        
        option.per_instance = 1;
        option.name = "shift_coverage";
    endgroup
    
    // Logical operation coverage
    covergroup cg_logical @(posedge clk iff (sample_enable && rst_n && (opcode inside {AND, OR, XOR})));
        cp_operation: coverpoint opcode {
            bins and_op = {AND};
            bins or_op = {OR};
            bins xor_op = {XOR};
        }
        
        cp_result_zero: coverpoint (result == 0) {
            bins non_zero = {0};
            bins zero = {1};
        }
        
        cx_logical_result: cross cp_operation, cp_result_zero;
        
        option.per_instance = 1;
        option.name = "logical_coverage";
    endgroup
    
    // Compare operation coverage
    covergroup cg_compare @(posedge clk iff (sample_enable && rst_n && (opcode == CMP)));
        cp_signed_mode: coverpoint signed_op {
            bins unsigned_cmp = {0};
            bins signed_cmp = {1};
        }
        
        cp_result: coverpoint result[0] {
            bins less_than = {1};
            bins not_less_than = {0};
        }
        
        cx_compare: cross cp_signed_mode, cp_result;
        
        option.per_instance = 1;
        option.name = "compare_coverage";
    endgroup
    
    // Cross coverage between operations and signed mode
    covergroup cg_cross_coverage @(posedge clk iff (sample_enable && rst_n));
        cp_opcode: coverpoint opcode;
        cp_signed: coverpoint signed_op;
        cx_op_signed: cross cp_opcode, cp_signed;
        
        option.per_instance = 1;
        option.name = "cross_coverage";
    endgroup
    
    // ========================================================================
    // Coverage instantiation
    // ========================================================================
    
    cg_operations      cov_operations;
    cg_operand_values  cov_operand_values;
    cg_flags           cov_flags;
    cg_arithmetic      cov_arithmetic;
    cg_shifts          cov_shifts;
    cg_logical         cov_logical;
    cg_compare         cov_compare;
    cg_cross_coverage  cov_cross;
    
    initial begin
        cov_operations = new();
        cov_operand_values = new();
        cov_flags = new();
        cov_arithmetic = new();
        cov_shifts = new();
        cov_logical = new();
        cov_compare = new();
        cov_cross = new();
    end
    
    // ========================================================================
    // Coverage reporting
    // ========================================================================
    
    task automatic report_coverage();
        real total_coverage;
        
        $display("");
        $display("========================================");
        $display("Functional Coverage Report");
        $display("========================================");
        $display("Operation Coverage: %0.2f%%", cov_operations.get_coverage());
        $display("Operand Value Coverage: %0.2f%%", cov_operand_values.get_coverage());
        $display("Flag Coverage: %0.2f%%", cov_flags.get_coverage());
        $display("Arithmetic Coverage: %0.2f%%", cov_arithmetic.get_coverage());
        $display("Shift Coverage: %0.2f%%", cov_shifts.get_coverage());
        $display("Logical Coverage: %0.2f%%", cov_logical.get_coverage());
        $display("Compare Coverage: %0.2f%%", cov_compare.get_coverage());
        $display("Cross Coverage: %0.2f%%", cov_cross.get_coverage());
        
        total_coverage = (cov_operations.get_coverage() * 0.25 +
                         cov_operand_values.get_coverage() * 0.25 +
                         cov_flags.get_coverage() * 0.20 +
                         cov_arithmetic.get_coverage() * 0.10 +
                         cov_shifts.get_coverage() * 0.05 +
                         cov_logical.get_coverage() * 0.05 +
                         cov_compare.get_coverage() * 0.05 +
                         cov_cross.get_coverage() * 0.05);
        
        $display("----------------------------------------");
        $display("Weighted Total Coverage: %0.2f%%", total_coverage);
        $display("========================================");
        $display("");
    endtask

endmodule : alu_coverage
