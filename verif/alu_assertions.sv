// ============================================================================
// Module: alu_assertions
// Description: SystemVerilog Assertions (SVA) for ALU verification
// Author: Verification Team
// Date: February 2026
// ============================================================================

module alu_assertions 
    import alu_pkg::*;
#(
    parameter int WIDTH = 32
) (
    input  logic clk,
    input  logic rst_n,
    
    // DUT interface
    input  logic [WIDTH-1:0]   operand_a,
    input  logic [WIDTH-1:0]   operand_b,
    input  opcode_e            opcode,
    input  logic               signed_op,
    input  logic [WIDTH-1:0]   result,
    input  flags_t             flags
);

    // ========================================================================
    // Property: No X or Z in outputs
    // ========================================================================
    
    property p_no_x_in_result;
        @(posedge clk) disable iff (!rst_n)
        !$isunknown(result);
    endproperty
    
    property p_no_x_in_flags;
        @(posedge clk) disable iff (!rst_n)
        !$isunknown(flags);
    endproperty
    
    assert_no_x_result: assert property (p_no_x_in_result)
        else $error("Result contains X or Z");
    
    assert_no_x_flags: assert property (p_no_x_in_flags)
        else $error("Flags contain X or Z");
    
    // ========================================================================
    // Property: Zero flag consistency
    // ========================================================================
    
    property p_zero_flag_set;
        @(posedge clk) disable iff (!rst_n)
        (result == 0) |-> (flags.zero == 1);
    endproperty
    
    property p_zero_flag_clear;
        @(posedge clk) disable iff (!rst_n)
        (result != 0) |-> (flags.zero == 0);
    endproperty
    
    assert_zero_flag_set: assert property (p_zero_flag_set)
        else $error("Zero flag not set when result is zero");
    
    assert_zero_flag_clear: assert property (p_zero_flag_clear)
        else $error("Zero flag set when result is non-zero");
    
    // ========================================================================
    // Property: Carry flag only for arithmetic operations
    // ========================================================================
    
    property p_carry_only_arithmetic;
        @(posedge clk) disable iff (!rst_n)
        (opcode inside {AND, OR, XOR, SLL, SRL, CMP}) |-> (flags.carry == 0);
    endproperty
    
    assert_carry_only_arithmetic: assert property (p_carry_only_arithmetic)
        else $error("Carry flag set for non-arithmetic operation: %s", opcode_to_string(opcode));
    
    // ========================================================================
    // Property: Overflow flag only for signed arithmetic
    // ========================================================================
    
    property p_overflow_only_signed_arithmetic;
        @(posedge clk) disable iff (!rst_n)
        (!signed_op || !(opcode inside {ADD, SUB})) |-> (flags.overflow == 0);
    endproperty
    
    assert_overflow_only_signed: assert property (p_overflow_only_signed_arithmetic)
        else $error("Overflow flag set for unsigned or non-arithmetic operation");
    
    // ========================================================================
    // Property: Negative flag matches MSB
    // ========================================================================
    
    property p_negative_flag_matches_msb;
        @(posedge clk) disable iff (!rst_n)
        flags.negative == result[WIDTH-1];
    endproperty
    
    assert_negative_msb: assert property (p_negative_flag_matches_msb)
        else $error("Negative flag doesn't match result MSB");
    
    // ========================================================================
    // Property: XOR with self produces zero
    // ========================================================================
    
    property p_xor_self_zero;
        @(posedge clk) disable iff (!rst_n)
        (opcode == XOR && operand_a == operand_b) |-> (result == 0);
    endproperty
    
    assert_xor_self: assert property (p_xor_self_zero)
        else $error("XOR with self didn't produce zero");
    
    // ========================================================================
    // Property: AND with zero produces zero
    // ========================================================================
    
    property p_and_with_zero;
        @(posedge clk) disable iff (!rst_n)
        (opcode == AND && (operand_a == 0 || operand_b == 0)) |-> (result == 0);
    endproperty
    
    assert_and_zero: assert property (p_and_with_zero)
        else $error("AND with zero didn't produce zero");
    
    // ========================================================================
    // Property: OR with zero is identity
    // ========================================================================
    
    property p_or_with_zero_identity;
        @(posedge clk) disable iff (!rst_n)
        (opcode == OR && operand_b == 0) |-> (result == operand_a);
    endproperty
    
    assert_or_identity: assert property (p_or_with_zero_identity)
        else $error("OR with zero didn't preserve operand_a");
    
    // ========================================================================
    // Property: Shift by >= WIDTH produces zero
    // ========================================================================
    
    property p_shift_overflow_zero;
        @(posedge clk) disable iff (!rst_n)
        ((opcode inside {SLL, SRL}) && (operand_b[4:0] >= WIDTH)) |-> (result == 0);
    endproperty
    
    assert_shift_overflow: assert property (p_shift_overflow_zero)
        else $error("Shift by >= WIDTH didn't produce zero");
    
    // ========================================================================
    // Property: Compare result is always 0 or 1
    // ========================================================================
    
    property p_compare_binary_result;
        @(posedge clk) disable iff (!rst_n)
        (opcode == CMP) |-> (result inside {0, 1});
    endproperty
    
    assert_compare_binary: assert property (p_compare_binary_result)
        else $error("Compare result is not binary (0 or 1)");
    
    // ========================================================================
    // Property: Addition overflow detection
    // ========================================================================
    
    property p_add_overflow_positive;
        @(posedge clk) disable iff (!rst_n)
        (opcode == ADD && signed_op && 
         operand_a[WIDTH-1] == 0 && operand_b[WIDTH-1] == 0 && result[WIDTH-1] == 1) 
        |-> (flags.overflow == 1);
    endproperty
    
    property p_add_overflow_negative;
        @(posedge clk) disable iff (!rst_n)
        (opcode == ADD && signed_op && 
         operand_a[WIDTH-1] == 1 && operand_b[WIDTH-1] == 1 && result[WIDTH-1] == 0) 
        |-> (flags.overflow == 1);
    endproperty
    
    assert_add_overflow_pos: assert property (p_add_overflow_positive)
        else $error("Overflow not detected for positive + positive = negative");
    
    assert_add_overflow_neg: assert property (p_add_overflow_negative)
        else $error("Overflow not detected for negative + negative = positive");
    
    // ========================================================================
    // Property: Subtraction overflow detection
    // ========================================================================
    
    property p_sub_overflow_pos_minus_neg;
        @(posedge clk) disable iff (!rst_n)
        (opcode == SUB && signed_op && 
         operand_a[WIDTH-1] == 0 && operand_b[WIDTH-1] == 1 && result[WIDTH-1] == 1) 
        |-> (flags.overflow == 1);
    endproperty
    
    property p_sub_overflow_neg_minus_pos;
        @(posedge clk) disable iff (!rst_n)
        (opcode == SUB && signed_op && 
         operand_a[WIDTH-1] == 1 && operand_b[WIDTH-1] == 0 && result[WIDTH-1] == 0) 
        |-> (flags.overflow == 1);
    endproperty
    
    assert_sub_overflow_pos_neg: assert property (p_sub_overflow_pos_minus_neg)
        else $error("Overflow not detected for positive - negative = negative");
    
    assert_sub_overflow_neg_pos: assert property (p_sub_overflow_neg_minus_pos)
        else $error("Overflow not detected for negative - positive = positive");
    
    // ========================================================================
    // Coverage: Assert exercised count
    // ========================================================================
    
    cover_zero_flag_set: cover property (p_zero_flag_set);
    cover_carry_set: cover property (@(posedge clk) (flags.carry == 1));
    cover_overflow_set: cover property (@(posedge clk) (flags.overflow == 1));
    cover_all_operations: cover property (@(posedge clk) (opcode == $past(opcode) + 1));

endmodule : alu_assertions
