// ============================================================================
// Module: param_alu
// Description: Parameterized Arithmetic Logic Unit (ALU)
//              Supports 8 operations with configurable data width
// Author: ASIC Design Team
// Date: February 2026
// ============================================================================
// Features:
// - Parameterized data width (WIDTH)
// - Eight operations: ADD, SUB, AND, OR, XOR, SLL, SRL, CMP
// - Signed and unsigned operation support
// - Comprehensive flag generation (Zero, Carry, Overflow, Negative)
// - Pure combinational logic (zero latency)
// - Synthesizable, lint-clean SystemVerilog
// ============================================================================

module param_alu 
    import alu_pkg::*;
#(
    parameter int WIDTH = 32  // Data path width (8 to 64 bits)
) (
    // Input operands
    input  logic [WIDTH-1:0]   operand_a,    // First operand
    input  logic [WIDTH-1:0]   operand_b,    // Second operand
    
    // Control signals
    input  opcode_e            opcode,       // Operation selector
    input  logic               signed_op,    // 1=signed, 0=unsigned
    
    // Output results
    output logic [WIDTH-1:0]   result,       // Computation result
    output flags_t             flags         // Status flags {Z,C,V,N}
);

    // ========================================================================
    // Internal signals
    // ========================================================================
    
    // Intermediate results for each operation
    logic [WIDTH-1:0]   add_result;
    logic [WIDTH-1:0]   sub_result;
    logic [WIDTH-1:0]   and_result;
    logic [WIDTH-1:0]   or_result;
    logic [WIDTH-1:0]   xor_result;
    logic [WIDTH-1:0]   sll_result;
    logic [WIDTH-1:0]   srl_result;
    logic [WIDTH-1:0]   cmp_result;
    
    // Arithmetic operation signals
    logic               add_carry;
    logic               sub_carry;
    logic               add_overflow;
    logic               sub_overflow;
    
    // Extended operands for carry/overflow detection
    logic [WIDTH:0]     operand_a_ext;
    logic [WIDTH:0]     operand_b_ext;
    logic [WIDTH:0]     add_result_ext;
    logic [WIDTH:0]     sub_result_ext;
    
    // Comparison signals
    logic               cmp_less_unsigned;
    logic               cmp_less_signed;
    
    // ========================================================================
    // Arithmetic Operations (ADD, SUB)
    // ========================================================================
    
    // Addition with carry detection
    // Extend operands to WIDTH+1 bits for carry-out detection
    assign operand_a_ext = {1'b0, operand_a};
    assign operand_b_ext = {1'b0, operand_b};
    assign add_result_ext = operand_a_ext + operand_b_ext;
    assign add_result = add_result_ext[WIDTH-1:0];
    assign add_carry = add_result_ext[WIDTH];
    
    // Overflow detection for signed addition
    // Overflow occurs when:
    // - Adding two positive numbers yields negative result
    // - Adding two negative numbers yields positive result
    assign add_overflow = (operand_a[WIDTH-1] == operand_b[WIDTH-1]) && 
                          (add_result[WIDTH-1] != operand_a[WIDTH-1]);
    
    // Subtraction with borrow detection
    // Implemented as: A - B = A + (~B) + 1
    assign sub_result_ext = operand_a_ext + (~operand_b_ext) + 1'b1;
    assign sub_result = sub_result_ext[WIDTH-1:0];
    assign sub_carry = sub_result_ext[WIDTH];  // Inverted borrow
    
    // Overflow detection for signed subtraction
    // Overflow occurs when:
    // - Subtracting negative from positive yields negative
    // - Subtracting positive from negative yields positive
    assign sub_overflow = (operand_a[WIDTH-1] != operand_b[WIDTH-1]) && 
                          (sub_result[WIDTH-1] != operand_a[WIDTH-1]);
    
    // ========================================================================
    // Logical Operations (AND, OR, XOR)
    // ========================================================================
    
    assign and_result = operand_a & operand_b;
    assign or_result  = operand_a | operand_b;
    assign xor_result = operand_a ^ operand_b;
    
    // ========================================================================
    // Shift Operations (SLL, SRL)
    // ========================================================================
    
    // Shift amount is lower 5 bits of operand_b (0 to 31 positions)
    // For WIDTH < 32, shifts >= WIDTH result in zero
    assign sll_result = operand_a << operand_b[4:0];
    assign srl_result = operand_a >> operand_b[4:0];
    
    // ========================================================================
    // Compare Operation (CMP)
    // ========================================================================
    
    // Unsigned comparison: direct magnitude comparison
    assign cmp_less_unsigned = (operand_a < operand_b);
    
    // Signed comparison: account for two's complement representation
    // Use subtraction overflow logic for accurate signed comparison
    assign cmp_less_signed = (operand_a[WIDTH-1] != operand_b[WIDTH-1]) ? 
                              operand_a[WIDTH-1] :  // Different signs: negative < positive
                              (operand_a < operand_b);  // Same sign: magnitude comparison
    
    // Compare result: 1 if less than, 0 otherwise
    assign cmp_result = {{(WIDTH-1){1'b0}}, 
                         signed_op ? cmp_less_signed : cmp_less_unsigned};
    
    // ========================================================================
    // Result Multiplexer
    // ========================================================================
    
    // Select result based on operation code
    always_comb begin
        case (opcode)
            ADD:     result = add_result;
            SUB:     result = sub_result;
            AND:     result = and_result;
            OR:      result = or_result;
            XOR:     result = xor_result;
            SLL:     result = sll_result;
            SRL:     result = srl_result;
            CMP:     result = cmp_result;
            default: result = {WIDTH{1'b0}};  // Default to zero for undefined opcodes
        endcase
    end
    
    // ========================================================================
    // Flag Generation
    // ========================================================================
    
    // Zero flag: Set when result is all zeros
    assign flags.zero = (result == {WIDTH{1'b0}});
    
    // Carry flag: Set on carry out from MSB (ADD/SUB only)
    always_comb begin
        case (opcode)
            ADD:     flags.carry = add_carry;
            SUB:     flags.carry = sub_carry;
            default: flags.carry = 1'b0;
        endcase
    end
    
    // Overflow flag: Set on signed arithmetic overflow (ADD/SUB only)
    always_comb begin
        if (signed_op) begin
            case (opcode)
                ADD:     flags.overflow = add_overflow;
                SUB:     flags.overflow = sub_overflow;
                default: flags.overflow = 1'b0;
            endcase
        end else begin
            // Unsigned operations don't have overflow (use carry instead)
            flags.overflow = 1'b0;
        end
    end
    
    // Negative flag: Set when MSB of result is 1
    assign flags.negative = result[WIDTH-1];
    
    // ========================================================================
    // Assertions for design validation
    // ========================================================================
    
    // pragma translate_off
    
    // Check for X or Z propagation (should never occur in synthesized design)
    always_comb begin
        assert (!$isunknown(result)) 
            else $error("Result contains X or Z");
        assert (!$isunknown(flags)) 
            else $error("Flags contain X or Z");
    end
    
    // Verify zero flag consistency
    property p_zero_flag_correct;
        @(result) (result == 0) |-> (flags.zero == 1);
    endproperty
    assert property (p_zero_flag_correct)
        else $error("Zero flag incorrect when result is zero");
    
    // Verify carry flag only set for arithmetic operations
    property p_carry_only_arithmetic;
        @(opcode) (opcode inside {AND, OR, XOR, SLL, SRL, CMP}) |-> (flags.carry == 0);
    endproperty
    assert property (p_carry_only_arithmetic)
        else $error("Carry flag set for non-arithmetic operation");
    
    // pragma translate_on

endmodule : param_alu
