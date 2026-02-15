// ============================================================================
// Package: alu_tb_pkg
// Description: Testbench package containing transaction class and utilities
// Author: Verification Team
// Date: February 2026
// ============================================================================

package alu_tb_pkg;
    
    import alu_pkg::*;
    
    // ========================================================================
    // Parameters
    // ========================================================================
    
    parameter int DEFAULT_WIDTH = 32;
    parameter int MAX_TESTS = 10000;
    parameter int TIMEOUT_CYCLES = 1000;
    
    // ========================================================================
    // Transaction Class
    // ========================================================================
    
    class alu_transaction #(int WIDTH = 32);
        
        // Transaction fields
        rand bit [WIDTH-1:0]  operand_a;
        rand bit [WIDTH-1:0]  operand_b;
        rand opcode_e         opcode;
        rand bit              signed_op;
        
        // Expected results (filled by golden model)
        bit [WIDTH-1:0]       expected_result;
        flags_t               expected_flags;
        
        // Actual results (filled by monitor)
        bit [WIDTH-1:0]       actual_result;
        flags_t               actual_flags;
        
        // Transaction metadata
        int                   transaction_id;
        time                  timestamp;
        
        // ====================================================================
        // Constraints
        // ====================================================================
        
        // Operand distribution: bias toward interesting values
        constraint c_operand_distribution {
            operand_a dist {
                0 := 5,
                [1:10] := 10,
                [(2**(WIDTH-1))-5:(2**(WIDTH-1))+5] := 15,
                [(2**WIDTH)-10:(2**WIDTH)-1] := 10,
                {[WIDTH-1:0]{1'b1}} := 5
            };
            
            operand_b dist {
                0 := 5,
                [1:10] := 10,
                [(2**(WIDTH-1))-5:(2**(WIDTH-1))+5] := 15,
                [(2**WIDTH)-10:(2**WIDTH)-1] := 10,
                {[WIDTH-1:0]{1'b1}} := 5
            };
        }
        
        // Operation distribution: more arithmetic operations
        constraint c_opcode_distribution {
            opcode dist {
                ADD := 25,
                SUB := 25,
                AND := 10,
                OR  := 10,
                XOR := 10,
                SLL := 8,
                SRL := 8,
                CMP := 4
            };
        }
        
        // Signed operation distribution
        constraint c_signed_distribution {
            signed_op dist {0 := 50, 1 := 50};
        }
        
        // Shift amount constraint (for shift operations)
        constraint c_shift_amount {
            if (opcode inside {SLL, SRL}) {
                operand_b[4:0] dist {
                    0 := 10,
                    [1:7] := 30,
                    [8:23] := 40,
                    [24:31] := 20
                };
            }
        }
        
        // ====================================================================
        // Methods
        // ====================================================================
        
        // Constructor
        function new();
            transaction_id = 0;
            timestamp = $time;
        endfunction
        
        // Deep copy
        function alu_transaction copy();
            alu_transaction t = new();
            t.operand_a = this.operand_a;
            t.operand_b = this.operand_b;
            t.opcode = this.opcode;
            t.signed_op = this.signed_op;
            t.expected_result = this.expected_result;
            t.expected_flags = this.expected_flags;
            t.actual_result = this.actual_result;
            t.actual_flags = this.actual_flags;
            t.transaction_id = this.transaction_id;
            t.timestamp = this.timestamp;
            return t;
        endfunction
        
        // Display transaction
        function void display(string prefix = "");
            $display("%s Transaction ID: %0d", prefix, transaction_id);
            $display("%s   Timestamp: %0t", prefix, timestamp);
            $display("%s   Opcode: %s (%b)", prefix, opcode_to_string(opcode), opcode);
            $display("%s   Signed: %b", prefix, signed_op);
            $display("%s   Operand A: 0x%0h (%0d)", prefix, operand_a, operand_a);
            $display("%s   Operand B: 0x%0h (%0d)", prefix, operand_b, operand_b);
            $display("%s   Result: 0x%0h (%0d)", prefix, actual_result, actual_result);
            $display("%s   Flags: Z=%b C=%b V=%b N=%b", prefix, 
                     actual_flags.zero, actual_flags.carry, 
                     actual_flags.overflow, actual_flags.negative);
        endfunction
        
        // Compare expected vs actual
        function bit compare();
            bit match = 1;
            if (expected_result !== actual_result) begin
                $error("Result mismatch: Expected=0x%0h, Got=0x%0h", 
                       expected_result, actual_result);
                match = 0;
            end
            if (expected_flags !== actual_flags) begin
                $error("Flag mismatch: Expected=%b, Got=%b", 
                       expected_flags, actual_flags);
                match = 0;
            end
            return match;
        endfunction
        
    endclass : alu_transaction
    
    // ========================================================================
    // Utility Functions
    // ========================================================================
    
    // Golden model for ALU computation
    function automatic void compute_golden_model(
        input  int WIDTH,
        input  bit [WIDTH-1:0] a,
        input  bit [WIDTH-1:0] b,
        input  opcode_e op,
        input  bit signed_mode,
        output bit [WIDTH-1:0] result,
        output flags_t flags
    );
        bit [WIDTH:0] extended_result;
        bit signed [WIDTH-1:0] a_signed, b_signed, result_signed;
        
        // Cast to signed for signed operations
        a_signed = signed'(a);
        b_signed = signed'(b);
        
        // Compute result based on operation
        case (op)
            ADD: begin
                extended_result = {1'b0, a} + {1'b0, b};
                result = extended_result[WIDTH-1:0];
                flags.carry = extended_result[WIDTH];
                flags.overflow = (a[WIDTH-1] == b[WIDTH-1]) && 
                                 (result[WIDTH-1] != a[WIDTH-1]) && signed_mode;
            end
            
            SUB: begin
                extended_result = {1'b0, a} + {1'b0, ~b} + 1'b1;
                result = extended_result[WIDTH-1:0];
                flags.carry = extended_result[WIDTH];
                flags.overflow = (a[WIDTH-1] != b[WIDTH-1]) && 
                                 (result[WIDTH-1] != a[WIDTH-1]) && signed_mode;
            end
            
            AND: begin
                result = a & b;
                flags.carry = 0;
                flags.overflow = 0;
            end
            
            OR: begin
                result = a | b;
                flags.carry = 0;
                flags.overflow = 0;
            end
            
            XOR: begin
                result = a ^ b;
                flags.carry = 0;
                flags.overflow = 0;
            end
            
            SLL: begin
                result = a << b[4:0];
                flags.carry = 0;
                flags.overflow = 0;
            end
            
            SRL: begin
                result = a >> b[4:0];
                flags.carry = 0;
                flags.overflow = 0;
            end
            
            CMP: begin
                if (signed_mode) begin
                    result = {{(WIDTH-1){1'b0}}, (a_signed < b_signed)};
                end else begin
                    result = {{(WIDTH-1){1'b0}}, (a < b)};
                end
                flags.carry = 0;
                flags.overflow = 0;
            end
            
            default: begin
                result = '0;
                flags.carry = 0;
                flags.overflow = 0;
            end
        endcase
        
        // Common flags
        flags.zero = (result == 0);
        flags.negative = result[WIDTH-1];
        
    endfunction
    
    // Random delay generator for realistic timing
    function automatic int get_random_delay(int min_delay, int max_delay);
        return $urandom_range(min_delay, max_delay);
    endfunction
    
endpackage : alu_tb_pkg
