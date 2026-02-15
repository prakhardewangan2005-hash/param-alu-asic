// ============================================================================
// Package: alu_pkg
// Description: Package containing type definitions for parameterized ALU
// Author: ASIC Design Team
// Date: February 2026
// ============================================================================

package alu_pkg;

    // Operation codes for ALU
    typedef enum logic [2:0] {
        ADD = 3'b000,  // Addition
        SUB = 3'b001,  // Subtraction
        AND = 3'b010,  // Bitwise AND
        OR  = 3'b011,  // Bitwise OR
        XOR = 3'b100,  // Bitwise XOR
        SLL = 3'b101,  // Shift Left Logical
        SRL = 3'b110,  // Shift Right Logical
        CMP = 3'b111   // Compare (less than)
    } opcode_e;

    // ALU status flags structure
    typedef struct packed {
        logic zero;      // Z: Result is zero
        logic carry;     // C: Carry out (ADD/SUB only)
        logic overflow;  // V: Signed overflow (ADD/SUB only)
        logic negative;  // N: Result is negative (MSB = 1)
    } flags_t;

    // Function to convert opcode enum to string (for debugging)
    function automatic string opcode_to_string(opcode_e op);
        case (op)
            ADD: return "ADD";
            SUB: return "SUB";
            AND: return "AND";
            OR:  return "OR";
            XOR: return "XOR";
            SLL: return "SLL";
            SRL: return "SRL";
            CMP: return "CMP";
            default: return "UNKNOWN";
        endcase
    endfunction

    // Function to check if operation updates carry flag
    function automatic logic updates_carry(opcode_e op);
        return (op == ADD) || (op == SUB);
    endfunction

    // Function to check if operation updates overflow flag
    function automatic logic updates_overflow(opcode_e op);
        return (op == ADD) || (op == SUB);
    endfunction

endpackage : alu_pkg
