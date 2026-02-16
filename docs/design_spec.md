# Parameterized ALU - Design Specification

**Version**: 1.0  
**Date**: February 2026  
**Author**: ASIC Design Team  

## 1. Introduction

### 1.1 Purpose
This document specifies the architectural and functional requirements for a parameterized Arithmetic Logic Unit (ALU) suitable for integration into processor datapaths, DSP pipelines, or custom compute accelerators.

### 1.2 Scope
The specification covers:
- Functional operation of all ALU instructions
- Interface signals and timing
- Parameterization and configurability
- Flag generation logic
- Error detection mechanisms
- Design constraints and limitations

### 1.3 Document Conventions
- `signal_name`: RTL signal names in monospace
- **UPPERCASE**: Parameters and constants
- *Italics*: Emphasis on key concepts

## 2. Architectural Overview

### 2.1 High-Level Architecture

The ALU is implemented as a pure combinational logic block with the following characteristics:
- Zero-latency operation (output valid same cycle as input)
- Parameterized data width
- Eight fundamental operations
- Comprehensive flag generation
- Signed and unsigned operation support

### 2.2 Design Philosophy

**Key Principles:**
1. **Simplicity**: Combinational design eliminates pipeline complexity
2. **Flexibility**: Width parameterization supports multiple use cases
3. **Completeness**: All standard ALU operations included
4. **Observability**: Comprehensive flag set for status monitoring
5. **Synthesizability**: Technology-independent, lint-clean RTL

## 3. Functional Specification

### 3.1 Operation Set

#### 3.1.1 ADD (Opcode: 3'b000)
```
result = operand_a + operand_b
```
- **Signed Mode**: Two's complement addition
- **Unsigned Mode**: Binary addition
- **Flags Updated**: Zero, Carry, Overflow, Negative
- **Overflow Detection**: 
  - Signed: `(a[MSB] == b[MSB]) && (result[MSB] != a[MSB])`
  - Unsigned: Carry-out from MSB
- **Use Cases**: Address calculation, accumulation, increment

#### 3.1.2 SUB (Opcode: 3'b001)
```
result = operand_a - operand_b
```
- **Implementation**: `operand_a + (~operand_b) + 1` (two's complement)
- **Signed Mode**: Two's complement subtraction
- **Unsigned Mode**: Binary subtraction with borrow
- **Flags Updated**: Zero, Carry (borrow), Overflow, Negative
- **Overflow Detection**: Similar to ADD with inverted operand_b
- **Use Cases**: Pointer arithmetic, loop counters, decrement

#### 3.1.3 AND (Opcode: 3'b010)
```
result = operand_a & operand_b
```
- **Bitwise Operation**: Independent per-bit AND
- **Flags Updated**: Zero, Negative
- **Use Cases**: Bit masking, flag testing, clearing bits

#### 3.1.4 OR (Opcode: 3'b011)
```
result = operand_a | operand_b
```
- **Bitwise Operation**: Independent per-bit OR
- **Flags Updated**: Zero, Negative
- **Use Cases**: Bit setting, flag merging, masking

#### 3.1.5 XOR (Opcode: 3'b100)
```
result = operand_a ^ operand_b
```
- **Bitwise Operation**: Independent per-bit XOR
- **Flags Updated**: Zero, Negative
- **Use Cases**: Bit toggling, compare for equality, checksum

#### 3.1.6 SLL - Shift Left Logical (Opcode: 3'b101)
```
result = operand_a << operand_b[4:0]
```
- **Shift Amount**: Lower 5 bits of operand_b (0-31 positions)
- **Fill Bits**: Zero-filled from right
- **Flags Updated**: Zero, Negative
- **Note**: Shift amounts ≥ WIDTH result in all zeros
- **Use Cases**: Multiplication by powers of 2, bit positioning

#### 3.1.7 SRL - Shift Right Logical (Opcode: 3'b110)
```
result = operand_a >> operand_b[4:0]
```
- **Shift Amount**: Lower 5 bits of operand_b (0-31 positions)
- **Fill Bits**: Zero-filled from left
- **Flags Updated**: Zero, Negative
- **Note**: Shift amounts ≥ WIDTH result in all zeros
- **Use Cases**: Division by powers of 2, bit extraction

#### 3.1.8 CMP - Compare (Opcode: 3'b111)
```
result = (operand_a < operand_b) ? 1 : 0
```
- **Signed Mode**: Signed comparison
- **Unsigned Mode**: Unsigned comparison
- **Result**: 1 if a < b, else 0
- **Flags Updated**: Zero (result is 0), Negative (result[MSB])
- **Use Cases**: Conditional branches, min/max operations

### 3.2 Flag Specifications

#### 3.2.1 Zero Flag (Z)
- **Condition**: `result == 0` (all bits zero)
- **Updated By**: All operations
- **Purpose**: Equality detection, loop termination

#### 3.2.2 Carry Flag (C)
- **Condition**: Carry-out from MSB position
- **Updated By**: ADD, SUB only
- **Purpose**: Multi-precision arithmetic, unsigned overflow detection
- **Note**: 
  - ADD: True carry-out
  - SUB: Inverted borrow (1 = no borrow)

#### 3.2.3 Overflow Flag (V)
- **Condition**: Signed arithmetic overflow
- **Updated By**: ADD, SUB only
- **Detection Logic**:
```systemverilog
  overflow = (operand_a[MSB] == operand_b[MSB]) && 
             (result[MSB] != operand_a[MSB])
```
- **Purpose**: Signed arithmetic error detection
- **Note**: Only meaningful in signed mode

#### 3.2.4 Negative Flag (N)
- **Condition**: `result[MSB] == 1`
- **Updated By**: All operations
- **Purpose**: Sign detection, conditional branches
- **Note**: Only meaningful in signed interpretation

## 4. Interface Specification

### 4.1 Port Definitions
```systemverilog
module param_alu #(
    parameter int WIDTH = 32
) (
    input  logic [WIDTH-1:0]   operand_a,    // First operand
    input  logic [WIDTH-1:0]   operand_b,    // Second operand
    input  alu_pkg::opcode_e   opcode,       // Operation select
    input  logic               signed_op,    // 1=signed, 0=unsigned
    output logic [WIDTH-1:0]   result,       // Operation result
    output alu_pkg::flags_t    flags         // Status flags {Z,C,V,N}
);
```

### 4.2 Signal Descriptions

| Signal | Direction | Width | Type | Description |
|--------|-----------|-------|------|-------------|
| operand_a | Input | WIDTH | logic | Primary operand (left-hand side) |
| operand_b | Input | WIDTH | logic | Secondary operand (right-hand side) |
| opcode | Input | 3 | enum | Operation selector (8 operations) |
| signed_op | Input | 1 | logic | Signed(1) or Unsigned(0) operation |
| result | Output | WIDTH | logic | Computation result |
| flags | Output | 4 | struct | Status flags {zero, carry, overflow, negative} |

### 4.3 Timing Specifications

#### 4.3.1 Combinational Timing
- **Propagation Delay**: Input to output path is purely combinational
- **Setup/Hold**: N/A (no clock or registers in ALU core)
- **Critical Path**: Typically through adder-subtractor and overflow logic

#### 4.3.2 Integration Timing
When integrated into clocked designs:
- All inputs must be stable before clock edge
- Outputs valid within propagation delay after inputs change
- Recommended: Register inputs and outputs in parent module

## 5. Parameter Configuration

### 5.1 WIDTH Parameter

**Type**: `parameter int`  
**Default**: 32  
**Valid Range**: 8 to 64 bits  
**Description**: Data path width in bits

**Configuration Guidelines:**
- **8-bit**: Embedded systems, character processing
- **16-bit**: DSP applications, audio processing
- **32-bit**: General-purpose computing, standard processors
- **64-bit**: High-performance computing, 64-bit architectures

**Synthesis Impact:**
| WIDTH | Area (relative) | Critical Path | Power |
|-------|-----------------|---------------|-------|
| 8     | 1.0x           | Baseline      | 1.0x  |
| 16    | 2.1x           | +15%          | 2.2x  |
| 32    | 4.3x           | +25%          | 4.5x  |
| 64    | 8.8x           | +35%          | 9.1x  |

## 6. Design Constraints

### 6.1 Functional Constraints
1. **Single-Cycle Operation**: All operations complete in one combinational evaluation
2. **No State**: ALU maintains no internal state between operations
3. **No Clock**: Pure combinational logic (clock added by integrator if needed)
4. **Fixed-Point Only**: No floating-point support

### 6.2 Physical Constraints
1. **Technology Independence**: RTL is library-agnostic
2. **Synthesis**: Requires standard cell library with adders, multiplexers, logic gates
3. **Timing**: Critical path scales with WIDTH (adder dominates)
4. **Area**: Linear scaling with WIDTH for most operations

### 6.3 Integration Constraints
1. **Input Stability**: Inputs must remain stable during combinational evaluation
2. **Output Validity**: Outputs settle after propagation delay
3. **No Glitch Protection**: Integrator must register outputs if glitch-free operation required
4. **Reset**: No internal reset (stateless design)

## 7. Verification Strategy

### 7.1 Verification Approach
- Self-checking testbench with golden model
- Constrained random stimulus generation
- Directed tests for corner cases
- Assertion-based property checking

### 7.2 Coverage Metrics
- 100% code coverage (line, branch, toggle)
- >95% functional coverage (all operations × all data patterns)
- All corner cases validated

## 8. Revision History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 0.1 | Jan 2026 | Design Team | Initial draft |
| 1.0 | Feb 2026 | Design Team | Release version |

---
**End of Design Specification**
