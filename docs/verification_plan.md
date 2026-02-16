# Parameterized ALU - Verification Plan

**Version**: 1.0  
**Date**: February 2026  
**Status**: Released  

## 1. Executive Summary

This document outlines the comprehensive verification strategy for the parameterized ALU design. The verification approach follows industry-standard methodologies including constrained random testing, directed testing, assertion-based verification, and functional coverage closure.

**Verification Goals:**
- Achieve >95% functional coverage
- 100% code coverage (line, branch, toggle)
- Zero functional bugs in final RTL
- All assertions passing
- Corner case validation complete

## 2. Verification Strategy

### 2.1 Overall Approach

**Methodology**: Transaction-Level Modeling (TLM) with SystemVerilog
- **Architecture**: Monitor-Driver-Scoreboard pattern
- **Stimulus**: Constrained random + directed tests
- **Checking**: Self-checking with golden reference model
- **Coverage**: Functional coverage + code coverage
- **Assertions**: SVA properties for concurrent checking

### 2.2 Verification Environment Architecture
```
┌─────────────────────────────────────────────────────────┐
│                   alu_tb_top                            │
│                                                         │
│  ┌──────────┐      ┌─────────────┐      ┌──────────┐  │
│  │          │      │             │      │          │  │
│  │  Driver  │─────▶│  DUT (ALU)  │─────▶│ Monitor  │  │
│  │          │      │             │      │          │  │
│  └────┬─────┘      └─────────────┘      └─────┬────┘  │
│       │                                        │       │
│       │            ┌─────────────┐            │       │
│       │            │             │            │       │
│       └───────────▶│ Scoreboard  │◀───────────┘       │
│                    │ (Golden Ref)│                    │
│                    └─────────────┘                    │
│                                                         │
│  ┌──────────────┐         ┌──────────────────┐        │
│  │  Coverage    │         │   Assertions     │        │
│  │  Collector   │         │   (SVA)          │        │
│  └──────────────┘         └──────────────────┘        │
└─────────────────────────────────────────────────────────┘
```

### 2.3 Verification Components

#### 2.3.1 Driver
- **Purpose**: Generate and drive stimulus to DUT
- **Features**:
  - Constrained random transaction generation
  - Configurable test patterns
  - Operation sequence control
  - Randomization constraints

#### 2.3.2 Monitor
- **Purpose**: Capture DUT outputs and convert to transactions
- **Features**:
  - Output sampling
  - Transaction reconstruction
  - Protocol checking
  - Timing validation

#### 2.3.3 Scoreboard
- **Purpose**: Compare DUT output with golden reference
- **Features**:
  - Cycle-accurate golden model
  - Result comparison
  - Flag validation
  - Error reporting with diagnostics

#### 2.3.4 Coverage Collector
- **Purpose**: Measure verification completeness
- **Features**:
  - Operation coverage
  - Data pattern coverage
  - Corner case coverage
  - Cross-coverage analysis

#### 2.3.5 Assertions
- **Purpose**: Concurrent property checking
- **Features**:
  - Result validity checks
  - Flag consistency properties
  - Operational properties
  - X-propagation detection

## 3. Test Plan

### 3.1 Test Categories

#### 3.1.1 Directed Tests
Targeted tests for specific scenarios and corner cases.

| Test ID | Test Name | Description | Operations | Iterations |
|---------|-----------|-------------|------------|------------|
| DIR-001 | Basic Arithmetic | Simple add/sub with small values | ADD, SUB | 20 |
| DIR-002 | Logical Operations | AND/OR/XOR with known patterns | AND, OR, XOR | 24 |
| DIR-003 | Shift Boundaries | Shift by 0, max, and overflow | SLL, SRL | 16 |
| DIR-004 | Signed Overflow | Force signed overflow scenarios | ADD, SUB | 12 |
| DIR-005 | Unsigned Overflow | Force carry-out scenarios | ADD, SUB | 12 |
| DIR-006 | Zero Detection | Operations resulting in zero | ALL | 16 |
| DIR-007 | Max Value Operations | Test with maximum operand values | ALL | 16 |
| DIR-008 | Min Value Operations | Test with minimum operand values | ALL | 16 |
| DIR-009 | Comparison Boundary | CMP at equality and boundaries | CMP | 12 |
| DIR-010 | Mixed Sign | Signed operations with mixed signs | ADD, SUB, CMP | 16 |

**Total Directed Tests**: 160 individual test cases

#### 3.1.2 Constrained Random Tests
Automated random stimulus with intelligent constraints.

**Configuration:**
- **Test Duration**: 1000 operations per seed
- **Seed Sweep**: 100 different seeds
- **Width Variations**: 8-bit, 16-bit, 32-bit, 64-bit
- **Total Simulations**: 400 test runs

**Constraints:**
```systemverilog
// Example constraints (in actual testbench)
constraint operand_dist {
    operand_a dist {
        [0:10] := 10,                    // Small values
        [WIDTH/2-5:WIDTH/2+5] := 20,     // Mid-range
        [WIDTH-10:WIDTH-1] := 10          // Large values
    };
}

constraint opcode_dist {
    opcode dist {
        ADD := 20,
        SUB := 20,
        AND := 10,
        OR  := 10,
        XOR := 10,
        SLL := 10,
        SRL := 10,
        CMP := 10
    };
}
```

#### 3.1.3 Corner Case Tests
Specific scenarios targeting edge conditions.

| Corner Case | Description | Validation |
|-------------|-------------|------------|
| CC-001 | All zeros (a=0, b=0) | Result and flags correct |
| CC-002 | All ones (a=-1, b=-1) | Overflow/carry handled |
| CC-003 | Max positive (signed) | No false overflow |
| CC-004 | Max negative (signed) | Correct negative flag |
| CC-005 | Shift by WIDTH | Result is zero |
| CC-006 | Shift by WIDTH+1 | Result is zero (5-bit mask) |
| CC-007 | XOR with self (a^a) | Result always zero |
| CC-008 | AND with zero | Result always zero |
| CC-009 | OR with all-ones | Result always all-ones |
| CC-010 | Subtract equal values | Zero flag set, no borrow |
| CC-011 | Overflow boundary | Exactly at overflow point |
| CC-012 | Carry propagation | Long carry chains |

### 3.2 Test Execution Plan

#### Phase 1: Directed Testing (Week 1)
- Run all directed tests
- Debug any functional issues
- Achieve basic operation validation

#### Phase 2: Random Testing (Week 2)
- Execute constrained random with seed sweep
- Analyze coverage metrics
- Identify coverage holes

#### Phase 3: Corner Case Validation (Week 2)
- Execute all corner case tests
- Cross-check with assertions
- Validate flag generation

#### Phase 4: Coverage Closure (Week 3)
- Add directed tests for uncovered scenarios
- Re-run random tests with adjusted constraints
- Achieve >95% functional coverage

#### Phase 5: Regression & Sign-off (Week 3)
- Full regression suite (all tests)
- Zero failures requirement
- Documentation completion

## 4. Functional Coverage

### 4.1 Coverage Strategy

**Goal**: >95% functional coverage across all dimensions

### 4.2 Coverage Bins

#### 4.2.1 Operation Coverage
```systemverilog
covergroup op_coverage;
    opcode_cp: coverpoint opcode {
        bins add = {ADD};
        bins sub = {SUB};
        bins and_op = {AND};
        bins or_op = {OR};
        bins xor_op = {XOR};
        bins sll = {SLL};
        bins srl = {SRL};
        bins cmp = {CMP};
    }
endgroup
```
**Target**: 100% (all 8 operations)

#### 4.2.2 Data Pattern Coverage
```systemverilog
covergroup data_patterns;
    operand_a_cp: coverpoint operand_a {
        bins zero = {0};
        bins small = {[1:10]};
        bins mid = {[WIDTH/2-5:WIDTH/2+5]};
        bins large = {[WIDTH-10:WIDTH-1]};
        bins max = {~0};
    }
    // Similar for operand_b
endgroup
```

#### 4.2.3 Flag Coverage
```systemverilog
covergroup flag_coverage;
    zero_cp: coverpoint flags.zero {
        bins set = {1};
        bins clear = {0};
    }
    carry_cp: coverpoint flags.carry;
    overflow_cp: coverpoint flags.overflow;
    negative_cp: coverpoint flags.negative;
endgroup
```

#### 4.2.4 Cross-Coverage
```systemverilog
covergroup cross_coverage;
    opcode_signed: cross opcode, signed_op {
        // Ensure signed/unsigned tested for each operation
    }
    
    opcode_flags: cross opcode, flags.zero, flags.carry {
        // Ensure flag combinations for each operation
        ignore_bins invalid = binsof(opcode) intersect {AND, OR, XOR, SLL, SRL} 
                                  && binsof(flags.carry) intersect {1};
    }
endgroup
```

### 4.3 Coverage Metrics

| Coverage Type | Target | Weight |
|---------------|--------|--------|
| Operation Coverage | 100% | 25% |
| Data Pattern Coverage | >90% | 25% |
| Flag Coverage | 100% | 20% |
| Cross Coverage | >85% | 20% |
| Corner Cases | 100% | 10% |

**Overall Target**: >95% weighted average

## 5. Assertion-Based Verification

### 5.1 Assertion Categories

#### 5.1.1 Result Validity Assertions
```systemverilog
// No X or Z in result (synthesis constraint)
property result_no_x;
    @(operand_a or operand_b or opcode)
    !$isunknown(result);
endproperty

// ADD result bound checking
property add_bounds;
    @(operand_a or operand_b)
    (opcode == ADD) |-> (result <= operand_a + operand_b + 1);
endproperty
```

#### 5.1.2 Flag Consistency Assertions
```systemverilog
// Zero flag consistency
property zero_flag_correct;
    @(result)
    (result == 0) |-> (flags.zero == 1);
endproperty

// Carry only for arithmetic
property carry_only_arithmetic;
    @(opcode)
    (opcode inside {AND, OR, XOR, SLL, SRL, CMP}) |-> (flags.carry == 0);
endproperty
```

#### 5.1.3 Operational Assertions
```systemverilog
// XOR self is zero
property xor_self_zero;
    @(operand_a or operand_b or opcode)
    (opcode == XOR && operand_a == operand_b) |-> (result == 0);
endproperty

// Shift overflow
property shift_overflow_zero;
    @(operand_b or opcode)
    ((opcode inside {SLL, SRL}) && (operand_b[4:0] >= WIDTH)) |-> (result == 0);
endproperty
```

### 5.2 Assertion Execution
- **Concurrent**: All assertions active during simulation
- **Failure Action**: Immediate simulation stop with error report
- **Coverage**: Track assertion exercise count

## 6. Verification Metrics

### 6.1 Code Coverage

**Tools**: QuestaSim/VCS built-in coverage

| Metric | Target | Measurement |
|--------|--------|-------------|
| Line Coverage | 100% | Lines executed |
| Branch Coverage | 100% | All if/case branches |
| Toggle Coverage | >95% | All bits toggled 0→1, 1→0 |
| FSM Coverage | N/A | No FSMs in design |

### 6.2 Bug Tracking

**Bug Severity Classification:**
- **Critical**: Functional incorrectness, simulation crash
- **Major**: Corner case failure, incorrect flag
- **Minor**: Coverage hole, assertion false positive

**Target**: Zero critical/major bugs at tape-out

### 6.3 Regression Metrics

| Metric | Target |
|--------|--------|
| Pass Rate | 100% |
| Runtime (full regression) | <10 minutes |
| Coverage Delta (run-to-run) | <1% |

## 7. Success Criteria

### 7.1 Functional Verification Sign-off Checklist
- [ ] All directed tests passing (100%)
- [ ] Random test pass rate 100% (100/100 seeds)
- [ ] Functional coverage >95%
- [ ] Code coverage: line 100%, branch >98%
- [ ] All assertions passing (zero failures)
- [ ] Corner cases validated (12/12 passing)
- [ ] Scoreboard mismatches: zero
- [ ] Regression runtime <10 minutes
- [ ] Documentation complete

### 7.2 Known Limitations
- Formal verification not included (future enhancement)
- No power-aware simulation
- No timing-annotated gate-level simulation

## 8. Deliverables

- ✅ Verification testbench (SystemVerilog)
- ✅ Test suite (directed + random)
- ✅ Coverage reports
- ✅ Assertion report
- ✅ Regression summary
- ✅ Waveform database (key tests)
- ✅ Verification sign-off document

## 9. Revision History

| Version | Date | Changes |
|---------|------|---------|
| 0.1 | Jan 2026 | Initial draft |
| 1.0 | Feb 2026 | Release version |

---
**End of Verification Plan**
