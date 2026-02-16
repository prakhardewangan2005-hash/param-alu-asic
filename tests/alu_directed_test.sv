// ============================================================================
// Module: alu_directed_test
// Description: Directed test scenarios for ALU verification
// Author: Verification Team
// Date: February 2026
// ============================================================================

module alu_directed_test
    import alu_pkg::*;
    import alu_tb_pkg::*;
;

    // Test vectors for directed testing
    task automatic run_directed_tests(ref alu_driver driver, int WIDTH);
        
        $display("========================================");
        $display("Running Directed Test Suite");
        $display("========================================");
        
        // Test 1: Basic Addition
        test_basic_addition(driver, WIDTH);
        
        // Test 2: Basic Subtraction
        test_basic_subtraction(driver, WIDTH);
        
        // Test 3: Logical Operations
        test_logical_operations(driver, WIDTH);
        
        // Test 4: Shift Operations
        test_shift_operations(driver, WIDTH);
        
        // Test 5: Compare Operations
        test_compare_operations(driver, WIDTH);
        
        // Test 6: Signed Operations
        test_signed_operations(driver, WIDTH);
        
        // Test 7: Overflow Detection
        test_overflow_detection(driver, WIDTH);
        
        // Test 8: Zero Flag
        test_zero_flag(driver, WIDTH);
        
        $display("========================================");
        $display("Directed Tests Generation Complete");
        $display("========================================");
        
    endtask
    
    // ========================================================================
    // Test 1: Basic Addition
    // ========================================================================
    
    task automatic test_basic_addition(ref alu_driver driver, int WIDTH);
        $display("[DIRECTED] Test 1: Basic Addition");
        
        // Simple additions
        driver.generate_directed_transaction(10, 5, ADD, 0);
        driver.generate_directed_transaction(100, 50, ADD, 0);
        driver.generate_directed_transaction(255, 1, ADD, 0);
        
        // Addition with zero
        driver.generate_directed_transaction(0, 0, ADD, 0);
        driver.generate_directed_transaction(42, 0, ADD, 0);
        driver.generate_directed_transaction(0, 42, ADD, 0);
        
    endtask
    
    // ========================================================================
    // Test 2: Basic Subtraction
    // ========================================================================
    
    task automatic test_basic_subtraction(ref alu_driver driver, int WIDTH);
        $display("[DIRECTED] Test 2: Basic Subtraction");
        
        // Simple subtractions
        driver.generate_directed_transaction(10, 5, SUB, 0);
        driver.generate_directed_transaction(100, 50, SUB, 0);
        driver.generate_directed_transaction(255, 255, SUB, 0);
        
        // Subtraction resulting in zero
        driver.generate_directed_transaction(42, 42, SUB, 0);
        
        // Subtraction from zero
        driver.generate_directed_transaction(0, 10, SUB, 0);
        
    endtask
    
    // ========================================================================
    // Test 3: Logical Operations
    // ========================================================================
    
    task automatic test_logical_operations(ref alu_driver driver, int WIDTH);
        $display("[DIRECTED] Test 3: Logical Operations");
        
        bit [WIDTH-1:0] pattern_a, pattern_b;
        
        pattern_a = {WIDTH{1'b1}};  // All ones
        pattern_b = {WIDTH{1'b0}};  // All zeros
        
        // AND operations
        driver.generate_directed_transaction(pattern_a, pattern_a, AND, 0);  // 1 & 1 = 1
        driver.generate_directed_transaction(pattern_a, pattern_b, AND, 0);  // 1 & 0 = 0
        driver.generate_directed_transaction(pattern_b, pattern_b, AND, 0);  // 0 & 0 = 0
        
        // OR operations
        driver.generate_directed_transaction(pattern_a, pattern_a, OR, 0);   // 1 | 1 = 1
        driver.generate_directed_transaction(pattern_a, pattern_b, OR, 0);   // 1 | 0 = 1
        driver.generate_directed_transaction(pattern_b, pattern_b, OR, 0);   // 0 | 0 = 0
        
        // XOR operations
        driver.generate_directed_transaction(pattern_a, pattern_a, XOR, 0);  // 1 ^ 1 = 0
        driver.generate_directed_transaction(pattern_a, pattern_b, XOR, 0);  // 1 ^ 0 = 1
        driver.generate_directed_transaction(pattern_b, pattern_b, XOR, 0);  // 0 ^ 0 = 0
        
        // Alternating patterns
        if (WIDTH == 32) begin
            driver.generate_directed_transaction(32'hAAAAAAAA, 32'h55555555, AND, 0);
            driver.generate_directed_transaction(32'hAAAAAAAA, 32'h55555555, OR, 0);
            driver.generate_directed_transaction(32'hAAAAAAAA, 32'h55555555, XOR, 0);
        end
        
    endtask
    
    // ========================================================================
    // Test 4: Shift Operations
    // ========================================================================
    
    task automatic test_shift_operations(ref alu_driver driver, int WIDTH);
        $display("[DIRECTED] Test 4: Shift Operations");
        
        // Shift left by various amounts
        driver.generate_directed_transaction(1, 0, SLL, 0);   // Shift by 0
        driver.generate_directed_transaction(1, 1, SLL, 0);   // Shift by 1
        driver.generate_directed_transaction(1, 4, SLL, 0);   // Shift by 4
        driver.generate_directed_transaction(1, 8, SLL, 0);   // Shift by 8
        driver.generate_directed_transaction(1, 16, SLL, 0);  // Shift by 16
        driver.generate_directed_transaction(1, 31, SLL, 0);  // Shift by 31 (max)
        
        // Shift right by various amounts
        if (WIDTH == 32) begin
            driver.generate_directed_transaction(32'h80000000, 0, SRL, 0);   // Shift by 0
            driver.generate_directed_transaction(32'h80000000, 1, SRL, 0);   // Shift by 1
            driver.generate_directed_transaction(32'h80000000, 4, SRL, 0);   // Shift by 4
            driver.generate_directed_transaction(32'h80000000, 8, SRL, 0);   // Shift by 8
            driver.generate_directed_transaction(32'h80000000, 16, SRL, 0);  // Shift by 16
            driver.generate_directed_transaction(32'h80000000, 31, SRL, 0);  // Shift by 31 (max)
        end
        
        // Shift overflow (shift amount >= WIDTH)
        driver.generate_directed_transaction(1, WIDTH, SLL, 0);
        driver.generate_directed_transaction(1, WIDTH+5, SLL, 0);
        
    endtask
    
    // ========================================================================
    // Test 5: Compare Operations
    // ========================================================================
    
    task automatic test_compare_operations(ref alu_driver driver, int WIDTH);
        $display("[DIRECTED] Test 5: Compare Operations");
        
        // Unsigned comparisons
        driver.generate_directed_transaction(5, 10, CMP, 0);   // 5 < 10 = true
        driver.generate_directed_transaction(10, 5, CMP, 0);   // 10 < 5 = false
        driver.generate_directed_transaction(10, 10, CMP, 0);  // 10 < 10 = false
        
        // Signed comparisons
        driver.generate_directed_transaction(5, 10, CMP, 1);   // 5 < 10 = true
        driver.generate_directed_transaction(10, 5, CMP, 1);   // 10 < 5 = false
        
        // Boundary comparisons
        driver.generate_directed_transaction(0, 1, CMP, 0);
        driver.generate_directed_transaction({WIDTH{1'b1}}, 0, CMP, 0);
        
    endtask
    
    // ========================================================================
    // Test 6: Signed Operations
    // ========================================================================
    
    task automatic test_signed_operations(ref alu_driver driver, int WIDTH);
        $display("[DIRECTED] Test 6: Signed Operations");
        
        bit [WIDTH-1:0] pos_value, neg_value;
        
        pos_value = (1 << (WIDTH-2));  // Large positive
        neg_value = ~pos_value + 1;    // Negative of pos_value
        
        // Signed addition
        driver.generate_directed_transaction(pos_value, 1, ADD, 1);
        driver.generate_directed_transaction(neg_value, 1, ADD, 1);
        driver.generate_directed_transaction(pos_value, neg_value, ADD, 1);
        
        // Signed subtraction
        driver.generate_directed_transaction(pos_value, 1, SUB, 1);
        driver.generate_directed_transaction(neg_value, 1, SUB, 1);
        driver.generate_directed_transaction(pos_value, neg_value, SUB, 1);
        
        // Signed compare
        driver.generate_directed_transaction(pos_value, neg_value, CMP, 1);
        driver.generate_directed_transaction(neg_value, pos_value, CMP, 1);
        
    endtask
    
    // ========================================================================
    // Test 7: Overflow Detection
    // ========================================================================
    
    task automatic test_overflow_detection(ref alu_driver driver, int WIDTH);
        $display("[DIRECTED] Test 7: Overflow Detection");
        
        bit [WIDTH-1:0] max_pos, max_neg;
        
        max_pos = {1'b0, {(WIDTH-1){1'b1}}};  // Maximum positive (0111...1)
        max_neg = {1'b1, {(WIDTH-1){1'b0}}};  // Maximum negative (1000...0)
        
        // Signed overflow: positive + positive = negative
        driver.generate_directed_transaction(max_pos, 1, ADD, 1);
        driver.generate_directed_transaction(max_pos, max_pos, ADD, 1);
        
        // Signed overflow: negative + negative = positive
        driver.generate_directed_transaction(max_neg, max_neg, ADD, 1);
        driver.generate_directed_transaction(max_neg, -1, ADD, 1);
        
        // Signed overflow: positive - negative = negative
        driver.generate_directed_transaction(max_pos, max_neg, SUB, 1);
        
        // Signed overflow: negative - positive = positive
        driver.generate_directed_transaction(max_neg, max_pos, SUB, 1);
        
        // No overflow cases
        driver.generate_directed_transaction(max_pos, -1, ADD, 1);
        driver.generate_directed_transaction(max_neg, 1, ADD, 1);
        
    endtask
    
    // ========================================================================
    // Test 8: Zero Flag
    // ========================================================================
    
    task automatic test_zero_flag(ref alu_driver driver, int WIDTH);
        $display("[DIRECTED] Test 8: Zero Flag");
        
        // Operations that produce zero
        driver.generate_directed_transaction(0, 0, ADD, 0);
        driver.generate_directed_transaction(10, 10, SUB, 0);
        driver.generate_directed_transaction(42, 42, XOR, 0);
        driver.generate_directed_transaction({WIDTH{1'b1}}, 0, AND, 0);
        
        // Operations that don't produce zero
        driver.generate_directed_transaction(1, 1, ADD, 0);
        driver.generate_directed_transaction(10, 5, SUB, 0);
        driver.generate_directed_transaction(1, 1, OR, 0);
        
    endtask

endmodule : alu_directed_test
