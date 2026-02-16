// ============================================================================
// Module: alu_random_test
// Description: Constrained random test scenarios for ALU verification
// Author: Verification Team
// Date: February 2026
// ============================================================================

module alu_random_test
    import alu_pkg::*;
    import alu_tb_pkg::*;
;

    // ========================================================================
    // Random test with configurable parameters
    // ========================================================================
    
    task automatic run_random_tests(
        ref alu_driver driver,
        int WIDTH,
        int num_tests,
        int seed
    );
        
        $display("========================================");
        $display("Running Random Test Suite");
        $display("  Number of tests: %0d", num_tests);
        $display("  Random seed: %0d", seed);
        $display("  WIDTH: %0d", WIDTH);
        $display("========================================");
        
        // Set random seed
        void'($urandom(seed));
        
        // Generate random transactions
        for (int i = 0; i < num_tests; i++) begin
            driver.generate_random_transaction();
            
            // Progress indicator every 100 tests
            if ((i+1) % 100 == 0) begin
                $display("[RANDOM] Generated %0d/%0d transactions", i+1, num_tests);
            end
        end
        
        $display("========================================");
        $display("Random Test Generation Complete");
        $display("========================================");
        
    endtask
    
    // ========================================================================
    // Weighted random test (bias toward certain operations)
    // ========================================================================
    
    task automatic run_weighted_random_tests(
        ref alu_driver driver,
        int WIDTH,
        int num_tests,
        int seed,
        real arithmetic_weight = 0.5,
        real logical_weight = 0.3,
        real shift_weight = 0.15,
        real compare_weight = 0.05
    );
        
        alu_transaction #(WIDTH) trans;
        int op_select;
        real rand_val;
        
        $display("========================================");
        $display("Running Weighted Random Test Suite");
        $display("  Arithmetic weight: %0.2f", arithmetic_weight);
        $display("  Logical weight: %0.2f", logical_weight);
        $display("  Shift weight: %0.2f", shift_weight);
        $display("  Compare weight: %0.2f", compare_weight);
        $display("========================================");
        
        void'($urandom(seed));
        
        for (int i = 0; i < num_tests; i++) begin
            trans = new();
            
            // Randomize operands
            assert(trans.randomize() with {
                operand_a dist {
                    0 := 1,
                    [1:100] := 20,
                    [101:(2**(WIDTH-1))] := 60,
                    [(2**(WIDTH-1))+1:(2**WIDTH)-1] := 19
                };
            });
            
            // Select operation based on weights
            rand_val = $urandom_range(0, 1000) / 1000.0;
            
            if (rand_val < arithmetic_weight) begin
                // Arithmetic operations
                trans.opcode = (rand_val < arithmetic_weight/2) ? ADD : SUB;
            end else if (rand_val < arithmetic_weight + logical_weight) begin
                // Logical operations
                op_select = $urandom_range(0, 2);
                case (op_select)
                    0: trans.opcode = AND;
                    1: trans.opcode = OR;
                    2: trans.opcode = XOR;
                endcase
            end else if (rand_val < arithmetic_weight + logical_weight + shift_weight) begin
                // Shift operations
                trans.opcode = ($urandom_range(0, 1) == 0) ? SLL : SRL;
                // Bias shift amounts to reasonable values
                trans.operand_b = $urandom_range(0, WIDTH-1);
            end else begin
                // Compare operation
                trans.opcode = CMP;
            end
            
            // Randomize signed_op
            trans.signed_op = $urandom_range(0, 1);
            
            // Add to driver queue
            driver.trans_queue.push_back(trans);
        end
        
        $display("========================================");
        $display("Weighted Random Test Generation Complete");
        $display("========================================");
        
    endtask
    
    // ========================================================================
    // Stress test - back-to-back operations
    // ========================================================================
    
    task automatic run_stress_test(
        ref alu_driver driver,
        int WIDTH,
        int num_tests,
        int seed
    );
        
        $display("========================================");
        $display("Running Stress Test");
        $display("  (Back-to-back operations)");
        $display("========================================");
        
        void'($urandom(seed));
        
        for (int i = 0; i < num_tests; i++) begin
            driver.generate_random_transaction();
        end
        
        $display("========================================");
        $display("Stress Test Generation Complete");
        $display("========================================");
        
    endtask
    
    // ========================================================================
    // Corner case focused random test
    // ========================================================================
    
    task automatic run_corner_focused_random(
        ref alu_driver driver,
        int WIDTH,
        int num_tests,
        int seed
    );
        
        alu_transaction #(WIDTH) trans;
        
        $display("========================================");
        $display("Running Corner-Focused Random Test");
        $display("========================================");
        
        void'($urandom(seed));
        
        for (int i = 0; i < num_tests; i++) begin
            trans = new();
            
            // Bias toward corner values
            assert(trans.randomize() with {
                operand_a dist {
                    0 := 15,
                    1 := 10,
                    {WIDTH{1'b1}} := 15,
                    {1'b0, {(WIDTH-1){1'b1}}} := 10,  // Max positive
                    {1'b1, {(WIDTH-1){1'b0}}} := 10,  // Max negative
                    [2:(2**WIDTH)-2] := 40
                };
                
                operand_b dist {
                    0 := 15,
                    1 := 10,
                    {WIDTH{1'b1}} := 15,
                    {1'b0, {(WIDTH-1){1'b1}}} := 10,
                    {1'b1, {(WIDTH-1){1'b0}}} := 10,
                    [2:(2**WIDTH)-2] := 40
                };
            });
            
            driver.trans_queue.push_back(trans);
        end
        
        $display("========================================");
        $display("Corner-Focused Random Test Generation Complete");
        $display("========================================");
        
    endtask

endmodule : alu_random_test
