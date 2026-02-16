// ============================================================================
// Module: alu_tb_top
// Description: Top-level testbench for parameterized ALU
// Author: Verification Team
// Date: February 2026
// ============================================================================

module alu_tb_top
    import alu_pkg::*;
    import alu_tb_pkg::*;
;

    // ========================================================================
    // Parameters
    // ========================================================================
    
    parameter int WIDTH = 32;
    parameter int CLK_PERIOD = 10;  // 100 MHz clock
    
    // ========================================================================
    // Signals
    // ========================================================================
    
    logic clk;
    logic rst_n;
    
    // DUT interface
    logic [WIDTH-1:0]   operand_a;
    logic [WIDTH-1:0]   operand_b;
    opcode_e            opcode;
    logic               signed_op;
    logic [WIDTH-1:0]   result;
    flags_t             flags;
    
    // Control signals
    logic               driver_enable;
    logic               transaction_sent;
    logic               monitor_ready;
    logic               test_done;
    
    // ========================================================================
    // Clock generation
    // ========================================================================
    
    initial begin
        clk = 0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end
    
    // ========================================================================
    // DUT instantiation
    // ========================================================================
    
    param_alu #(
        .WIDTH(WIDTH)
    ) dut (
        .operand_a  (operand_a),
        .operand_b  (operand_b),
        .opcode     (opcode),
        .signed_op  (signed_op),
        .result     (result),
        .flags      (flags)
    );
    
    // ========================================================================
    // Driver instantiation
    // ========================================================================
    
    alu_driver #(
        .WIDTH(WIDTH)
    ) driver (
        .clk              (clk),
        .rst_n            (rst_n),
        .operand_a        (operand_a),
        .operand_b        (operand_b),
        .opcode           (opcode),
        .signed_op        (signed_op),
        .enable           (driver_enable),
        .transaction_sent (transaction_sent)
    );
    
    // ========================================================================
    // Monitor instantiation
    // ========================================================================
    
    alu_monitor #(
        .WIDTH(WIDTH)
    ) monitor (
        .clk                (clk),
        .rst_n              (rst_n),
        .result             (result),
        .flags              (flags),
        .operand_a          (operand_a),
        .operand_b          (operand_b),
        .opcode             (opcode),
        .signed_op          (signed_op),
        .transaction_valid  (transaction_sent),
        .ready              (monitor_ready)
    );
    
    // ========================================================================
    // Scoreboard instantiation
    // ========================================================================
    
    alu_scoreboard #(
        .WIDTH(WIDTH)
    ) scoreboard (
        .clk    (clk),
        .rst_n  (rst_n)
    );
    
    // ========================================================================
    // Coverage instantiation
    // ========================================================================
    
    alu_coverage #(
        .WIDTH(WIDTH)
    ) coverage (
        .clk           (clk),
        .rst_n         (rst_n),
        .sample_enable (transaction_sent),
        .operand_a     (operand_a),
        .operand_b     (operand_b),
        .opcode        (opcode),
        .signed_op     (signed_op),
        .result        (result),
        .flags         (flags)
    );
    
    // ========================================================================
    // Assertions instantiation
    // ========================================================================
    
    alu_assertions #(
        .WIDTH(WIDTH)
    ) assertions (
        .clk        (clk),
        .rst_n      (rst_n),
        .operand_a  (operand_a),
        .operand_b  (operand_b),
        .opcode     (opcode),
        .signed_op  (signed_op),
        .result     (result),
        .flags      (flags)
    );
    
    // ========================================================================
    // Scoreboard connection process
    // ========================================================================
    
    always @(posedge clk) begin
        if (rst_n && transaction_sent) begin
            alu_transaction #(WIDTH) trans;
            
            // Wait for monitor to capture
            @(posedge clk);
            
            // Get transaction from monitor
            trans = monitor.get_transaction();
            
            if (trans != null) begin
                scoreboard.check_transaction(trans);
            end
        end
    end
    
    // ========================================================================
    // Test control
    // ========================================================================
    
    initial begin
        // Initialize
        rst_n = 0;
        driver_enable = 0;
        test_done = 0;
        
        // Display test configuration
        $display("========================================");
        $display("ALU Testbench Started");
        $display("========================================");
        $display("Configuration:");
        $display("  WIDTH: %0d bits", WIDTH);
        $display("  CLOCK: %0d ns (%0d MHz)", CLK_PERIOD, 1000/CLK_PERIOD);
        $display("========================================");
        $display("");
        
        // Reset sequence
        repeat(5) @(posedge clk);
        rst_n = 1;
        $display("[TB] Reset released at time %0t", $time);
        
        // Wait for initialization
        repeat(2) @(posedge clk);
        
        // Run test based on plusarg
        run_test();
        
        // Wait for completion
        wait(test_done);
        
        // Final reporting
        repeat(10) @(posedge clk);
        
        $display("");
        $display("========================================");
        $display("Test Completed at time %0t", $time);
        $display("========================================");
        
        driver.report_statistics();
        monitor.report_statistics();
        scoreboard.report_results();
        coverage.report_coverage();
        
        if (scoreboard.all_passed()) begin
            $display("");
            $display("***************");
            $display("*** SUCCESS ***");
            $display("***************");
            $display("");
        end else begin
            $display("");
            $display("**************");
            $display("*** FAILED ***");
            $display("**************");
            $display("");
        end
        
        $finish;
    end
    
    // ========================================================================
    // Test execution task
    // ========================================================================
    
    task automatic run_test();
        string test_name;
        int num_random_tests;
        int seed;
        
        // Get test type from plusarg
        if (!$value$plusargs("TEST=%s", test_name)) begin
            test_name = "random";
        end
        
        // Get number of tests
        if (!$value$plusargs("NTESTS=%d", num_random_tests)) begin
            num_random_tests = 1000;
        end
        
        // Get random seed
        if (!$value$plusargs("SEED=%d", seed)) begin
            seed = $urandom();
        end
        $display("[TB] Using random seed: %0d", seed);
        
        $display("[TB] Running test: %s", test_name);
        $display("");
        
        case (test_name)
            "directed": run_directed_test();
            "random": run_random_test(num_random_tests, seed);
            "corner": run_corner_test();
            "all": begin
                run_directed_test();
                run_corner_test();
                run_random_test(num_random_tests, seed);
            end
            default: begin
                $display("ERROR: Unknown test '%s'", test_name);
                $display("Valid tests: directed, random, corner, all");
            end
        endcase
        
        test_done = 1;
    endtask
    
    // ========================================================================
    // Directed test
    // ========================================================================
    
    task automatic run_directed_test();
        $display("[TB] Running directed tests...");
        
        driver_enable = 1;
        
        // Generate directed test patterns
        // Basic arithmetic
        driver.generate_directed_transaction(32'h00000005, 32'h00000003, ADD, 0);
        driver.generate_directed_transaction(32'h00000010, 32'h00000008, SUB, 0);
        
        // Logical operations
        driver.generate_directed_transaction(32'hAAAAAAAA, 32'h55555555, AND, 0);
        driver.generate_directed_transaction(32'hAAAAAAAA, 32'h55555555, OR, 0);
        driver.generate_directed_transaction(32'hAAAAAAAA, 32'h55555555, XOR, 0);
        
        // Shifts
        driver.generate_directed_transaction(32'h00000001, 32'h00000004, SLL, 0);
        driver.generate_directed_transaction(32'h80000000, 32'h00000004, SRL, 0);
        
        // Compare
        driver.generate_directed_transaction(32'h00000005, 32'h00000010, CMP, 0);
        driver.generate_directed_transaction(32'h00000010, 32'h00000005, CMP, 0);
        
        // Wait for all transactions to complete
        wait(driver.trans_queue.size() == 0);
        repeat(20) @(posedge clk);
        
        $display("[TB] Directed tests completed");
    endtask
    
    // ========================================================================
    // Random test
    // ========================================================================
    
    task automatic run_random_test(int num_tests, int seed);
        $display("[TB] Running %0d random tests with seed %0d...", num_tests, seed);
        
        // Set seed
        void'($urandom(seed));
        
        driver_enable = 1;
        
        // Generate random transactions
        for (int i = 0; i < num_tests; i++) begin
            driver.generate_random_transaction();
        end
        
        // Wait for all transactions to complete
        wait(driver.trans_queue.size() == 0);
        repeat(20) @(posedge clk);
        
        $display("[TB] Random tests completed");
    endtask
    
    // ========================================================================
    // Corner case test
    // ========================================================================
    
    task automatic run_corner_test();
        $display("[TB] Running corner case tests...");
        
        driver_enable = 1;
        driver.generate_corner_cases();
        
        // Wait for all transactions to complete
        wait(driver.trans_queue.size() == 0);
        repeat(20) @(posedge clk);
        
        $display("[TB] Corner case tests completed");
    endtask
    
    // ========================================================================
    // Timeout watchdog
    // ========================================================================
    
    initial begin
        #(CLK_PERIOD * TIMEOUT_CYCLES * 1000);
        $error("TIMEOUT: Simulation exceeded maximum time");
        $finish;
    end

endmodule : alu_tb_top
