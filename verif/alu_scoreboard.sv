// ============================================================================
// Module: alu_scoreboard
// Description: Scoreboard component for ALU testbench
//              Compares DUT output with golden reference model
// Author: Verification Team
// Date: February 2026
// ============================================================================

module alu_scoreboard 
    import alu_pkg::*;
    import alu_tb_pkg::*;
#(
    parameter int WIDTH = 32
) (
    input  logic clk,
    input  logic rst_n
);

    // ========================================================================
    // Internal variables
    // ========================================================================
    
    int transactions_checked;
    int transactions_passed;
    int transactions_failed;
    
    alu_transaction #(WIDTH) error_queue[$];
    
    // ========================================================================
    // Initialization
    // ========================================================================
    
    initial begin
        transactions_checked = 0;
        transactions_passed = 0;
        transactions_failed = 0;
    end
    
    // ========================================================================
    // Check transaction against golden model
    // ========================================================================
    
    task automatic check_transaction(alu_transaction #(WIDTH) trans);
        bit [WIDTH-1:0] golden_result;
        flags_t golden_flags;
        bit match;
        
        // Compute golden model
        compute_golden_model(
            WIDTH,
            trans.operand_a,
            trans.operand_b,
            trans.opcode,
            trans.signed_op,
            golden_result,
            golden_flags
        );
        
        // Store expected values
        trans.expected_result = golden_result;
        trans.expected_flags = golden_flags;
        
        // Compare
        match = 1;
        transactions_checked++;
        
        if (trans.actual_result !== golden_result) begin
            $error("[SCOREBOARD] @%0t: Result mismatch for transaction %0d", 
                   $time, trans.transaction_id);
            $error("  Operation: %s, Signed: %b", opcode_to_string(trans.opcode), trans.signed_op);
            $error("  Operand A: 0x%0h", trans.operand_a);
            $error("  Operand B: 0x%0h", trans.operand_b);
            $error("  Expected Result: 0x%0h", golden_result);
            $error("  Actual Result: 0x%0h", trans.actual_result);
            match = 0;
        end
        
        if (trans.actual_flags !== golden_flags) begin
            $error("[SCOREBOARD] @%0t: Flag mismatch for transaction %0d", 
                   $time, trans.transaction_id);
            $error("  Expected Flags: Z=%b C=%b V=%b N=%b", 
                   golden_flags.zero, golden_flags.carry, golden_flags.overflow, golden_flags.negative);
            $error("  Actual Flags: Z=%b C=%b V=%b N=%b", 
                   trans.actual_flags.zero, trans.actual_flags.carry, trans.actual_flags.overflow, trans.actual_flags.negative);
            match = 0;
        end
        
        if (match) begin
            transactions_passed++;
        end else begin
            transactions_failed++;
            error_queue.push_back(trans.copy());
        end
        
        // Periodic progress reporting
        if (transactions_checked % 100 == 0) begin
            $display("[SCOREBOARD] @%0t: Checked %0d transactions (%0d passed, %0d failed)", 
                     $time, transactions_checked, transactions_passed, transactions_failed);
        end
        
    endtask
    
    // ========================================================================
    // Final report
    // ========================================================================
    
    task automatic report_results();
        real pass_rate;
        
        $display("");
        $display("========================================");
        $display("Scoreboard Final Report");
        $display("========================================");
        $display("Total transactions checked: %0d", transactions_checked);
        $display("Transactions passed: %0d", transactions_passed);
        $display("Transactions failed: %0d", transactions_failed);
        
        if (transactions_checked > 0) begin
            pass_rate = (real'(transactions_passed) / real'(transactions_checked)) * 100.0;
            $display("Pass rate: %0.2f%%", pass_rate);
        end
        
        $display("========================================");
        
        if (transactions_failed > 0) begin
            $display("");
            $display("ERROR: %0d transactions failed!", transactions_failed);
            $display("First few failures:");
            for (int i = 0; i < 5 && i < error_queue.size(); i++) begin
                error_queue[i].display("  ");
            end
        end else begin
            $display("");
            $display("SUCCESS: All transactions passed!");
        end
        
        $display("========================================");
        $display("");
    endtask
    
    // ========================================================================
    // Get statistics
    // ========================================================================
    
    function automatic bit all_passed();
        return (transactions_failed == 0) && (transactions_checked > 0);
    endfunction
    
    function automatic int get_total_checked();
        return transactions_checked;
    endfunction
    
    function automatic int get_total_passed();
        return transactions_passed;
    endfunction
    
    function automatic int get_total_failed();
        return transactions_failed;
    endfunction

endmodule : alu_scoreboard
