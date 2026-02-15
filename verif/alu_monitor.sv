// ============================================================================
// Module: alu_monitor
// Description: Monitor component for ALU testbench
//              Captures DUT outputs and creates transactions
// Author: Verification Team
// Date: February 2026
// ============================================================================

module alu_monitor 
    import alu_pkg::*;
    import alu_tb_pkg::*;
#(
    parameter int WIDTH = 32
) (
    input  logic clk,
    input  logic rst_n,
    
    // Interface to DUT outputs
    input  logic [WIDTH-1:0]   result,
    input  flags_t             flags,
    
    // Interface to DUT inputs (for transaction capture)
    input  logic [WIDTH-1:0]   operand_a,
    input  logic [WIDTH-1:0]   operand_b,
    input  opcode_e            opcode,
    input  logic               signed_op,
    
    // Control signals
    input  logic               transaction_valid,
    output logic               ready
);

    // ========================================================================
    // Internal variables
    // ========================================================================
    
    alu_transaction #(WIDTH) observed_trans_queue[$];
    int transactions_observed;
    
    // ========================================================================
    // Initialization
    // ========================================================================
    
    initial begin
        ready = 1;
        transactions_observed = 0;
    end
    
    // ========================================================================
    // Monitor process
    // ========================================================================
    
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            transactions_observed <= 0;
        end else if (transaction_valid) begin
            alu_transaction #(WIDTH) trans;
            trans = new();
            
            // Capture inputs
            trans.operand_a = operand_a;
            trans.operand_b = operand_b;
            trans.opcode = opcode;
            trans.signed_op = signed_op;
            
            // Capture outputs
            trans.actual_result = result;
            trans.actual_flags = flags;
            
            // Metadata
            trans.transaction_id = transactions_observed++;
            trans.timestamp = $time;
            
            // Add to queue for scoreboard
            observed_trans_queue.push_back(trans);
            
            // Periodic reporting
            if (transactions_observed % 100 == 0) begin
                $display("[MONITOR] @%0t: Observed %0d transactions", $time, transactions_observed);
            end
        end
    end
    
    // ========================================================================
    // Get transaction for scoreboard
    // ========================================================================
    
    function automatic alu_transaction #(WIDTH) get_transaction();
        if (observed_trans_queue.size() > 0) begin
            return observed_trans_queue.pop_front();
        end else begin
            return null;
        end
    endfunction
    
    // ========================================================================
    // Queue status
    // ========================================================================
    
    function automatic int get_queue_size();
        return observed_trans_queue.size();
    endfunction
    
    // ========================================================================
    // Statistics reporting
    // ========================================================================
    
    task automatic report_statistics();
        $display("========================================");
        $display("Monitor Statistics");
        $display("========================================");
        $display("Total transactions observed: %0d", transactions_observed);
        $display("Transactions in queue: %0d", observed_trans_queue.size());
        $display("========================================");
    endtask

endmodule : alu_monitor
