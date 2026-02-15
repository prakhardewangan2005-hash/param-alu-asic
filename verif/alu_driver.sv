// ============================================================================
// Module: alu_driver
// Description: Driver component for ALU testbench
//              Generates stimulus and drives DUT inputs
// Author: Verification Team
// Date: February 2026
// ============================================================================

module alu_driver 
    import alu_pkg::*;
    import alu_tb_pkg::*;
#(
    parameter int WIDTH = 32
) (
    input  logic clk,
    input  logic rst_n,
    
    // Interface to DUT
    output logic [WIDTH-1:0]   operand_a,
    output logic [WIDTH-1:0]   operand_b,
    output opcode_e            opcode,
    output logic               signed_op,
    
    // Control signals
    input  logic               enable,
    output logic               transaction_sent
);

    // ========================================================================
    // Internal variables
    // ========================================================================
    
    alu_transaction #(WIDTH) trans_queue[$];
    int transactions_sent;
    int transaction_count;
    
    // ========================================================================
    // Initialization
    // ========================================================================
    
    initial begin
        operand_a = '0;
        operand_b = '0;
        opcode = ADD;
        signed_op = 0;
        transaction_sent = 0;
        transactions_sent = 0;
        transaction_count = 0;
    end
    
    // ========================================================================
    // Transaction generation task
    // ========================================================================
    
    task automatic generate_random_transaction();
        alu_transaction #(WIDTH) trans;
        trans = new();
        
        if (!trans.randomize()) begin
            $error("Transaction randomization failed");
        end
        
        trans.transaction_id = transaction_count++;
        trans.timestamp = $time;
        trans_queue.push_back(trans);
        
    endtask
    
    // ========================================================================
    // Directed transaction generation
    // ========================================================================
    
    task automatic generate_directed_transaction(
        input bit [WIDTH-1:0] a,
        input bit [WIDTH-1:0] b,
        input opcode_e op,
        input bit signed_mode
    );
        alu_transaction #(WIDTH) trans;
        trans = new();
        
        trans.operand_a = a;
        trans.operand_b = b;
        trans.opcode = op;
        trans.signed_op = signed_mode;
        trans.transaction_id = transaction_count++;
        trans.timestamp = $time;
        
        trans_queue.push_back(trans);
    endtask
    
    // ========================================================================
    // Corner case generation
    // ========================================================================
    
    task automatic generate_corner_cases();
        // Zero operands
        generate_directed_transaction('0, '0, ADD, 0);
        generate_directed_transaction('0, '0, SUB, 0);
        
        // Max values
        generate_directed_transaction('1, '1, ADD, 0);
        generate_directed_transaction('1, '1, SUB, 0);
        
        // Overflow scenarios (signed)
        generate_directed_transaction({1'b0, {(WIDTH-1){1'b1}}}, 1, ADD, 1); // Max positive + 1
        generate_directed_transaction({1'b1, {(WIDTH-1){1'b0}}}, 1, SUB, 1); // Min negative - 1
        
        // XOR with self
        generate_directed_transaction(32'hAAAAAAAA, 32'hAAAAAAAA, XOR, 0);
        
        // Shifts
        generate_directed_transaction(32'h1, 0, SLL, 0);      // Shift by 0
        generate_directed_transaction(32'h1, 31, SLL, 0);     // Max shift
        generate_directed_transaction(32'h1, WIDTH, SLL, 0);  // Overflow shift
        
        $display("[DRIVER] Generated %0d corner case transactions", trans_queue.size());
    endtask
    
    // ========================================================================
    // Main driver process
    // ========================================================================
    
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            operand_a <= '0;
            operand_b <= '0;
            opcode <= ADD;
            signed_op <= 0;
            transaction_sent <= 0;
        end else if (enable && trans_queue.size() > 0) begin
            alu_transaction #(WIDTH) trans;
            trans = trans_queue.pop_front();
            
            // Drive transaction to DUT
            operand_a <= trans.operand_a;
            operand_b <= trans.operand_b;
            opcode <= trans.opcode;
            signed_op <= trans.signed_op;
            transaction_sent <= 1;
            transactions_sent++;
            
            // Display transaction info
            if (transactions_sent % 100 == 0) begin
                $display("[DRIVER] @%0t: Sent %0d transactions", $time, transactions_sent);
            end
        end else begin
            transaction_sent <= 0;
        end
    end
    
    // ========================================================================
    // Statistics reporting
    // ========================================================================
    
    task automatic report_statistics();
        $display("========================================");
        $display("Driver Statistics");
        $display("========================================");
        $display("Total transactions generated: %0d", transaction_count);
        $display("Total transactions sent: %0d", transactions_sent);
        $display("Transactions in queue: %0d", trans_queue.size());
        $display("========================================");
    endtask

endmodule : alu_driver
