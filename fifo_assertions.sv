`include"synch_fifo_case.v"

module fifo_assertions 
(	     
        input clk,rst,re,we,
	input[7:0]din,
        input reg[7:0]dout,
        input  f,e
);

sequence reset_seq;
((!e) && (!f));
endsequence

property reset_prty;
@(posedge clk) (rst) |-> e ##0 !f; 
endproperty

sequence overflow_seq;
((!e) && (!re && we)) ;
endsequence

property overflow_prty;
@(posedge clk) overflow_seq[*8]  |=> f;
endproperty

sequence underflow_seq;
(!f && !we && re);
endsequence

property underflow_prty;
@(posedge clk) underflow_seq[*8]  |=> e;
endproperty

 
RESET:assert property (reset_prty) $display(" reset pass!!"); else $error("reset fail!!");
FIFO_UNDERFLOW:assert property (underflow_prty) $display("empty pass!!"); else $error("empty fail!!");
FIFO_OVERFLOW:assert property (overflow_prty) $display("full pass!!"); else $error("full fail!!");


endmodule


