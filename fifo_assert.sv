module syn_fifo(input clk,rst,we,re,input [7:0]di,output  [7:0]dout,output e,f);
reg [3:0]wt_ptr,rd_ptr;
fifo_ram f1(.clk(clk),.en(rst),.we_a(we),.rd_b(re),.addr_a(wt_ptr),.addr_b(rd_ptr),.di(di),.dout(dout));
always@(posedge clk)
begin
assert(rst)
begin
wt_ptr<=4'b0;
rd_ptr<=4'b0;
end
else if(we&!f)
wt_ptr<=wt_ptr+1'b1;
else if(re&!e)
rd_ptr<=rd_ptr+1'b1;
end
assign e=(wt_ptr==rd_ptr)?1'b1:1'b0;
assign f=({~wt_ptr[3],wt_ptr[2:0]}==rd_ptr)?1'b1:1'b0;
endmodule

//--------------------------------------------------------------------------

module fifo_ram(input clk,en,we_a,rd_b,input [2:0]addr_a,addr_b,input [7:0]di,
output reg [7:0]dout);
reg[7:0]mem[0:7];
always@(posedge clk)
begin
if(en)
begin
if(we_a)
mem[addr_a]<=di;
if(rd_b)
dout<=mem[addr_b];
end
end

endmodule  



//assertion//////

module fifo_assertion(clk,rst_n,rd_n,wr_n,over_flow,under_flow);
input logic rst_n,clk,rd_n,wr_n;
output logic under_flow,over_flow;

//reset

sequence reset_seq;
((!under_flow)&&(!over_flow));
endsequence

property reset_prty;
@(posedge clk)(!rst_n)|->!under_flow##0!over_flow;
endproperty

sequence overflow_seq;
((!under_flow)&&(!rd_n&&wr_n));
endsequence

property overflow_prty;
@(posedge clk)overflow_seq[*16]|=>over_flow;
endproperty

sequence underflow_seq;
(!over_flow&&!wr_n&&rd_n);
endsequence

property underflow_prty;
@(posedge clk)underflow_seq[*16]|=>under_flow;
endproperty

RESET:assert property(reset_prty);
FIFO_UNDERFLOW:assert property(underflow_prty);
FIFO_OVERFLOW:assert property(overflow_prty);
endmodule

////////////testbench////////////

module TBfifo();
logic clk,rst,we,re;
logic [7:0]di;
logic [7:0]dout;
logic e,f;

syn_fifo f1(.clk(clk),.rst(rst),.we(we),.re(re),.di(di),.dout(dout),.e(e),.f(f));
bind syn_fifo: f1 fifo_assertion s_a(clk,rst,re,we,e,f); 
always 
#5 clk = ~clk; 

initial 
begin 
clk = 0; 
rst = 0; we=0;re=0;di=2'd3;
$monitor("rst=%d\twe=%d\tre=%d\tdi=%d\tdout=%d\te=%d\tf=%d",rst,we,re,di,dout,e,f);
#25 rst=1;we=1;
end
endmodule