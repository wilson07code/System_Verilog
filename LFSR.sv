module LFSR #(parameter n=4)
(input clk,rst,output logic [n-1:0]q);
always@(posedge clk)
begin
if(rst)
q<=1;
else
begin
q[n-1]<=(q[0]^q[n-3])^q[n-2];
q[n-2:0]<=q[n-1:1];
end
end
endmodule

module LFSR_tb();
parameter n=4;
logic clk,rst;
logic [n-1:0]q;

LFSR l1(.*);

initial
clk=1'b0;
always@(*)
clk<=~clk;

initial
begin
$display($time,"clk=%d rst=%d q=%d",clk,rst,q);
rst=1'b1;
#10 rst=1'b0;
end
endmodule
