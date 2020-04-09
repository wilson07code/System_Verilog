module assertion_counter(clk,reset,count,t); 
input clk,reset; 
output reg [3:0]count; 
output t; 
always @(posedge clk or negedge reset) 
begin 
if(!reset) 
count <= 0; 
else 
count <= count + 1'b1; 
end 
assign t = &count; 
endmodule

//Assertion File 1 
//`include "assertion_counter.sv" 
module count_assert_file(clk,reset,count,t); 
input clk,reset,t; 
input [3:0] count; 

property p1; 
@(posedge clk) 
disable iff(!reset) 
(count < 15 |-> !t); 
endproperty 

property p2; 
@(posedge clk) 
disable iff(!reset) 
(count == 15 |-> t); 
endproperty 
assert property (p1) 
$display("PASS"); 
else 
$error("FAIL!!!"); 
assert property (p2) 
$display("PASS"); 
else 
$error("FAIL!!!"); 
endmodule


module assertion_counter_tb(); 
logic clk,reset,t; 
logic [3:0]count; 
assertion_counter c1 (clk,reset,count,t); 
bind assertion_counter: c1 count_assert_file c_a(clk,reset,count,t); 
always 
#5 clk = ~clk; 
initial 
begin 
clk = 0; 
reset = 0; 
$monitor("count=%b\tt=%b",count,t); 
#25 reset = 1; 
end 
endmodule