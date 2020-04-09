module assertion_ram(input logic clk,rst,read,write, 
 logic [7:0] addr, logic [15:0]data, 
 output logic [15:0]out); 
logic [15:0]mem[255:0]; 
always@(posedge clk, posedge rst) 
begin 
if(rst) 
out <= 16'b0; 
else 
begin 
if(read) 
out <= mem[addr]; 
if(write) 
mem[addr] <= data; 
end 
stable_when_write : assert property (disable iff (rst) write |-> 
$stable(out)); 
end 
endmodule