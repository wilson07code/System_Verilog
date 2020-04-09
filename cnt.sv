module count
(input clk,rst,output logic[4:0]cnt);
always@(posedge clk)
begin
if(rst)
cnt<=5'd0;
else
cnt<=cnt+1;
end
endmodule