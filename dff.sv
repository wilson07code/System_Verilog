module dff(input logic clk,d,rst,output logic q,q1);
always@(posedge clk,negedge rst)
begin
q<=d;
q1<=!d;
end
endmodule