module DT_cast(input clk);
int rad,area;
initial
rad=32;
always@(posedge clk)
begin
$cast(output variable,expression);
$cast(area,3.14*rad*rad);
$display(area);
end
endmodule