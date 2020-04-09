//Design
module duv(input clk);
bit siga,sigb;
always@(posedge clk)
sigb <= !siga;
endmodule


//Testbench
module duv_tb;
bit clk;
duv di(clk);
initial
begin
for(int i=0;i<=16;i++)
#1 clk=~clk;
end
always@(posedge clk)
di.siga <= di.sigb;
always@(negedge clk)
$display("time=%2d\tsiga=%0b\tsigb=%0b",$time,di.siga,di.sigb);
endmodule