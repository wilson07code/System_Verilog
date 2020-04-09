module duv(input clk);
bit siga,sigb;
always@(posedge clk)
sigb <= !siga;
endmodule

program bench(input clk);
initial
forever
begin
@(posedge clk)
mod_tb.di.siga <= mod_tb.di.sigb;
end
endprogram


module mod_tb;
bit clk;
duv di(clk);
bench bi(clk);
initial
begin
for(int i=0;i<=16;i++)
#1 clk=~clk;
end
always@(negedge clk)
$strobe("time =%d\tsiga A=%b\tSiga b=%b\t",$time,di.siga,di.sigb);
endmodule