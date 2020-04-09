timeunit 1ns;
timeprecision 1ps;
module timing;
//`timescale 1ns/1ps

initial
begin
$timeformat(-9,3,"ns",8);
#1 $display("%t",$realtime);
#2ns $display("%t",$realtime);
#0.1ns $display("%t",$realtime);
#41ps $display("%t",$realtime);
end
endmodule