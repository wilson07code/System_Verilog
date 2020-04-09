module test_inac;

reg a,b,c,d;

initial
begin
$monitor($time,"a=%d b=%d c=%d d=%d",a,b,c,d);
a=1'b0;
#0a=1'b1;
#0c=b;
end

initial
begin
b=1'b1;
#0d=a;
$display("d=%d",d);
end

endmodule
