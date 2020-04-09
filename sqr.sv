module square();
logic [2:0]a;
logic [8:0]b;

initial
begin

a=3'b101;
#10 a=3'b011;
repeat(10)
b=a*a;

$display("%d",b);
end
endmodule