class test;
rand int a,b;
endclass

module d10_5();

initial
begin
test t1=new();
repeat(10)
begin
if(t1.randomize(a,b)with{a==0;b==4|b==5;})

$display("a=%d,b=%d",t1.a,t1.b);
else
$display("field");
end
end
endmodule