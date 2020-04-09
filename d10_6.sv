class test;
int a[];
rand bit [4:0]b;
endclass

module d10_6;

initial
begin
int i=0;
test t1=new();
t1.a=new[5];

repeat(10)
begin
if(t1.randomize(b)with{b>7;})
begin
t1.a[i]=t1.b;
i++;
$display("a=%p",t1.a);
end
else
$display("failed");
end
end
endmodule