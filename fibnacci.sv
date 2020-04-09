module fibnacci
(input [3:0]a,output [15:0]y);
initial
begin
for(int i=0;i<=15;i++)
$display("%d",fib(i));
end
assign y=fib(a);
function automatic integer fib
(input [3:0]a);
if(a==0)
fib=0;
else if(a==1)
fib=1;
else
fib=fib(a-1)+fib(a-2);
endfunction
endmodule