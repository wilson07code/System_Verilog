module factorial
(input [2:0]a,output [13:0]z);
assign z=fact(a);
function integer fact
(input [2:0]a);
if(a==0)
fact=1;
else
fact=fact(a-1)*a;
endfunction
endmodule