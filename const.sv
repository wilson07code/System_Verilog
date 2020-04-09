
//class imp;
// rand bit x;
// rand bit [1:0] y;
// constraint c_xy {
// (x==0)->(y==0);
// }
// endclass

class C;
 rand byte A[4];
 constraint C1{ foreach (A[i]) A[i]inside {2,4,8,16};}
 constraint C2{foreach (A[j]) A[j]> 2*j;} 
 endclass



module cons;
C c=new();
initial 
begin


repeat(10)
begin

if(c.randomize())
$display("A=%p",c.A);
else
$display("failed");
end
end
endmodule