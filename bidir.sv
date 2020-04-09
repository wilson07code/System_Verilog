program bidrectional_const; 
class bidr; 
rand bit[5:0]b,c,d; 
constraint c1{40>d;d>b;b==c;c>=25;} 
endclass 
initial 
begin 
repeat(10) 
begin 
bidr b; 
b=new; 
if(b.randomize()) 
$display("b=%0d\tc=%0d\td=%0d",b.b,b.c,b.d); 
end 
end 
endprogram