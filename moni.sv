module moni;
reg a,b,c;
initial begin
$monitor($time,"a=%b,b=%b,c=%b",a,b,c);
a=0;b=0;c=0;
#5 a=1;b=0;c=1;
#5 a=0;b=1;c=1;
#5 a=1;b=1;c=1;

#5 a=0;b=1;c=1;
end
endmodule