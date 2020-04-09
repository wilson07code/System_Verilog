module d2_5
(input a,b,c,d,output logic y);
logic l1,l2;

assign l1=a|b;
assign l2=c&d;
assign y=l1&l2;

assign b=1'b0;
assign c=1'b1;
assign d=1'b1;
endmodule