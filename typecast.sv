module typecast;
int i =70;
initial
begin
i=shortint'(i);
$display("%d",i);
end
endmodule