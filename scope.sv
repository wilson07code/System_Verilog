class B;
extern task print();
endclass

task B::print();
$display("system verilog for verification -HEP");
endtask

module main;
initial
begin
B b;
b=new();
b.print();
end
endmodule
