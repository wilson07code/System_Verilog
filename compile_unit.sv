int i=10;
module mod1();
int i=25;
task print();
$display("you've got 1",$unit::i,"!");
$display("i've got1",i,"!");
$display("i've got 2",$root.mod1.i,"!");
endtask:print

initial
begin
print();
end
endmodule