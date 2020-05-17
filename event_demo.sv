module events;
event e1,e2;
initial
begin
	$display("1 before event",$time);
	->e1;
	wait(e2.triggered);
	$display("1 after event",$time);
end

initial
begin
	$display("2 before event",$time);
	->e2;
	wait(e1.triggered);
	$display("2 after event",$time);
end
endmodule