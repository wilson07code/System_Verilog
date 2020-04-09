module WCEqual;

logic [3:0] a = 4'b1111, b = 4'bxx1x, c = 4'bxx0x, d = 4'bx10x;

initial
begin
	$display("(a ==? b) ",(a ==? b));
	$display("(a !=? b) ", (a !=? b));

	$display("(a ==? c) ",(a ==? c));
	$display("(a !=? c) ",(a !=? c));

	$display("(a ==? d) ",(a ==? d));
	$display("(a !=? d) ",(a !=? d));

	$display("(c ==? b) ",(c ==? b));
	$display("(c !=? b) ",(c !=? b));

	$display("(d ==? b) ",(d ==? b));
	$display("(d !=? b) ",(d !=? b));

	$display("(c ==? d) ",(c ==? d));
	$display("(c !=? d) ",(c !=? d));

	$display("(d ==? c) ",(d ==? c));
	$display("(d !=? c) ",(d !=? c));
end

endmodule