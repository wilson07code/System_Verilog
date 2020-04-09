module DTCast;

int rad = 1, area1;
real area2;

initial
begin
	$cast(area1,3.141592654 * rad * rad);		//$cast system task used here. Evaluation done first. Then, type of area1 checked. Then, stored in that.
	$cast(area2,3.141592654 * rad * rad);		//$cast system task used here. Evaluation done first. Then, type of area2 checked. Then, stored in that.

	$display("area1 = %g, area2 = %g",area1,area2);	//Not supported for synthesis
end

endmodule