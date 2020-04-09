module STCast;

shortint i,j = 1;
int k = 1;

initial
begin
	repeat(5)
	begin
		i = int'(j * k);		//This is static typecasting. Before evaluation, output size is fixed. Only after allocation of memory, evaluation is done. If output needs more memory, it is truncated so as to fit into the allocated output size.
		$display("i = %d, j = %d, k = %d",i,j,k);
		j++;				//Static typecasting format : <datatype>'(<expression>);
		k++;
	end					//Synthesisable
end

endmodule