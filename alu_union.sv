package my_package;

bit arith_logic_sel;
logic [1:0] arithlogic_op;
logic [15:0] data_out;

struct packed //arith_logic_info
{
	bit [7:0] ip_data1;
        bit [7:0] ip_data2;
} arith_data,logic_data;

struct //arith_logic_result 
{
	union packed 
	{
		logic [15:0] result_data;
	} result;
} final_result;

endpackage





module alu_struct_union_test; 

import my_package::*;
initial
begin
	 arith_data.ip_data1 = 8'd10;
 	 arith_data.ip_data2 = 8'd10;
	 logic_data.ip_data1 = 8'd05;
	 logic_data.ip_data2 = 8'd05;
	 arith_logic_sel = 1'b1;
	 arithlogic_op = 2'd0;
	 
	if(arith_logic_sel == 1'b1)
		begin
			case(arithlogic_op)
	        		2'd0: data_out = arith_data.ip_data1 + arith_data.ip_data2;
				2'd1: data_out = arith_data.ip_data1 - arith_data.ip_data2;
				2'd2: data_out = arith_data.ip_data1 * arith_data.ip_data2;
				2'd3: data_out = arith_data.ip_data1 / arith_data.ip_data2;
		     	     default: data_out = 16'd0; 	
			endcase
			final_result.result.result_data = data_out;
		end
	else
		begin
			case(arithlogic_op)
	        		2'd0: data_out = ~(logic_data.ip_data1 & logic_data.ip_data2);
				2'd1: data_out = ~(logic_data.ip_data1 | logic_data.ip_data2);
				2'd2: data_out = ~ logic_data.ip_data1;
				2'd3: data_out =   logic_data.ip_data1 ^ logic_data.ip_data2;
                     	     default: data_out = 16'd0; 
			endcase
			final_result.result.result_data = data_out;
		end
	$display ("%d",final_result.result.result_data);
	
end

endmodule
