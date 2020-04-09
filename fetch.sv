

module FDCorrect(clock, reset, enable_updatePC, enable_fetch, pc,npc,
instrmem_rd, taddr, br_taken);

	input logic enable_updatePC, br_taken, enable_fetch;
	input bit clock,reset;
	input logic [15:0] taddr;

	output logic [15:0] pc, npc;
	output logic instrmem_rd;

	always @(posedge clock)
	begin

		if(reset)
		begin
			pc <= 16'h3000;
		end
	
		else
		begin
			if(enable_updatePC)
				if(br_taken)
					pc <= taddr;
				else if(~br_taken)
					pc <= npc;
				else
					pc <= 16'hxxxx;
			else
				pc <= pc;
		end

	end

	assign npc = pc + 1'b1;
	assign instrmem_rd = (enable_fetch) ? 1'b1 : 1'bz;


endmodule
