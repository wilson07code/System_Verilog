//stage 1 - the execute preprocessor
`define CLK_PERIOD 10
`define REGISTER_WIDTH 32
`define INSTR_WIDTH 32
`define IMMEDIATE_WIDTH 16
`define MEM_READ 3'b101
`define MEM_WRITE 3'b100
`define ARITH_LOGIC 3'b001
`define SHIFT_REG 3'b000

module preprocessor
(input clk,reset,enable_ex,
input [31:0]src1,src2,imm,mem_data_read_in,
input [6:0]control_in,
output logic enable_arith,enable_shift,mem_data_write_en,
output logic [2:0] operation_out,opselect_out,
output logic [31:0] mem_data_write_out,aluin1,aluin2,
output logic [4:0] shift_number);

assign mem_data_write_en=(control_in[2:0] == `MEM_WRITE && control_in[3] == 1'b1)?1:0;
assign mem_data_write_out=src2;

always@(posedge clk)
begin
aluin2<=aluin2;
if(!reset)
begin
	aluin1<=0;
	aluin2<=0;
	operation_out<=0;
	opselect_out<=0;
	shift_number<=0;
	enable_arith<=0;
	enable_shift<=0;
end
else
begin
	if(enable_ex)
	begin
		aluin1<=src1;

		case(control_in[2:0])
		`ARITH_LOGIC:begin if(control_in[3])
					aluin2<=imm;
				  else
					aluin2<=src2; end
		`MEM_READ:begin	if(control_in[3])
					aluin2<=mem_data_read_in;
				else
					aluin2<=aluin2; end
		endcase

		operation_out<=control_in[6:4];
		opselect_out<=control_in[2:0];

		case(control_in[2:0])
		`SHIFT_REG:begin if(imm[2])
					shift_number<=src2[4:0];
				 else
					shift_number<=imm[10:6]; end
		default : shift_number<=0;
		endcase

		case(control_in[2:0])
		`ARITH_LOGIC:enable_arith<=1'b1;
		`MEM_READ:begin	if(control_in[3])
					enable_arith<=1'b1;
				else
					enable_arith<=1'b0; end
		default : enable_arith<=0;
		endcase

		if(control_in[2:0] == `SHIFT_REG)
			enable_shift<=1;
		else
			enable_shift<=0;
	end
	else
	begin
		aluin1<=aluin1;
		aluin2<=aluin2;
		operation_out<=operation_out;
		opselect_out<=opselect_out;
		shift_number<=0;
		enable_arith<=0;
		enable_shift<=0;
	end
end
end
endmodule

//SHIFT_ALU

`define CLK_PERIOD 10
`define REGISTER_WIDTH 32
`define INSTR_WIDTH 32
`define IMMEDIATE_WIDTH 16
`define MEM_READ 3'b101
`define MEM_WRITE 3'b100
`define ARITH_LOGIC 3'b001
`define SHIFT_REG 3'b000 
// SHIFTING
`define SHLEFTLOG 3'b000
`define SHLEFTART 3'b001
`define SHRGHTLOG 3'b010
`define SHRGHTART 3'b011

module shift_alu
(input clk,reset,enable,
input [31:0]in,
input [4:0]shift,
input [2:0]shift_operation,
output reg [32:0]aluout);
reg [31:0]w={32{1'b1}};

always@(posedge clk)
begin
	aluout<=aluout;
if(!reset)
	aluout<=0;
else
begin
	if(enable)
	begin
		case(shift_operation)
		`SHLEFTLOG : aluout <= in<<shift;
		`SHLEFTART : begin if(in[31]==0) aluout <= {1'b0,{in<<shift}};
					else aluout <= {1'b1,{in<<shift}};	end
		`SHRGHTLOG : aluout <= in>>shift;
		`SHRGHTART : begin 
				if(in[31]==1'b1)
					aluout <= {1'b0,{(in>>shift) | (w<<(32-shift))}};
				else
					aluout <= in>>shift;
			     end
		endcase
	end
end
end
endmodule


//Arithematic block of ALU

`define CLK_PERIOD 10
`define REGISTER_WIDTH 32
`define INSTR_WIDTH 32
`define IMMEDIATE_WIDTH 16
`define MEM_READ 3'b101
`define MEM_WRITE 3'b100
`define ARITH_LOGIC 3'b001
`define SHIFT_REG 3'b000

`define ADD	3'b000
`define HADD	3'b001
`define SUB	3'b010
`define NOT	3'b011
`define AND	3'b100
`define OR	3'b101
`define XOR	3'b110
`define LHG	3'b111

`define LOADBYTE 3'b000
`define LOADBYTEU 3'b100
`define LOADHALF 3'b001
`define LOADHALFU 3'b101
`define LOADWORD 3'b011
 
module arith_alu
(input clk,reset,enable,
input signed [31:0]aluin1,aluin2,
input [2:0]aluoperation,aluopselect,
output reg [32:0]aluout);
reg [15:0]h_add;
reg h_carry;
reg signed [31:0]r1,r2;
assign r1=aluin1;
assign r2=aluin2;
assign {h_carry,h_add}= aluin1[15:0] + aluin2[15:0];
always@(posedge clk)
begin
aluout <= aluout;
if(!reset)
	aluout<=0;
else
begin
	if(enable)
	begin
		case(aluopselect)
		`ARITH_LOGIC : begin
				case(aluoperation)
				`ADD : aluout <= r1 + r2;
				`HADD: aluout <= {h_carry,{16{h_add[15]}},h_add};
				`SUB : aluout <= r1 - r2;
				`NOT : aluout <= {1'b0,{~aluin2}};
				`AND : aluout <= {1'b0,{aluin1 & aluin2}};
				`OR  : aluout <= {1'b0,{aluin1 | aluin2}};
				`XOR : aluout <= {1'b0,{aluin1 ^ aluin2}};
				`LHG : aluout <= {1'b0,{aluin2[15:0]},16'b0};
				endcase
			      end
		`MEM_READ : begin
				case(aluoperation)
				`LOADBYTE : aluout <= {1'b0,{24{aluin2[7]}},aluin2[7:0]};
				`LOADBYTEU: aluout <= {25'b0,aluin2[7:0]};
				`LOADHALF : aluout <= {1'b0,{16{aluin2[15]}},aluin2[15:0]};
				`LOADHALFU: aluout <= {17'b0,aluin2[15:0]};
				`LOADWORD : aluout <= {1'b0,aluin2}; 
				endcase
			   end
		endcase
	end
end
end
endmodule


// d flip flop of the ALU

module alu_dff
(input clk,reset,d,
output reg q);
always@(posedge clk)
begin
if(!reset)
	q<=0;
else
	q<=~d;
end
endmodule

// multiplexer for the output selection of the ALU

module alu_mux
(input [31:0]a,b,
input s,
output [31:0]aluout);
assign aluout = s==1'b1 ? b : a;
endmodule


//mux logic for carry

module mux_c
(input a,b,s,
output carry);
assign carry = s==1'b1 ? b : a;
endmodule



//the compiled module of alu

module top_alu
(input clk,reset,enable_arith,enable_shift,
input [31:0]aluin1,aluin2,
input [2:0]operation,opselect,
input [4:0]shift_number,
output reg [31:0]aluout,
output reg carry);
wire [31:0]w1,w2;
wire c1,c2,w3;
arith_alu a1(.*,.enable(enable_arith),.aluoperation(operation),.aluopselect(opselect),.aluout({c1,w1}));

shift_alu s1(.*,.enable(enable_shift),.in(aluin1),.shift(shift_number),.shift_operation(opselect),.aluout({c2,w2}));

alu_dff d1(.*,.d(enable_arith),.q(w3));

alu_mux m1(.a(w1),.b(w2),.s(w3),.aluout(aluout));

mux_c k1(.a(c1),.b(c2),.s(w3),.carry(carry));

endmodule

//The top module connecting preprocessor and the ALU

module main_mod
(input clk,reset,enable_ex,
input [31:0]src1,src2,imm,mem_data_read_in,
input [6:0]control_in,
output reg [31:0]aluout,mem_data_write_out,
output reg carry,mem_data_write_en);

wire w_arith,w_shift;
wire [31:0]aluin1,aluin2;
wire [4:0]sh;
wire [2:0]w1,w2;
assign w1=control_in[6:4];
assign w2=control_in[2:0];

preprocessor p1(.*,.operation_out(w1),.opselect_out(w2),.mem_data_write_out(mem_data_write_out),.aluin1(aluin1),.aluin2(aluin2),.shift_number(sh),.enable_arith(w_arith),.enable_shift(w_shift));

top_alu a1(.*,.aluin1(aluin1),.aluin2(aluin2),.operation(w1),.opselect(w2),.enable_arith(w_arith),.enable_shift(w_shift),.shift_number(sh));

endmodule


//Packet

class packet;
rand bit enable_ex;
rand bit signed [31:0]src1;
rand bit signed [31:0]src2;
rand bit [31:0]imm;
rand bit [31:0]mem_data_read_in;
rand bit [6:0] control_in;
bit signed [31:0]aluout,mem_data_write_out;
bit carry,mem_data_write_en;
constraint c1 {enable_ex==1'b1;}
endclass

//PROBE_Packet

class p_packet;
bit clk,reset;
bit enable_ex;
bit [31:0]src1;
bit [31:0]src2;
bit [31:0]imm;
bit [31:0]mem_data_read_in;
bit signed [31:0]mem_data_write_out;
bit [6:0] control_in;
bit carry,mem_data_write_en;
bit enable_arith,enable_shift;
bit signed [31:0]alu_in1;
bit signed [31:0]alu_in2;
bit [2:0] operation_out,opselect_out;
bit [4:0]shift_number;
endclass

//Interface

interface intf(input clk,reset);
bit enable_ex;
bit signed [31:0]src1,src2,imm,mem_data_read_in;
bit [6:0] control_in;
bit signed [31:0]aluout,mem_data_write_out;
bit carry,mem_data_write_en;
endinterface

//Probe_Interface

interface p_intf
(input enable_ex,
input clk,
input reset,
input [31:0]src1,
input [31:0] src2,
input [31:0]imm,
input carry,mem_data_write_en,
input [31:0]mem_data_read_in,
input [31:0]mem_data_write_out,
input [6:0] control_in,
input bit enable_arith,enable_shift,
input signed [31:0]alu_in1,
input signed [31:0]alu_in2,
input signed [2:0] operation_out,opselect_out,
input [4:0]shift_number);
endinterface	

//generator

class generator;
packet p1=new();
mailbox #(packet)gen_drv;
function new(mailbox #(packet)gen_drv);
this.gen_drv=gen_drv;
endfunction
task run();
assert(p1.randomize())
gen_drv.put(p1);
else 
$display("randomizaton fail");
endtask
endclass
 		
//Driver

class driver;
packet p1;
mailbox #(packet)gen_drv;
virtual intf i;
function new(mailbox #(packet)gen_drv,virtual intf i);
this.gen_drv=gen_drv;
this.i=i;
endfunction
task run();
gen_drv.get(p1);
i.enable_ex=p1.enable_ex;
i.src1=p1.src1;
i.src2=p1.src2;
i.imm=p1.imm;
i.mem_data_read_in=p1.mem_data_read_in;
i.mem_data_write_out=p1.mem_data_write_out;
i.carry=p1.carry;
i.mem_data_write_en=p1.mem_data_write_en;
i.control_in=p1.control_in;
endtask
endclass		

//monitor

class monitor;
p_packet p1;
mailbox #(p_packet)mon_sb;
virtual p_intf p;
function new(mailbox #(p_packet)mon_sb,virtual p_intf p);
this.mon_sb=mon_sb;
this.p=p;
endfunction
task run();
p1=new();
p1.enable_ex=p.enable_ex;
p1.src1=p.src1;
p1.src2=p.src2;
p1.imm=p.imm;
p1.mem_data_read_in=p.mem_data_read_in;
p1.mem_data_write_out=p.mem_data_write_out;
p1.control_in=p.control_in;
p1.carry=p.carry;
p1.mem_data_write_en=p.mem_data_write_en;
p1.enable_arith=p.enable_arith;
p1.enable_shift=p.enable_shift;
p1.alu_in1=p.alu_in1;
p1.alu_in2=p.alu_in2;
p1.operation_out=p.operation_out;
p1.opselect_out=p.opselect_out;
p1.shift_number=p.shift_number;
p1.reset=p.reset;
mon_sb.put(p1);
endtask
endclass


//SCOREboard

class scoreboard;

	p_packet probePkt;
	
	mailbox #(p_packet) mb_mon_scb;

	bit scb_enable_ex;
	bit [31:0] scb_src1,scb_src2,scb_imm,scb_mem_data_read_in;
	bit [6:0]scb_control_in;
	bit scb_enable_arith,scb_enable_shift,scb_mem_data_write_en;
	bit [2:0] scb_operation_out,scb_opselect_out;
	bit [31:0] scb_mem_data_write_out,scb_alu_in1,scb_alu_in2;
	bit [4:0] scb_shift_number;

	function new(mailbox #(p_packet) mb_mon_scb);
		this.mb_mon_scb = mb_mon_scb;
	endfunction

	task run();

		//$display("SCOREBOARD OUTPUT");

		probePkt = new();
		mb_mon_scb.get(probePkt);

		scb_enable_ex = probePkt.enable_ex;
		scb_mem_data_read_in = probePkt.mem_data_read_in;
		scb_control_in = probePkt.control_in;
		scb_src1 = probePkt.src1;
		scb_src2 = probePkt.src2;
		scb_imm = probePkt.imm;

		
			if(scb_enable_ex==1'b1)
			begin
				scb_operation_out = scb_control_in[6:4];
				scb_opselect_out = scb_control_in[2:0];
				scb_alu_in1 = scb_src1;
				scb_mem_data_write_out = scb_src2;

				if((scb_opselect_out == 3'b100) && (scb_control_in[3] == 1))
				begin
					scb_mem_data_write_en=1'b1;
				end
			
				if(scb_control_in[2:0]==3'b001)
				begin
					if(scb_control_in[3]==1'b0)
						scb_alu_in2 = scb_src2;
					else if(scb_control_in == 1'b1)
						scb_alu_in2 = scb_imm;
					else
					begin
					end
				end
				else if(scb_control_in[2:0] == 3'b101)
				begin
					if(scb_control_in[3] == 1'b1)
						scb_alu_in2 = scb_mem_data_read_in;
				end
				else
				begin
				end
				if(scb_opselect_out == 3'b000)
				begin
					if(scb_imm[2]==1'b1)
						scb_shift_number = scb_src2[4:0];
					else
						scb_shift_number = scb_imm[10:6];
				end
				else if(scb_opselect_out == 3'b001)
				begin
					if((scb_control_in[3]==1'b0) || (scb_control_in[3]==1'b0))
						scb_enable_arith = 1'b1;
				end
				else if (scb_opselect_out == 3'b101)
				begin
					if(scb_control_in[3]==1'b0)
						scb_enable_arith = 1'b0;
					else
						scb_enable_arith = 1'b1;
				end
				else if (scb_opselect_out == 3'b000)
				begin
					scb_enable_shift = 1'b1;
				end
			end



		assert(probePkt.enable_arith == scb_enable_arith)
			$display("enable_arith match");
		else
			$error("enable_arith mismatch");

		assert(probePkt.enable_shift == scb_enable_shift)
			$display("enable_shift match");
		else
			$error("enable_shift mismatch");

		assert(probePkt.mem_data_write_en === scb_mem_data_write_en)
			$display("mem_data_write_en match");
		else
			$error("mem_data_write_en mismatch");

		assert(probePkt.operation_out == scb_operation_out)
			$display("operation_out match");
		else
			$error("operation_out mismatch");

		assert(probePkt.opselect_out == scb_opselect_out)
			$display("opselect_out match");
		else
			$error("opselect_out mismatch");

		assert(probePkt.mem_data_write_out === scb_mem_data_write_out)
			$display("mem_data_write_out match");
		else
			$error("mem_data_write_out mismatch");

		assert(probePkt.alu_in1 == scb_alu_in1)
			$display("alu_in1 match");
		else
			$error("alu_in1 mismatch");

		assert(probePkt.alu_in2 == scb_alu_in2)
			$display("alu_in2 match");
		else
			$error("alu_in2 mismatch");

		assert(probePkt.shift_number === scb_shift_number)
			$display("shift_number match");
		else
			$error("shift_number mismatch");

		

	endtask

	task pcInit();
		scb_alu_in1 = 32'h0;
		scb_alu_in2 = 32'h0;
		scb_shift_number = 5'h0;
		scb_enable_arith = 1'h0;
		scb_enable_shift= 1'h0;
		scb_operation_out = 3'h0;
		scb_opselect_out = 3'h0;
		scb_mem_data_write_out = 32'h0;
		scb_mem_data_write_en = 1'h0;
	endtask

endclass


//coverage 
class coverage;
virtual intf i;

covergroup cg @(posedge i.clk);
alu_src1_CP: coverpoint i.src1;
alu_src2_CP: coverpoint i.src2;
alu_imm_CP: coverpoint i.imm;
alu_mem_data_read_in_CP: coverpoint i.mem_data_read_in;
alu_control_in_CP: coverpoint i.control_in;
alu_alu_out_CP: coverpoint i.aluout;
alu_mem_data_write_out_CP: coverpoint i.mem_data_write_out;
alu_carry_CP: coverpoint i.carry;
alu_mem_data_write_en_CP: coverpoint i.mem_data_write_en;
alu_reset_cp: coverpoint i.reset;
alu_enable_ex_cp: coverpoint i.enable_ex;
endgroup

function new (virtual intf i);
this.i=i;
cg=new();
endfunction

task sample();
cg.sample();
endtask
endclass

//Environment

class environment;
mailbox #(packet)gen_drv;
mailbox #(p_packet)mon_sb;
virtual intf i;
virtual p_intf p;
generator g1;
driver d1;
monitor m1;
scoreboard s1;
coverage c1;
function new(virtual intf i,virtual p_intf p);
this.i=i;
this.p=p;
endfunction
function void build();
gen_drv=new();
mon_sb=new();
g1=new(gen_drv);
d1=new(gen_drv,i);
m1=new(mon_sb,p);
s1=new(mon_sb);
c1=new(i);
endfunction

task run();
g1.run();
d1.run();
m1.run();
s1.run();
c1.sample();
endtask
endclass


//TEST

//module test(intf i,p_intf p);
//environment e1;
//initial
//begin
//e1=new(i,p);
//e1.build();
//repeat(1000)
//#10 e1.run();
//end
//endmodule

program test(intf i,p_intf p);
environment e1;
initial
begin
e1=new(i,p);
e1.build();
repeat(1000)
@(negedge i.clk)
 e1.run();
end
endprogram

//TOP_MODULE

module TOP_ALU_arch3();
bit clk,rst;
always 
#5 clk++;

initial
begin
rst=1'b1;
#40 rst=1'b0;
#800 rst=1'b1;
#11 rst=1'b0;
end 

intf i(clk,rst);
main_mod a1(.clk(clk),.reset(reset),.enable_ex(i.enable_ex),
.src1(i.src1),.src2(i.src2),.imm(i.imm),.control_in(i.control_in),
.mem_data_read_in(i.mem_data_read_in),.aluout(i.aluout),
.carry(i.carry),.mem_data_write_out(i.mem_data_write_out),
.mem_data_write_en(i.mem_data_write_en));

p_intf p1(.clk(clk),.reset(reset),.enable_ex(a1.e1.enable_ex),
.src1(a1.e1.src1),.src2(a1.e1.src2),.imm(a1.e1.imm),
.mem_data_read_in(a1.e1.mem_data_read_in),.mem_data_write_out(a1.e1.mem_data_write_out),
.control_in(a1.e1.control_in),.enable_arith(a1.e1.enable_arith),
.carry(a1.e1.carry),.mem_data_write_en(a1.e1.mem_data_write_en),
.enable_shift(a1.e1.enable_shift),.alu_in1(a1.e1.alu_in1),
.alu_in2(a1.e1.alu_in2),.operation_out(a1.e1.operation_out),
.opselect_out(a1.e1.opselect_out),
.shift_number(a1.e1.shift_number));

test t1(i,p);

endmodule
