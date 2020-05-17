//stage 1 - the execute preprocessor
`define MEM_READ 3'b101
`define ARITH_LOGIC 3'b001
`define SHIFT_REG 3'b000

module ex_pp(clk,reset,enable_ex,src1,src2,imm,mem_data_read_in,control_in,enable_arith,enable_shift,aluin1,aluin2,operation_out,opselect_out,shift_number);
input clk,reset,enable_ex;
input signed [31:0]src1;
input signed [31:0]src2;
input [31:0]imm;
input [31:0]mem_data_read_in;
input [6:0] control_in;
output reg enable_arith,enable_shift;
output reg signed [31:0]aluin1,aluin2;
output reg [2:0] operation_out,opselect_out;
output reg [4:0]shift_number;


always @ (posedge clk)
begin

if(reset)
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
if(enable_ex)
begin
aluin1<=src1;
operation_out<=control_in[6:4];
opselect_out<=control_in[2:0];
case(opselect_out)
`SHIFT_REG:
begin
enable_arith<=0;
enable_shift<=1;
if(imm[2])
shift_number<=src2[4:0];
else
shift_number<=imm[10:6];
end
`ARITH_LOGIC:
begin
if(control_in[3])
begin
aluin2<=imm;
enable_arith<=1;
enable_shift<=0;
end
else
begin
aluin2<=src2;
enable_arith<=1;
enable_shift<=0;
end
end
`MEM_READ:
begin
if(control_in[3])
begin
aluin2<=mem_data_read_in;
enable_arith<=1;
enable_shift<=0;
end
else
begin
aluin2<=aluin2;
enable_arith<=0;
enable_shift<=0;
end
end
default:
begin
aluin1<=aluin1;
aluin2<=aluin2;
shift_number<=0;
enable_arith<=0;
enable_shift<=0;
end
endcase
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
endmodule




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
output reg [32:0]alu_out);
reg [31:0]w={32{1'b1}};

always@(posedge clk)
begin
	alu_out<=alu_out;
if(!reset)
	alu_out<=0;
else
begin
	if(enable)
	begin
		case(shift_operation)
		`SHLEFTLOG : alu_out <= in<<shift;
		`SHLEFTART : begin if(in[31]==0) alu_out <= {1'b0,{in<<shift}};
					else alu_out <= {1'b1,{in<<shift}};	end
		`SHRGHTLOG : alu_out <= in>>shift;
		`SHRGHTART : begin 
				if(in[31]==1'b1)
					alu_out <= {1'b0,{(in>>shift) | (w<<(32-shift))}};
				else
					alu_out <= in>>shift;
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
output reg [32:0]alu_out);
reg [15:0]h_add;
reg h_carry;
reg signed [31:0]r1,r2;
assign r1=aluin1;
assign r2=aluin2;
assign {h_carry,h_add}= aluin1[15:0] + aluin2[15:0];
always@(posedge clk)
begin
alu_out <= alu_out;
if(!reset)
	alu_out<=0;
else
begin
	if(enable)
	begin
		case(aluopselect)
		`ARITH_LOGIC : begin
				case(aluoperation)
				`ADD : alu_out <= r1 + r2;
				`HADD: alu_out <= {h_carry,{16{h_add[15]}},h_add};
				`SUB : alu_out <= r1 - r2;
				`NOT : alu_out <= {1'b0,{~aluin2}};
				`AND : alu_out <= {1'b0,{aluin1 & aluin2}};
				`OR  : alu_out <= {1'b0,{aluin1 | aluin2}};
				`XOR : alu_out <= {1'b0,{aluin1 ^ aluin2}};
				`LHG : alu_out <= {1'b0,{aluin2[15:0]},16'b0};
				endcase
			      end
		`MEM_READ : begin
				case(aluoperation)
				`LOADBYTE : alu_out <= {1'b0,{24{aluin2[7]}},aluin2[7:0]};
				`LOADBYTEU: alu_out <= {25'b0,aluin2[7:0]};
				`LOADHALF : alu_out <= {1'b0,{16{aluin2[15]}},aluin2[15:0]};
				`LOADHALFU: alu_out <= {17'b0,aluin2[15:0]};
				`LOADWORD : alu_out <= {1'b0,aluin2}; 
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
output [31:0]alu_out);
assign alu_out = s==1'b1 ? b : a;
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
output reg [31:0]alu_out,
output reg carry);
wire [31:0]w1,w2;
wire c1,c2,w3;
arith_alu a1(.*,.enable(enable_arith),.aluoperation(operation),.aluopselect(opselect),.alu_out({c1,w1}));

shift_alu s1(.*,.enable(enable_shift),.in(aluin1),.shift(shift_number),.shift_operation(opselect),.alu_out({c2,w2}));

alu_dff d1(.*,.d(enable_arith),.q(w3));

alu_mux m1(.a(w1),.b(w2),.s(w3),.alu_out(alu_out));

mux_c k1(.a(c1),.b(c2),.s(w3),.carry(carry));

endmodule

//The top module connecting preprocessor and the ALU
module main_mod
(input clk,reset,enable_ex,
input [31:0]src1,src2,imm,mem_data_read_in,
input [6:0]control_in,
output reg [31:0]alu_out,mem_data_write_out,
output reg carry,mem_data_write_en);

wire w_arith,w_shift;
wire [31:0]aluin1,aluin2;
wire [4:0]sh;
wire [2:0]w1,w2;
assign w1=control_in[6:4];
assign w2=control_in[2:0];

ex_pp p1(.*,.operation_out(w1),.opselect_out(w2),.aluin1(aluin1),.aluin2(aluin2),.shift_number(sh),.enable_arith(w_arith),.enable_shift(w_shift));

top_alu a1(.*,.aluin1(aluin1),.aluin2(aluin2),.operation(w1),.opselect(w2),.enable_arith(w_arith),.enable_shift(w_shift),.shift_number(sh));

endmodule

//packet
class packet;
rand bit enable_ex;
rand bit signed [31:0]src1;
rand bit signed [31:0]src2;
rand bit [31:0]imm;
rand bit [31:0]mem_data_read_in;
rand bit [6:0] control_in;
bit signed [31:0]alu_out;
bit carry;
constraint c1 {enable_ex==1'b1;}
endclass


//probe_packet
class p_packet;
bit clk,reset;
bit enable_ex;
bit signed [31:0]src1;
bit signed [31:0]src2;
bit [31:0]imm;
bit [31:0]mem_data_read_in;
bit [6:0] control_in;
bit enable_arith,enable_shift;
bit signed [31:0]alu_in1;
bit signed [31:0]alu_in2;
bit [2:0] operation_out,opselect_out;
bit [4:0]shift_number;
endclass

//interface
interface intf(input clk,reset);
bit enable_ex;
bit signed [31:0]src1,src2,imm,mem_data_read_in;
bit [6:0] control_in;
bit signed [31:0]alu_out;
bit carry;
endinterface

//probe_interface
interface p_intf
(input enable_ex,
input clk,
input reset,
input signed [31:0]src1,
input signed [31:0] src2,
input [31:0]imm,
input [31:0]mem_data_read_in,
input [6:0] control_in,
input bit enable_arith,enable_shift,
input signed [31:0]alu_in1,
input signed [31:0]alu_in2,
input [2:0] operation_out,opselect_out,
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

//driver
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
i.control_in=p1.control_in;
endtask
endclass

//monitor

class monitor;
p_packet p1=new();
mailbox #(p_packet)mon_sb;
virtual p_intf p;
function new(mailbox #(p_packet)mon_sb,virtual p_intf p);
this.mon_sb=mon_sb;
this.p=p;
endfunction
task run();
p1.enable_ex=p.enable_ex;
p1.src1=p.src1;
p1.src2=p.src2;
p1.imm=p.imm;
p1.mem_data_read_in=p.mem_data_read_in;
p1.control_in=p.control_in;
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

//scoreboard
`define MEM_READ 3'b101
`define ARITH_LOGIC 3'b001
`define SHIFT_REG 3'b000
class scoreboard;
p_packet p1;
mailbox #(p_packet)mon_sb;
local bit enable_arith,enable_shift;
local bit signed [31:0]alu_in1,alu_in2;
local bit [2:0] operation_out,opselect_out;
local bit [4:0]shift_number;
function new(mailbox #(p_packet)mon_sb);
this.mon_sb=mon_sb;
endfunction
task run();
mon_sb.get(p1);
// pre-processor dummy logic
if(p1.reset)
begin
alu_in1<=0;
alu_in2<=0;
operation_out<=0;
opselect_out<=0;
shift_number<=0;
enable_arith<=0;
enable_shift<=0;
end
else
if(p1.enable_ex)
begin
alu_in1<=p1.src1;
operation_out<=p1.control_in[6:4];
opselect_out<=p1.control_in[2:0];
case(opselect_out)
`SHIFT_REG:
begin
enable_arith<=0;
enable_shift<=1;
if(p1.imm[2])
shift_number<=p1.src2[4:0];
else
shift_number<=p1.imm[10:6];
end
`ARITH_LOGIC:
begin
if(p1.control_in[3])
begin
alu_in2<=p1.imm;
enable_arith<=1;
enable_shift<=0;
end
else
begin
alu_in2<=p1.src2;
enable_arith<=1;
enable_shift<=0;
end
end
`MEM_READ:
begin
if(p1.control_in[3])
begin
alu_in2<=p1.mem_data_read_in;
enable_arith<=1;
enable_shift<=0;
end
else
begin
alu_in2<=alu_in2;
enable_arith<=0;
enable_shift<=0;
end
end
default:
begin
alu_in1<=alu_in1;
alu_in2<=alu_in2;
shift_number<=0;
enable_arith<=0;
enable_shift<=0;
end
endcase
end
else
begin
alu_in1<=alu_in1;
alu_in2<=alu_in2;
operation_out<=operation_out;
opselect_out<=opselect_out;
shift_number<=0;
enable_arith<=0;
enable_shift<=0;
end
//end of pre-processor dummy logic
assert(enable_arith===p1.enable_arith && enable_shift===p1.enable_shift && alu_in1===p1.alu_in1 && alu_in2===p1.alu_in2 &&
 operation_out===p1.operation_out && opselect_out===p1.opselect_out && shift_number===p1.shift_number)
begin
$display($time,"design is done");
$display("en_ar1=%d,en_ar2=%d,en_s1=%d,en_s2=%d,alu_in1_dummy=%d,alu_in1=%d,alu_in2_dummy=%d,alu_in2=%d,op_out_dummy=%d,op_out=%d,op_sel_dummy=%d,op_sel=%d,shift_dummy=%d,shift=%d",enable_arith,p1.enable_arith,enable_shift,p1.enable_shift,alu_in1,p1.alu_in1,alu_in2,p1.alu_in2,
operation_out,p1.operation_out,opselect_out,p1.opselect_out,shift_number,p1.shift_number);
end
else
begin
$display($time,"-design is failed-");
$display("en_ar1=%d,en_ar2=%d,en_s1=%d,en_s2=%d,alu_in1_dummy=%d,alu_in1=%d,alu_in2_dummy=%d,alu_in2=%d,op_out_dummy=%d,op_out=%d,op_sel_dummy=%d,op_sel=%d,shift_dummy=%d,shift=%d",enable_arith,p1.enable_arith,enable_shift,p1.enable_shift,alu_in1,p1.alu_in1,alu_in2,p1.alu_in2,
operation_out,p1.operation_out,opselect_out,p1.opselect_out,shift_number,p1.shift_number);
end
endtask
endclass


//environment

class environment;
mailbox #(packet)gen_drv;
mailbox #(p_packet)mon_sb;
virtual intf i;
virtual p_intf p;
generator g1;
driver d1;
monitor m1;
scoreboard s1;
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
endfunction
task run();
g1.run();
d1.run();
#1 m1.run();
s1.run();
endtask
endclass

//test

module test(intf i,p_intf p);
environment e1;
initial
begin
e1=new(i,p);
e1.build();
repeat(10000)
begin
#10 e1.run();
end
end
endmodule

//top_TB

module top_arch3();
bit clk,reset,enable_ex;
//Clock generation
initial
begin 
clk = 1'b0;
forever
#5 clk = ~clk;
end

//enable_ex
initial
begin
enable_ex=1'b0;
#10;
enable_ex=1'b1;
#10;
enable_ex=1'b0;
#10;
enable_ex=1'b1;
end

//Reset generation
initial 
begin
reset=1'b0;
#10;
reset=1'b1;
#50;
reset=1'b0;
#10;
reset=1'b1;
end

intf i(clk,reset);
main_mod a1(.clk(clk),.reset(reset),.enable_ex(i.enable_ex),.src1(i.src1),.src2(i.src2),.imm(i.imm),.control_in(i.control_in),.mem_data_read_in(i.mem_data_read_in),.alu_out(i.alu_out),.carry(i.carry));
p_intf p(.clk(clk),.reset(reset),.enable_ex(p.enable_ex),.src1(p.src1),.src2(p.src2),.imm(p.imm),.mem_data_read_in(p.mem_data_read_in),
.control_in(p.control_in),.enable_arith(p.enable_arith),.enable_shift(p.enable_shift),.alu_in1(p.alu_in1),.alu_in2(p.alu_in2),
.operation_out(p.operation_out),.opselect_out(p.opselect_out),.shift_number(p.shift_number));
test t1(i,p);
endmodule

