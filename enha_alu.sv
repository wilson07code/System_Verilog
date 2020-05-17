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
input [31:0] src1,src2,imm,mem_data_read_in,
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


//alu_shift
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
module topmodule_enhanced_alu
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




//transaction
class env_enhancedalu_transaction;
//input clk,reset,enable_ex,
rand bit [31:0]src1;
rand bit [31:0]src2;
rand bit [31:0]imm;
rand bit [31:0]mem_data_read_in;
rand bit [6:0]control_in;
bit [31:0]aluout;
bit [31:0]mem_data_write_out;
bit carry,mem_data_write_en;
endclass



//interface
interface env_enhancedalu_interface (input bit clk,reset,enable_ex);
bit [31:0]src1,src2,imm,mem_data_read_in;
bit [6:0]control_in;
bit [31:0]aluout,mem_data_write_out;
bit carry,mem_data_write_en;
endinterface



// interface j
interface env_enhancedalu_rinterface (input bit clk,reset,enable_ex);
bit [31:0]src1,src2,imm,mem_data_read_in;
bit [6:0]control_in;
bit [31:0]aluout,mem_data_write_out;
bit carry,mem_data_write_en;
endinterface




//env_generator
class env_enhancedalu_generator;
env_enhancedalu_transaction pkt;
mailbox #(env_enhancedalu_transaction)gen_drv;

function new (mailbox #(env_enhancedalu_transaction)gen_drv);
this.gen_drv=gen_drv;
endfunction

task run;
pkt=new();
assert(pkt.randomize())
begin
$display("Randomization successful.");
gen_drv.put(pkt);
end
else 
$display("Randomization failure.");
endtask
endclass




//driver
class env_enhancedalu_driver;
env_enhancedalu_transaction pkt;
mailbox #(env_enhancedalu_transaction)gen_drv;
virtual env_enhancedalu_interface i;
virtual env_enhancedalu_rinterface ri;

function new (mailbox #(env_enhancedalu_transaction)gen_drv,virtual env_enhancedalu_interface i,virtual env_enhancedalu_rinterface ri);
this.gen_drv=gen_drv;
this.i=i;
this.ri=ri;
endfunction

task run;
gen_drv.get(pkt);
i.src1=pkt.src1;
i.src2=pkt.src2;
i.imm=pkt.imm;
i.mem_data_read_in=pkt.mem_data_read_in;
i.control_in=pkt.control_in;

ri.src1=pkt.src1;
ri.src2=pkt.src2;
ri.imm=pkt.imm;
ri.mem_data_read_in=pkt.mem_data_read_in;
ri.control_in=pkt.control_in;                
                                         
endtask
endclass



//monitor
class env_enhancedalu_monitor;
env_enhancedalu_transaction pkt1,pkt2;
mailbox #(env_enhancedalu_transaction)mon_sb;
mailbox #(env_enhancedalu_transaction)mon_sb2;
virtual env_enhancedalu_interface i;
virtual env_enhancedalu_rinterface ri;

function new (mailbox #(env_enhancedalu_transaction)mon_sb,mailbox #(env_enhancedalu_transaction)mon_sb2,virtual env_enhancedalu_interface i,virtual env_enhancedalu_rinterface ri);
this.mon_sb=mon_sb;
this.mon_sb2=mon_sb2;
this.i=i;
this.ri=ri;
endfunction

task run;
pkt1=new();
pkt2=new();

pkt1.src1=i.src1;
pkt1.src2=i.src2;
pkt1.imm=i.imm;
pkt1.mem_data_read_in=i.mem_data_read_in;
pkt1.control_in=i.control_in;
 
pkt1.aluout=i.aluout;
pkt1.mem_data_write_out=i.mem_data_write_out;
pkt1.carry=i.carry;
pkt1.mem_data_write_en=i.mem_data_write_en;

pkt2.src2=i.src2;
pkt2.imm=i.imm;
pkt2.mem_data_read_in=i.mem_data_read_in;
pkt2.control_in=i.control_in;
 
pkt2.aluout=i.aluout;
pkt2.mem_data_write_out=i.mem_data_write_out;
pkt2.carry=i.carry;
pkt2.mem_data_write_en=i.mem_data_write_en;

$display($time," pkt1.src1=%0b pkt1.src2=%0b pkt1.imm=%0b pkt1.mem_data_read_in=%0b pkt1.control_in=%0b pkt1.aluout=%0b pkt1.mem_data_write_out=%0b pkt1.carry=%0b pkt1.mem_data_write_en=%0b",pkt1.src1,pkt1.src2,pkt1.imm,pkt1.mem_data_read_in,pkt1.control_in,pkt1.aluout,pkt1.mem_data_write_out,pkt1.carry,pkt1.mem_data_write_en);
$display($time," pkt1.src1=%0b pkt1.src2=%0b pkt1.imm=%0b pkt1.mem_data_read_in=%0b pkt1.control_in=%0b pkt1.aluout=%0b pkt1.mem_data_write_out=%0b pkt1.carry=%0b pkt1.mem_data_write_en=%0b",pkt1.src1,pkt1.src2,pkt1.imm,pkt1.mem_data_read_in,pkt1.control_in,pkt1.aluout,pkt1.mem_data_write_out,pkt1.carry,pkt1.mem_data_write_en);

mon_sb.put(pkt1);
mon_sb2.put(pkt2);
endtask
endclass



//scoreboard
class env_enhancedalu_scoreboard;
env_enhancedalu_transaction pkt1,pkt2;
mailbox #(env_enhancedalu_transaction)mon_sb;
mailbox #(env_enhancedalu_transaction)mon_sb2;

function new(mailbox #(env_enhancedalu_transaction)mon_sb,mailbox #(env_enhancedalu_transaction)mon_sb2);
this.mon_sb=mon_sb;
this.mon_sb2=mon_sb2;
endfunction

task run;
mon_sb.get(pkt1);
mon_sb2.get(pkt2);
assert(pkt1.aluout==pkt2.aluout && pkt1.mem_data_write_out==pkt2.mem_data_write_out && pkt1.carry==pkt2.carry && pkt1.mem_data_write_en==pkt2.mem_data_write_en)
begin
$display("Design is okay.");
end
else
begin
$display("Design is not okay.");
end
endtask
endclass


//coverage
class env_enhancedalu_coverage;
virtual env_enhancedalu_interface i;

covergroup cg @(posedge i.clk);
enhancedalu_src1_CP: coverpoint i.src1;
enhancedalu_src2_CP: coverpoint i.src2;
enhancedalu_imm_CP: coverpoint i.imm;
enhancedalu_mem_data_read_in_CP: coverpoint i.mem_data_read_in;
enhancedalu_control_in_CP: coverpoint i.control_in;
enhancedalu_aluout_CP: coverpoint i.aluout {bins ao1 = {32'h0};}
enhancedalu_mem_data_write_out_CP: coverpoint i.mem_data_write_out;
enhancedalu_carry_CP: coverpoint i.carry;
enhancedalu_mem_data_write_en_CP: coverpoint i.mem_data_write_en;
enhancedalu_reset_cp: coverpoint i.reset;
enhancedalu_enable_ex_cp: coverpoint i.enable_ex;
endgroup

function new (virtual env_enhancedalu_interface i);
this.i=i;
cg=new();
endfunction

task sample();
cg.sample();
endtask
endclass



//environment
class env_enhancedalu_environment;
mailbox #(env_enhancedalu_transaction)gen_drv;
mailbox #(env_enhancedalu_transaction)mon_sb;
mailbox #(env_enhancedalu_transaction)mon_sb2;
virtual env_enhancedalu_interface i;
virtual env_enhancedalu_rinterface ri;
env_enhancedalu_generator g1;
env_enhancedalu_driver d1;
env_enhancedalu_monitor m1;
env_enhancedalu_coverage c1;
env_enhancedalu_scoreboard s1;

function new (virtual env_enhancedalu_interface i,virtual env_enhancedalu_rinterface ri);
this.i=i;
this.ri=ri;
endfunction

function void build;
gen_drv=new();
mon_sb=new();
mon_sb2=new();
g1=new(gen_drv);
d1=new(gen_drv,i,ri);
m1=new(mon_sb,mon_sb2,i,ri);
s1=new(mon_sb,mon_sb2);
c1=new(i);
endfunction

task run;
fork
g1.run();
d1.run();
c1.sample();
m1.run();
s1.run();
join
endtask
endclass



//test
module env_enhancedalu_test(env_enhancedalu_interface i,env_enhancedalu_rinterface ri);
env_enhancedalu_environment en;

initial
begin
en=new(i,ri);
en.build();
repeat(10000)
begin
#10 en.run();
end
end
endmodule



//top
module enhancedalu_top_architecture_2;
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

env_enhancedalu_interface i(clk,reset,enable_ex);
env_enhancedalu_rinterface ri(clk,reset,enable_ex);
env_enhancedalu_test T(i,ri);


topmodule_enhanced_alu alu1 (.clk(clk),.reset(reset),.enable_ex(enable_ex),.src1(i.src1),.src2(i.src2),.imm(i.imm),.mem_data_read_in(i.mem_data_read_in),.control_in(i.control_in),.aluout(i.aluout),.mem_data_write_out(i.mem_data_write_out),.carry(i.carry),.mem_data_write_en(i.mem_data_write_en));
topmodule_enhanced_alu alu2 (.clk(clk),.reset(reset),.enable_ex(enable_ex),.src1(ri.src1),.src2(ri.src2),.imm(ri.imm),.mem_data_read_in(ri.mem_data_read_in),.control_in(ri.control_in),.aluout(ri.aluout),.mem_data_write_out(ri.mem_data_write_out),.carry(ri.carry),.mem_data_write_en(ri.mem_data_write_en));
endmodule
