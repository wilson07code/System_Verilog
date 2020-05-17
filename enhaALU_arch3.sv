//PRE_processor

`define MEM_READ 3'b101
`define ARITH_LOGIC 3'b001
`define SHIFT_REG 3'b000

module ex_pp(clk,rst,enable_ex,src1,src2,imm,mem_data_read_in,control_in,enable_arith,enable_shift,alu_in1,alu_in2,operation_out,opselect_out,shift_number);
input clk,rst,enable_ex;
input signed [31:0]src1;
input signed [31:0]src2;
input [31:0]imm;
input [31:0]mem_data_read_in;
input [6:0] control_in;
output reg enable_arith,enable_shift;
output reg signed [31:0]alu_in1,alu_in2;
output reg [2:0] operation_out,opselect_out;
output reg [4:0]shift_number;

always @ (posedge clk)
begin

if(rst)
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
if(enable_ex)
begin
alu_in1<=src1;
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
alu_in2<=imm;
enable_arith<=1;
enable_shift<=0;
end
else
begin
alu_in2<=src2;
enable_arith<=1;
enable_shift<=0;
end
end
`MEM_READ:
begin
if(control_in[3])
begin
alu_in2<=mem_data_read_in;
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
end
endmodule

///Arithmetic_alu

`define ADD 3'b000 
`define HADD 3'b001
`define SUB 3'b010 
`define NOT 3'b011
`define AND 3'b100 
`define OR 3'b101
`define XOR 3'b110 
`define LHG 3'b111
`define MEM_READ 3'b101
`define MEM_WRITE 3'b100
`define ARITH_LOGIC 3'b001
`define SHIFT_REG 3'b000
`define LOADBYTE 3'b000
`define LOADBYTEU 3'b100
`define LOADHALF 3'b001
`define LOADHALFU 3'b101
`define LOADWORD 3'b011

module arith_alu(enable,clk,rst,alu_in1,alu_in2,alu_operation,alu_opselect,alu_out);
input enable,clk,rst;
input signed [31:0]alu_in1;
input signed [31:0]alu_in2;
input [2:0]alu_operation,alu_opselect;
output reg signed [32:0]alu_out;
logic h_carry;
logic [15:0]h_add;
always @ (posedge clk)
begin
if(rst)
alu_out<=0;
else if(enable)
begin
case({alu_opselect,alu_operation})
{`ARITH_LOGIC,`ADD}:alu_out<=alu_in1+alu_in2;
{`ARITH_LOGIC,`HADD}:
begin
{h_carry,h_add[15:0]} = alu_in1[15:0]+alu_in2[15:0];
if(h_add[15])
alu_out<={h_carry,16'b1,h_add};
else
alu_out<={h_carry,16'b0,h_add};
end
{`ARITH_LOGIC,`SUB}:alu_out<=alu_in1-alu_in2;
{`ARITH_LOGIC,`NOT}:alu_out<={1'b0,~(alu_in2)};
{`ARITH_LOGIC,`AND}:alu_out<={1'b0,(alu_in1&alu_in2)};
{`ARITH_LOGIC,`OR}:alu_out<={1'b0,(alu_in1|alu_in2)};
{`ARITH_LOGIC,`XOR}:alu_out<={1'b0,(alu_in1^alu_in2)};
{`ARITH_LOGIC,`LHG}:alu_out<={1'b0,alu_in2[15:0],16'b0};
{`MEM_READ,`LOADBYTE} :
begin
if(alu_in2[7])
alu_out<={1'b0,24'b1,alu_in2[7:0]};
else
alu_out<={25'b0,alu_in2[7:0]};
end
{`MEM_READ,`LOADBYTEU}:alu_out<={25'b0,alu_in2[7:0]};
{`MEM_READ,`LOADHALF}:
begin
if(alu_in2[15])
alu_out<={1'b0,24'b1,alu_in2[15:0]};
else
alu_out<={1'b0,24'b1,alu_in2[15:0]};
end
{`MEM_READ,`LOADHALFU}:alu_out<={25'b0,alu_in2[15:0]};
{`MEM_READ,`LOADWORD}:alu_out<={1'b0,alu_in2};
{`MEM_READ,3'b111}:alu_out<={1'b0,alu_in2};
{`MEM_READ,3'b111}:alu_out<={1'b0,alu_in2};
{`MEM_READ,3'b111}:alu_out<={1'b0,alu_in2};
default: alu_out<=alu_out;
endcase
end
else
alu_out<=alu_out;
end
endmodule

///D_ff

module dff(input logic clk,rst,d,output logic y);
always @ (posedge clk)
begin
if(rst)
y<=0;
else
y<=d;
end
endmodule

//MUX_21

module mux21(s,in1,in2,y);
input s;
input signed [31:0]in1;
input [31:0]in2;
output [31:0]y;
assign y=(s==1'b1)?in1:in2;
endmodule

//shift ALU

`define SHLEFTLOG 3'b000
`define SHLEFTART 3'b001
`define SHRGHTLOG 3'b010
`define SHRGHTART 3'b011

module shift_alu(clk,rst,enable,in,shift,shift_operation,shift_alu_out);
input clk,rst,enable;
input signed [31:0]in;
input [4:0]shift;
input [2:0]shift_operation;
output reg signed [31:0] shift_alu_out;
always @ (posedge clk)
begin
if(rst)
shift_alu_out<=0;
else if (enable)
begin
case(shift_operation)
`SHLEFTLOG:shift_alu_out<=in << shift;
`SHLEFTART:shift_alu_out<=in <<< shift;
`SHRGHTLOG:shift_alu_out<=in >> shift;
`SHRGHTART:shift_alu_out<=in >>> shift;
default: shift_alu_out<=shift_alu_out;
endcase
end
else
shift_alu_out<=shift_alu_out;
end
endmodule

//ALU

module alu(clk,rst,enable_arith,enable_shift,alu_in1,alu_in2,operation_out,opselect_out,shift_number,alu_out,carry);
input clk,rst;
input enable_arith,enable_shift;
input signed [31:0]alu_in1;
input signed [31:0]alu_in2;
input [2:0] operation_out,opselect_out;
input [4:0]shift_number;
output logic signed [31:0]alu_out;
output logic carry;
wire [31:0] shift_alu_out;
shift_alu s1(.*,.in(alu_in1),.shift(shift_number),.shift_operation(operation_out),.enable(enable_shift)); 
wire [32:0] arith_alu_out;
arith_alu a1(.enable(enable_arith),.*,.alu_operation(operation_out),.alu_opselect(opselect_out),.alu_out(arith_alu_out));
wire s;
dff d1(.*,.d(enable_arith),.y(s));
mux21 m1(.s(s),.in1({arith_alu_out[31:0]}),.in2(shift_alu_out),.y(alu_out));
assign carry=arith_alu_out[32];
endmodule

//ALU_top

module alu_top(clk,rst,enable_ex,src1,src2,imm,control_in,mem_data_read_in,alu_out,carry);
input clk,rst,enable_ex;
input signed [31:0]src1;
input signed [31:0]src2;
input [31:0]imm;
input [31:0]mem_data_read_in;
input [6:0] control_in;
output signed [31:0]alu_out;
output carry;
wire enable_arith,enable_shift;
wire signed [31:0]alu_in1,alu_in2;
wire [2:0] operation_out,opselect_out;
wire [4:0]shift_number;
ex_pp e1(.*);
alu a1(.*);
endmodule

//Packet

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

//PROBE_Packet

class p_packet;
bit clk,rst;
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

//Interface

interface intf(input clk,rst);
bit enable_ex;
bit signed [31:0]src1,src2,imm,mem_data_read_in;
bit [6:0] control_in;
bit signed [31:0]alu_out;
bit carry;
endinterface

//Probe_Interface

interface p_intf
(input enable_ex,
input clk,
input rst,
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
p1.control_in=p.control_in;
p1.enable_arith=p.enable_arith;
p1.enable_shift=p.enable_shift;
p1.alu_in1=p.alu_in1;
p1.alu_in2=p.alu_in2;
p1.operation_out=p.operation_out;
p1.opselect_out=p.opselect_out;
p1.shift_number=p.shift_number;
p1.rst=p.rst;
mon_sb.put(p1);
endtask
endclass

//Scoreboard

`define MEM_READ 3'b101
`define ARITH_LOGIC 3'b001
`define SHIFT_REG 3'b000
class scoreboard;
p_packet p1;
mailbox #(p_packet)mon_sb;
local bit enable_ex,enable_arith,enable_shift;
local bit signed [31:0]alu_in1,alu_in2;
local bit [2:0] operation_out,opselect_out;
local bit [4:0]shift_number;

function new(mailbox #(p_packet)mon_sb);
this.mon_sb=mon_sb;
endfunction

task run();

mon_sb.get(p1);

// pre-processor dummy logic

if(p1.rst)
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
//default:
//begin
//alu_in1<=alu_in1;
//alu_in2<=alu_in2;
//shift_number<=0;
////enable_arith<=0;
//enable_shift<=0;
//end
endcase
end
//else
//begin
//alu_in1<=alu_in1;
//alu_in2<=alu_in2;
//operation_out<=operation_out;
//opselect_out<=opselect_out;
//shift_number<=0;
//enable_arith<=0;
//enable_shift<=0;
//end
//end of pre-processor dummy logic
assert(enable_arith==p1.enable_arith && enable_shift==p1.enable_shift && alu_in1==p1.alu_in1 && alu_in2==p1.alu_in2 &&
 operation_out==p1.operation_out && opselect_out==p1.opselect_out && shift_number==p1.shift_number)
begin
$display($time,"----------hit------------");
$display("en_ar1=%d,en_ar2=%d,en_s1=%d,en_s2=%d,alu_in1_dummy=%d,alu_in1=%d,alu_in2_dummy=%d,alu_in2=%d,op_out_dummy=%d,op_out=%d,op_sel_dummy=%d,op_sel=%d,shift_dummy=%d,shift=%d",enable_arith,p1.enable_arith,enable_shift,p1.enable_shift,alu_in1,p1.alu_in1,alu_in2,p1.alu_in2,
operation_out,p1.operation_out,opselect_out,p1.opselect_out,shift_number,p1.shift_number);
end
else
begin
$display($time,"-------miss---------------");
$display("en_ar1=%d,en_ar2=%d,en_s1=%d,en_s2=%d,alu_in1_dummy=%d,alu_in1=%d,alu_in2_dummy=%d,alu_in2=%d,op_out_dummy=%d,op_out=%d,op_sel_dummy=%d,op_sel=%d,shift_dummy=%d,shift=%d",enable_arith,p1.enable_arith,enable_shift,p1.enable_shift,alu_in1,p1.alu_in1,alu_in2,p1.alu_in2,
operation_out,p1.operation_out,opselect_out,p1.opselect_out,shift_number,p1.shift_number);
end
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
alu_alu_out_CP: coverpoint i.alu_out {bins ao1 = {32'h0};}
//alu_mem_data_write_out_CP: coverpoint i.mem_data_write_out;
alu_carry_CP: coverpoint i.carry;
//alu_mem_data_write_en_CP: coverpoint i.mem_data_write_en;
alu_rst_cp: coverpoint i.rst;
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

module test(intf i,p_intf p);
environment e1;
initial
begin
e1=new(i,p);
e1.build();
repeat(10000)
@(negedge i.clk)
 e1.run();
end
endmodule

//TOP_MODULE

module ALU_arch3_top();
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
alu_top a1(.clk(clk),.rst(rst),.enable_ex(i.enable_ex),.src1(i.src1),.src2(i.src2),.imm(i.imm),.control_in(i.control_in),.mem_data_read_in(i.mem_data_read_in),.alu_out(i.alu_out),.carry(i.carry));
p_intf p(.clk(clk),.rst(rst),.enable_ex(a1.e1.enable_ex),.src1(a1.e1.src1),.src2(a1.e1.src2),.imm(a1.e1.imm),.mem_data_read_in(a1.e1.mem_data_read_in),.control_in(a1.e1.control_in),.enable_arith(a1.e1.enable_arith),.enable_shift(a1.e1.enable_shift),.alu_in1(a1.e1.alu_in1),.alu_in2(a1.e1.alu_in2),.operation_out(a1.e1.operation_out),.opselect_out(a1.e1.opselect_out),.shift_number(a1.e1.shift_number));
test t1(i,p);
endmodule

