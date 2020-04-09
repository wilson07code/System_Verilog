////////////priority logic__DUT---1/////////////////////////

module priority_logic
(input enable,reset,
 input [3:0] in,
 output reg [3:0] op);

always @ (reset,enable,in)
begin
	if(reset==1'b0)
	begin
		op=4'b0000;
	end
	else if(enable==1'b0)
		begin
			op=4'b0000;
		end
		else if(in[0]==1'b1)
			begin
				op=4'b0001;
			end
			else if(in[1]==1'b1)
				begin
					op=4'b0010;
				end
				else if(in[2]==1'b1)
					begin
						op=4'b0100;
					end
					else if(in[3]==1'b1)
						begin
							op=4'b1000;
						end
						else
						begin
							op=4'b0000;
						end
end
endmodule

//////////////////priority_logic_.vfile---2//////////

module priority_logic
(input enable,reset,
 input [3:0] in,
 output reg [3:0] op);

always @ (reset,enable,in)
begin
	if(reset==1'b0)
	begin
		op=4'b0000;
	end
	else if(enable==1'b0)
		begin
			op=4'b0000;
		end
		else if(in[0]==1'b1)
			begin
				op=4'b0001;
			end
			else if(in[1]==1'b1)
				begin
					op=4'b0010;
				end
				else if(in[2]==1'b1)
					begin
						op=4'b0100;
					end
					else if(in[3]==1'b1)
						begin
							op=4'b1000;
						end
						else
						begin
							op=4'b0000;
						end
end
endmodule

///////////dummy_priority_dut----3/////////////

module priority_logic_dummy
//PORT DECLARATION
(input en,reset,
 input a3,a2,a1,a0,
 output reg [3:0] y);

//PROCEDURAL BLOCK
always@(reset,en,a3,a2,a1,a0)
begin
	if(!reset)
		y=4'b0000;
	else if(!en)
		y=4'b0000;
	else
	begin
		if(a0)
			y=4'b0001;
		else if(a1)
			y=4'b0010;
		else if(a2)
			y=4'b0100;
		else if(a3)
			y=4'b1000;
		else
			y=4'b0000;
	end
end
endmodule


////////////////////ring counter_dut---4////////////////

module ring_counter
(input clock,reset,enable,
 output reg [3:0] token);

always @ (posedge clock)
begin
	if (reset==1'b0)
	   token<=4'b0001;
   else if (enable==1'b1)
	   token<={token[2:0],token[3]};
	else
	   token<=token;
end
endmodule

///////////ring counter.v file---5//////////////

module ring_counter
(input clock,reset,enable,
 output reg [3:0] token);

always @ (posedge clock)
begin
	if (reset==1'b0)
	   token<=4'b0001;
   else if (enable==1'b1)
	   token<={token[2:0],token[3]};
	else
	   token<=token;
end
endmodule

////////////////////ring counter _dummy_dut---6///////////////////

module ring_counter_dummy
//PORT DECLARATION
(input clock,reset,en,
 output reg [3:0] q);

//PROCEDURAL BLOCK
always@(posedge clock)
begin
	if(!reset)
		q<=4'b0001;
	else if(en)
		q<={q[2:0],q[3]};//LEFT SHIFTING
end
endmodule

////////////////arbiter.v_file----7/////////////

module arbiter
(input clock,reset,ack,
 input [3:0] req,
 output [3:0] grant);
wire [15:0] priority_op_wire;
wire [3:0] token_wire;

ring_counter M1 (.clock(clock),.reset(reset),.enable(ack),.token(token_wire));

priority_logic M2 (.enable(token_wire[0]),.reset(reset),.in(req),.op(priority_op_wire[3:0]));

priority_logic M3 (.enable(token_wire[1]),.reset(reset),.in({req[0],req[3:1]}),.op(priority_op_wire[7:4]));

priority_logic M4 (.enable(token_wire[2]),.reset(reset),.in({req[1:0],req[3:2]}),.op(priority_op_wire[11:8]));

priority_logic M5 (.enable(token_wire[3]),.reset(reset),.in({req[2:0],req[3]}),.op(priority_op_wire[15:12]));

or M6 (grant[0],priority_op_wire[0],priority_op_wire[7],priority_op_wire[10],priority_op_wire[13]);

or M7 (grant[1],priority_op_wire[1],priority_op_wire[4],priority_op_wire[11],priority_op_wire[14]);

or M8 (grant[2],priority_op_wire[2],priority_op_wire[5],priority_op_wire[8],priority_op_wire[15]);

or M9 (grant[3],priority_op_wire[3],priority_op_wire[6],priority_op_wire[9],priority_op_wire[12]);

endmodule

/////////////////arbiter_dut----8////////////////////

module arbiter
(input clock,reset,ack,
 input [3:0] req,
 output [3:0] grant);
wire [15:0] priority_op_wire;
wire [3:0] token_wire;

ring_counter M1 (.clock(clock),.reset(reset),.enable(ack),.token(token_wire));

priority_logic M2 (.enable(token_wire[0]),.reset(reset),.in(req),.op(priority_op_wire[3:0]));

priority_logic M3 (.enable(token_wire[1]),.reset(reset),.in({req[0],req[3:1]}),.op(priority_op_wire[7:4]));

priority_logic M4 (.enable(token_wire[2]),.reset(reset),.in({req[1:0],req[3:2]}),.op(priority_op_wire[11:8]));

priority_logic M5 (.enable(token_wire[3]),.reset(reset),.in({req[2:0],req[3]}),.op(priority_op_wire[15:12]));

or M6 (grant[0],priority_op_wire[0],priority_op_wire[7],priority_op_wire[10],priority_op_wire[13]);

or M7 (grant[1],priority_op_wire[1],priority_op_wire[4],priority_op_wire[11],priority_op_wire[14]);

or M8 (grant[2],priority_op_wire[2],priority_op_wire[5],priority_op_wire[8],priority_op_wire[15]);

or M9 (grant[3],priority_op_wire[3],priority_op_wire[6],priority_op_wire[9],priority_op_wire[12]);

endmodule


///////////////arbiter_dummy_dut----9///////////////////////////

module arbiter_dummy
// PORT DECLARATION
(input clock,reset,ack,
 input[3:0] req,
 output [3:0] grant);

//WIRE DECLARATION
wire [3:0] y1,y2,y3,y4;
wire [3:0] en;

//MODULE INSTANTIATION FOR PRIORITY LOGIC
priority_logic_dummy p1(.a0(req[0]),.a1(req[1]),.a2(req[2]),.a3(req[3]),.en(en[0]),.reset(reset),.y(y1));
priority_logic_dummy p2(.a0(req[1]),.a1(req[2]),.a2(req[3]),.a3(req[0]),.en(en[1]),.reset(reset),.y(y2));
priority_logic_dummy p3(.a0(req[2]),.a1(req[3]),.a2(req[0]),.a3(req[1]),.en(en[2]),.reset(reset),.y(y3));
priority_logic_dummy p4(.a0(req[3]),.a1(req[0]),.a2(req[1]),.a3(req[2]),.en(en[3]),.reset(reset),.y(y4));

// MODULE INSTANTIATION FOR RING COUNTER
ring_counter_dummy c1(.clock(clock),.reset(reset),.en(ack),.q(en));

// ASSIGNING GRANT OUTPUT
assign grant[0]=y1[0]|y2[3]|y3[2]|y4[1];
assign grant[1]=y1[1]|y2[0]|y3[3]|y4[2];
assign grant[2]=y1[2]|y2[1]|y3[0]|y4[3];
assign grant[3]=y1[3]|y2[2]|y3[1]|y4[0];
endmodule



//////////////////interface----10///////////////

interface env_arbiter_interface (input bit clock,reset);
bit ack;
bit [3:0] req;
bit [3:0] grant;
endinterface

////////////////////Rinterface----11//////////

interface env_arbiter_rinterface (input bit clock,reset);
bit ack;
bit [3:0] req;
bit [3:0] grant;
endinterface

//////////////transaction---12///////////////

class env_arbiter_transaction;
rand bit ack;
rand bit [3:0] req;
bit [3:0] grant;
endclass

//////////////////generator----13//////////////

class env_arbiter_generator;
env_arbiter_transaction pkt;
mailbox #(env_arbiter_transaction)gen_drv;

function new (mailbox #(env_arbiter_transaction)gen_drv);
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

//////////////driver----14///////////////

class env_arbiter_driver;
env_arbiter_transaction pkt;
mailbox #(env_arbiter_transaction)gen_drv;
virtual env_arbiter_interface i;
virtual env_arbiter_rinterface ri;

function new (mailbox #(env_arbiter_transaction)gen_drv,virtual env_arbiter_interface i,virtual env_arbiter_rinterface ri);
this.gen_drv=gen_drv;
this.i=i;
this.ri=ri;
endfunction

task run;
gen_drv.get(pkt);
i.ack=pkt.ack;
i.req=pkt.req;
ri.ack=pkt.ack;
ri.req=pkt.req;
endtask
endclass

///////////////monitor----15////////////////

class env_arbiter_monitor;
env_arbiter_transaction pkt1,pkt2;
mailbox #(env_arbiter_transaction)mon_sb;
mailbox #(env_arbiter_transaction)mon_sb2;
virtual env_arbiter_interface i;
virtual env_arbiter_rinterface ri;

function new (mailbox #(env_arbiter_transaction)mon_sb,mailbox #(env_arbiter_transaction)mon_sb2,virtual env_arbiter_interface i,virtual env_arbiter_rinterface ri);
this.mon_sb=mon_sb;
this.mon_sb2=mon_sb2;
this.i=i;
this.ri=ri;
endfunction

task run;
pkt1=new();
pkt2=new();

pkt1.ack=i.ack;
pkt1.req=i.req;
pkt1.grant=i.grant;

pkt2.ack=ri.ack;
pkt2.req=ri.req;
pkt2.grant=ri.grant;

$display($time," pkt1.ack=%0b pkt1.req=%0b pkt1.grant=%0b",pkt1.ack,pkt1.req,pkt1.grant);
$display($time," pkt2.ack=%0b pkt2.req=%0b pkt2.grant=%0b",pkt2.ack,pkt2.req,pkt2.grant);

mon_sb.put(pkt1);
mon_sb2.put(pkt2);
endtask
endclass

//////////////////scoreboard---16////////////////////

class env_arbiter_scoreboard;
env_arbiter_transaction pkt1,pkt2;
mailbox #(env_arbiter_transaction)mon_sb;
mailbox #(env_arbiter_transaction)mon_sb2;

function new(mailbox #(env_arbiter_transaction)mon_sb,mailbox #(env_arbiter_transaction)mon_sb2);
this.mon_sb=mon_sb;
this.mon_sb2=mon_sb2;
endfunction

task run;
mon_sb.get(pkt1);
mon_sb2.get(pkt2);
assert(pkt1.grant==pkt2.grant)
begin
$display("Design is okay.");
end
else
begin
$display("Design is not okay.");
end
endtask
endclass

////////////////coverage----17///////////

class env_arbiter_coverage;
virtual env_arbiter_interface i;

covergroup cg @(posedge i.clock);
arbiter_req_CP: coverpoint i.req{ignore_bins req1 = {4'b0000};}
arbiter_grant_CP: coverpoint i.grant{bins grant1 = {4'b0000,4'b0001,4'b0010,4'b0100,4'b1000};}
arbiter_reset_ack_cross: cross i.reset,i.ack;
endgroup

function new (virtual env_arbiter_interface i);
this.i=i;
cg=new();
endfunction

task sample();
cg.sample();
endtask
endclass

///////////////////environment----18///////////////

class env_arbiter_environment;
mailbox #(env_arbiter_transaction)gen_drv;
mailbox #(env_arbiter_transaction)mon_sb;
mailbox #(env_arbiter_transaction)mon_sb2;
virtual env_arbiter_interface i;
virtual env_arbiter_rinterface ri;
env_arbiter_generator g1;
env_arbiter_driver d1;
env_arbiter_monitor m1;
env_arbiter_coverage c1;
env_arbiter_scoreboard s1;

function new (virtual env_arbiter_interface i,virtual env_arbiter_rinterface ri);
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

///////////////////////test----19///////////////////////

module env_arbiter_test(env_arbiter_interface i,env_arbiter_rinterface ri);
env_arbiter_environment en;

initial
begin
en=new(i,ri);
en.build();
repeat(500)
begin
#10 en.run();
end
end
endmodule

/////////////////arbiter_top----20/////////////////

module arbiter_top;
bit clock,reset;

//Clock generation
initial
begin 
clock = 1'b0;
forever
#5 clock = ~clock;
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

env_arbiter_interface i(clock,reset);
env_arbiter_rinterface ri(clock,reset);
env_arbiter_test T(i,ri);

//DUT Instantiation synthesizable 
arbiter DUT(.clock(clock),.reset(reset),.ack(i.ack),.req(i.req),.grant(i.grant));

//Dummy DUT simulatable code
arbiter_dummy DUMMY(.clock(clock),.reset(reset),.ack(ri.ack),.req(ri.req),.grant(ri.grant));
endmodule
