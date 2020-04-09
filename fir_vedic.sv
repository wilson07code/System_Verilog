//dut
module fir_4tap_using_4x4_vedic_multiplier(input clk,rst,input
[3:0]xn,output [9:0]yn);
wire [8:0]a10,a20,a30;
wire [7:0]m10,m20,m30,m40;
wire [3:0]d10,d20,d30,d40;
parameter h0=4'b0101,
h1=4'b0100,
h2=4'b0011,
h3=4'b0010;//[5,4,3,2]
assign d10 =xn;
vedic_4x4 M1(.clk(clk),.rst(rst),.a(d10),.b(h0),.c(m10));
dff ff1(.clk(clk),.rst(rst),.d(d10),.q(d20));
vedic_4x4 M2(.clk(clk),.rst(rst),.a(d20),.b(h1),.c(m20));
assign a10=m10+m20;
dff ff2(.clk(clk),.rst(rst),.d(d20),.q(d30));
vedic_4x4 M3(.clk(clk),.rst(rst),.a(d30),.b(h2),.c(m30));
assign a20=a10+m30;
dff ff3(.clk(clk),.rst(rst),.d(d30),.q(d40));
vedic_4x4 M4(.clk(clk),.rst(rst),.a(d40),.b(h3),.c(m40));
assign a30=a20+m40;
assign yn=a30;
endmodule
//child module d-flipflop
module dff(input clk,rst,input [3:0]d,output reg[3:0]q);
always@(posedge clk)
begin
if(rst)
q<=4'b0;
else
q<=d;
end
endmodule

//------------------------------------------------------------------
//Vedic 4x4 multiplier used in 4tap FIR filter
//------------------------------------------------------------------
////// vedic 4x4 multiplier using vedic 2x2 multiplier
module vedic_4x4(clk,rst,a,b,c);
input clk,rst;
input [3:0]a;
input [3:0]b;
output [7:0]c;
wire [3:0]q0;
wire [3:0]q1;
wire [3:0]q2;
wire [3:0]q3;
wire [7:0]c;
wire [3:0]temp1;
wire [5:0]temp2;
wire [5:0]temp3;
wire [5:0]temp4;
wire [3:0]q4;
wire [5:0]q5;
wire [5:0]q6;
// using 4 2x2 multipliers
vedic_2x2 z1(a[1:0],b[1:0],q0[3:0]);
vedic_2x2 z2(a[3:2],b[1:0],q1[3:0]);
vedic_2x2 z3(a[1:0],b[3:2],q2[3:0]);
vedic_2x2 z4(a[3:2],b[3:2],q3[3:0]);
// stage 1 adders
assign temp1 ={2'b0,q0[3:2]};
add_4_bit z5(q1[3:0],temp1,q4);
assign temp2 ={2'b0,q2[3:0]};
assign temp3 ={q3[3:0],2'b0};
add_6_bit z6(temp2,temp3,q5);
assign temp4={2'b0,q4[3:0]};
// stage 2 adder
add_6_bit z7(temp4,q5,q6);
// fnal output assignment
assign c[1:0]=q0[1:0];
assign c[7:2]=q6[5:0];
endmodule
////////////////////////////////////
module vedic_2x2(a,b,c );
input [1:0]a;
input [1:0]b;
output [3:0]c;
wire [3:0]c;
wire [3:0]temp;
//stage 1
// four multiplication operation of bits according to vedic logic
//done using and gates
assign c[0]=a[0]&b[0];
assign temp[0]=a[1]&b[0];
assign temp[1]=a[0]&b[1];

assign temp[2]=a[1]&b[1];
//stage two
// using two half adders
ha z1(temp[0],temp[1],c[1],temp[3]);
ha z2(temp[2],temp[3],c[2],c[3]);
endmodule
//////////////////////
module ha(input a,b,output s,c);
assign s=a^b;
assign c=a&b;
endmodule
////////////////////////////////////////
module fa(input a,b,ci,output s,co );
assign s=a^b^ci;
assign co=(a&b)|ci&(a^b);
endmodule
///////////////////////
module add_4_bit(input [3:0]a,b,output [3:0]s);
wire [3:0]c;
ha n1(a[0],b[0],s[0],c[0]);
fa n2(a[1],b[1],c[0],s[1],c[1]);
fa n3(a[2],b[2],c[1],s[2],c[2]);
fa n4(a[3],b[3],c[2],s[3],c[3]);
endmodule
////////////////////////////////
module add_6_bit(input [5:0]a,b,output [5:0]s);
wire [5:0]c;
ha n1(a[0],b[0],s[0],c[0]);
fa n2(a[1],b[1],c[0],s[1],c[1]);
fa n3(a[2],b[2],c[1],s[2],c[2]);
fa n4(a[3],b[3],c[2],s[3],c[3]);
fa n5(a[4],b[4],c[3],s[4],c[4]);
fa n6(a[5],b[5],c[4],s[5],c[5]);
endmodule





//packet
class packet;
rand bit [3:0] xn;
bit [9:0] yn;
endclass



//interface_1
interface intf1 (input bit clk,rst);
bit [3:0] xn;
bit [9:0] yn;
endinterface



// interface_2
interface intf2 (input bit clk,rst);
bit [3:0] xn;
bit [9:0] yn;
endinterface




//generator
class generator;
packet pkt;
mailbox #(packet)gen_drv;

function new (mailbox #(packet)gen_drv);
this.gen_drv=gen_drv;
endfunction

task run;
pkt=new();
assert(pkt.randomize())
begin
$display("DONE");
gen_drv.put(pkt);
end
else 
$display("FAILED");
endtask
endclass




//driver
class driver;
packet pkt;
mailbox #(packet)gen_drv;
virtual intf1 i;
virtual intf2 j;

function new (mailbox #(packet)gen_drv,virtual intf1 i,virtual intf2 j);
this.gen_drv=gen_drv;
this.i=i;
this.j=j;
endfunction

task run;
gen_drv.get(pkt);
i.xn=pkt.xn;
j.xn=pkt.xn;
endtask
endclass



//monitor
class monitor;
packet pkt1,pkt2;
mailbox #(packet)mon_sb;
mailbox #(packet)mon_sb2;
virtual intf1 i;
virtual intf2 j;

function new (mailbox #(packet)mon_sb,mailbox #(packet)mon_sb2,virtual intf1 i,virtual intf2 j);
this.mon_sb=mon_sb;
this.mon_sb2=mon_sb2;
this.i=i;
this.j=j;
endfunction

task run;
pkt1=new();
pkt2=new();

pkt1.xn=i.xn;
pkt1.yn=i.yn;

pkt2.xn=j.xn;
pkt2.yn=j.yn;

$display($time," pkt1.xn=%0b pkt1.yn=%0b",pkt1.xn,pkt1.yn);
$display($time," pkt2.xn=%0b pkt2.yn=%0b",pkt2.xn,pkt2.yn);

mon_sb.put(pkt1);
mon_sb2.put(pkt2);
endtask
endclass



//scoreboard
class scoreboard;
packet pkt1,pkt2;
mailbox #(packet)mon_sb;
mailbox #(packet)mon_sb2;

function new(mailbox #(packet)mon_sb,mailbox #(packet)mon_sb2);
this.mon_sb=mon_sb;
this.mon_sb2=mon_sb2;
endfunction

task run;
mon_sb.get(pkt1);
mon_sb2.get(pkt2);
assert(pkt1.yn==pkt2.yn)
begin
$display("HIT");
end
else
begin
$display("MISS");
end
endtask
endclass


//coverage
class coverage;
virtual intf1 i;

covergroup cg @(posedge i.clk);
A: coverpoint i.xn;
C: coverpoint i.yn{bins yn1 = {[0:255]}; }
endgroup

function new (virtual intf1 i);
this.i=i;
cg=new();
endfunction

task sample();
cg.sample();
endtask
endclass

//coverage_2
class coverage2;
virtual intf2 j;

covergroup cg2 @(posedge j.clk);
B: coverpoint j.xn;
D: coverpoint j.yn{bins yn2 = {[0:255]}; }
endgroup

function new (virtual intf2 j);
this.j=j;
cg2=new();
endfunction

task sample();
cg2.sample();
endtask
endclass



//environment
class environment;
mailbox #(packet)gen_drv;
mailbox #(packet)mon_sb;
mailbox #(packet)mon_sb2;
virtual intf1 i;
virtual intf2 j;
generator g1;
driver d1;
monitor m1;
coverage c1;
coverage2 c2;
scoreboard s1;

function new (virtual intf1 i,virtual intf2 j);
this.i=i;
this.j=j;
endfunction

function void build;
gen_drv=new();
mon_sb=new();
mon_sb2=new();
g1=new(gen_drv);
d1=new(gen_drv,i,j);
m1=new(mon_sb,mon_sb2,i,j);
s1=new(mon_sb,mon_sb2);
c1=new(i);
c2=new(j);
endfunction

task run;
fork
g1.run();
d1.run();
c1.sample();
c2.sample();
m1.run();
s1.run();
join
endtask
endclass



//test
module test(intf1 i,intf2 j);
environment en;

initial
begin
en=new(i,j);
en.build();
repeat(20000)
#10 en.run();
end
endmodule



//top
module top_VM_arch2;
bit clk,rst;

//Clock generation
initial
begin 
clk = 1'b0;
forever
#5 clk = ~clk;
end

//Reset generation
initial 
begin
rst=1'b1;
#10;
rst=1'b0;
#50;
rst=1'b1;
#10;
rst=1'b0;
end

intf1 i(clk,rst);
intf2 j(clk,rst);
test T(i,j);

 
fir_4tap_using_4x4_vedic_multiplier fir1 (.clk(clk),.rst(rst),.xn(i.xn),.yn(i.yn));
fir_4tap_using_4x4_vedic_multiplier fir2 (.clk(clk),.rst(rst),.xn(j.xn),.yn(j.yn));
endmodule