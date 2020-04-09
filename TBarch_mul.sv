//DUT

module mul8bit
(output reg [15:0]out,input [7:0] a,b);
reg [15:0]temp;
integer i;
always@(a,b)
begin
out=b[0]?{1'b0,a,7'b0}:15'd0;
for(i=1;i<8;i=i+1)
begin
if(b[i])
begin
temp=out>>1'b1;
out=temp+{1'b0,a,7'b0};
end
else
begin
temp=out>>1'b1;
out= temp;
end
end
end
endmodule

//packet

class packet;
rand bit [7:0]a,b;
bit [15:0]out;
endclass

//interface
interface intf();
bit [7:0]a,b;
bit [15:0]out;
endinterface

//generator

class generator;
packet pkt;
mailbox #(packet)gen_drv;
function new(mailbox #(packet)gen_drv);
this.gen_drv=gen_drv;
endfunction

task run();
pkt=new();
assert(pkt.randomize())
gen_drv.put(pkt);
else
$display("field");
endtask
endclass

//driver

class driver;
packet pkt;
mailbox #(packet)gen_drv;
mailbox #(packet)drv_sb;
virtual intf i;
function new(mailbox #(packet)gen_drv,mailbox #(packet)drv_sb,virtual intf i);
this.gen_drv=gen_drv;
this.drv_sb=drv_sb;
this.i=i;
endfunction

task run();
gen_drv.get(pkt);
drv_sb.put(pkt);
i.a=pkt.a;
i.b=pkt.b;
endtask
endclass

//monitor

class monitor;
packet pkt=new();
mailbox #(packet)mon_sb;
virtual intf i;
function new(mailbox #(packet)mon_sb,virtual intf i);
this.mon_sb=mon_sb;
this.i=i;
endfunction
task run();
pkt.a=i.a;
pkt.b=i.b;
pkt.out=i.out;
mon_sb.put(pkt);
endtask
endclass


//scoreboard

class scoreboard;
packet pkt1,pkt2;
mailbox #(packet)drv_sb;
mailbox #(packet)mon_sb;

function new(mailbox #(packet)drv_sb,mailbox #(packet)mon_sb);

this.drv_sb=drv_sb;
this.mon_sb=mon_sb;
endfunction
task run;
drv_sb.get(pkt1);
mon_sb.get(pkt2);

pkt1.out=pkt1.a*pkt1.b;

assert(pkt1.out==pkt2.out)
$display("pkt1:\t%d,%d,%d,pkt2:\t%d,%d,%d",pkt1.a,pkt1.b,pkt1.out,pkt2.a,pkt2.b,pkt2.out);
else
$display("miss");
endtask
endclass

class coverage;
virtual intf i;
covergroup cg @(i.a,i.b);
A: coverpoint i.a{bins a1 = {127};bins a2 = {255};bins a3 ={7'bx};}
B: coverpoint i.b{bins b1 = {32};bins b2 = {64};bins b3 ={255};}
O: coverpoint i.out{bins o1 = {65025};bins o2 = {256,65512};}
endgroup
function new (virtual intf i);
this.i = i ;
cg = new;
endfunction
task sample();
cg.sample();
endtask
endclass

//environment

class environment;
mailbox #(packet)gen_drv;
mailbox #(packet)drv_sb;
mailbox #(packet)mon_sb;

generator g1;
driver d1;
monitor m1;
coverage c1;
scoreboard s1;
virtual intf i;

function new(virtual intf i);
this.i=i;
endfunction

function void build();
gen_drv=new();
drv_sb=new();
mon_sb=new();
g1=new(gen_drv);
d1=new(gen_drv,drv_sb,i);
m1=new(mon_sb,i);
s1=new(drv_sb,mon_sb);
c1=new(i);
endfunction

task run();
g1.run();
d1.run();
c1.sample();
#1 m1.run();
s1.run();
endtask
endclass






//test

module test(intf i);
environment en;
initial
begin
en=new(i);
en.build();
repeat(50)
en.run();
end
endmodule


///top_testbench

module top_MUL();
intf i();
mul8bit m1(.a(i.a),.b(i.b),.out(i.out));
test t1(.i(i));
endmodule