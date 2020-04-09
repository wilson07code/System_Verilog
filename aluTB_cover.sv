//alu

module alu_nbit #(parameter n=4)
(input bit [n-1:0]a,b,
input bit [2:0]s,
output bit [n-1:0]sum,
output bit co);
parameter ADD=3'd0,
SUB=3'd1,
INR=3'd2,
DCR=3'd3,
AND=3'd4,
OR=3'd5,
XOR=3'd6;
always@(a,b,s)
begin
assert(^a!==1'bx)
else
$error("a is x");
assert(^b!==1'bx)
else
$error("b is x");
assert(^s!==1'bx)
else
$error("sel is x");
case(s)
ADD:{co,sum}=a+b;
SUB:{co,sum}=a-b;
INR:{co,sum}=a+1'b1;
DCR:{co,sum}=b-1'b1;
AND:{co,sum}={1'b0,a&b};
OR:{co,sum}={1'b0,a|b};
XOR:{co,sum}={1'b0,a^b};
default:{co,sum}={1'b0,~a};

endcase
end
endmodule

//// ?PACKET

class packet;
rand bit [3:0]a,b;
rand bit [2:0]s;
bit [3:0]sum;
bit co;
endclass

/// ?INTERFACE

interface intf;
bit [3:0]a,b,sum;
bit [2:0]s;
bit co;
modport drv(output a,b,s);
modport mon(input sum,co);
endinterface

//?GENERATOR

class generator;
packet pkt;
mailbox #(packet)gen_drv;
function new(mailbox #(packet)gen_drv);
this.gen_drv=gen_drv;
endfunction
task run;
pkt=new();
assert(pkt.randomize())
gen_drv.put(pkt);
else
$display("randomization failed");
endtask
endclass

///?DRIVER

class driver;
packet pkt;
mailbox #(packet)gen_drv;
mailbox #(packet)drv_sb;
virtual intf i;
function new(mailbox #(packet)gen_drv,mailbox
#(packet)drv_sb,virtual intf i);
this.gen_drv=gen_drv;
this.drv_sb=drv_sb;
this.i=i;
endfunction
task run;
gen_drv.get(pkt);
drv_sb.put(pkt);
i.a = pkt.a;
i.b = pkt.b;
i.s = pkt.s;
endtask
endclass

///MONITOR

class monitor;
packet pkt;
mailbox #(packet)mon_sb;
virtual intf i;
function new(mailbox #(packet)mon_sb,virtual intf i);
this.mon_sb=mon_sb;
this.i=i;
endfunction
task run;
pkt=new();
pkt.a=i.a;
pkt.b=i.b;
pkt.s=i.s;
pkt.sum=i.sum;
pkt.co=i.co;
mon_sb.put(pkt);
endtask
endclass

//  ?SCOREBOARD

class scoreboard;
packet pkt1,pkt2; //pkt1 from MONITOR and pkt2 from DRIVER
mailbox #(packet)drv_sb;
mailbox #(packet)mon_sb;
function new(mailbox #(packet)drv_sb,mailbox #(packet)mon_sb);
this.drv_sb=drv_sb;
this.mon_sb=mon_sb;
endfunction
task run;
mon_sb.get(pkt1);
drv_sb.get(pkt2);
case(pkt2.s)
3'd0:{pkt2.co,pkt2.sum}=pkt2.a-pkt2.b;
3'd1:{pkt2.co,pkt2.sum}=pkt2.a+pkt2.b;
3'd2:{pkt2.co,pkt2.sum}=pkt2.a+1'b1;
3'd3:{pkt2.co,pkt2.sum}=pkt2.b-1'b1;
3'd4:{pkt2.co,pkt2.sum}={1'b0,pkt2.a&pkt2.b};
3'd5:{pkt2.co,pkt2.sum}={1'b0,pkt2.a|pkt2.b};
3'd6:{pkt2.co,pkt2.sum}={1'b0,pkt2.a^pkt2.b};
default:{pkt2.co,pkt2.sum}={1'b0,~pkt2.a};
endcase
if(pkt1.co==pkt2.co && pkt1.sum==pkt2.sum)
begin
$display(" design is ok");
$display($time,"\t SCOREBOARD: a=%b b=%b s=%b sum=%d co=%b",pkt1.a,pkt1.b,pkt1.s,pkt1.sum,pkt1.co);
$display($time,"\t DUT: a=%b b=%b s=%b sum=%d co=%b",pkt2.a,pkt2.b,pkt2.s,pkt2.sum,pkt2.co);
end
else begin
$display(" design is not ok");
$display($time, "a=%b b=%b s=%b sum=%d co=%b",pkt1.a,pkt1.b,pkt1.s,pkt1.sum,pkt1.co); end
endtask
endclass

//COVERAGE? ?CLASS

class coverage;
virtual intf i;
covergroup cg @(i.a,i.b,i.s);
A: coverpoint i.a{illegal_bins a_bin = {[5:7]};}
B: coverpoint i.b{bins b_bin = {[8:13]};}
S: coverpoint i.s{ignore_bins s1 = {0,1};bins s2 = {3'bxxx};}
SUM: coverpoint i.sum{bins sm1 = {4'dx};}
COUT: coverpoint i.co{bins co1 = {1'bx};}
endgroup
function new (virtual intf i);
this.i = i ;
cg = new;
endfunction
task sample();
cg.sample();
endtask
endclass

///ENVIRONMENT

class environment;
mailbox #(packet)gen_drv;
mailbox #(packet)drv_sb;
mailbox #(packet)mon_sb;
virtual intf i;
generator g1;
driver d1;
coverage c1;
monitor m1;
scoreboard s1;
function new(virtual intf i);
this.i=i;
endfunction
function void build;
gen_drv=new();
drv_sb=new();
mon_sb=new();
g1=new(gen_drv);
d1=new(gen_drv,drv_sb,i);
c1=new(i);
m1=new(mon_sb,i);
s1=new(drv_sb,mon_sb);
endfunction
task run;
g1.run();
d1.run();
c1.sample();
#1 m1.run();
s1.run();
endtask
endclass
//?TEST

program env_alu_test(intf i);
environment en;
initial
begin
en=new(i);
en.build();
repeat(100)
begin
en.run();
end
end
endprogram

module alu_top;
intf i();
alu_nbit aa(.a(i.a),.b(i.b),.s(i.s),.sum(i.sum),.co(i.co));
env_alu_test t(i);
endmodule