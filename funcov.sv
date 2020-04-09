// Adder 
module env_adder(input [2:0]a,b,output reg [2:0]s,output reg c); 
always@(a,b) 
begin 
$display("inside DUT"); 
{c,s}=a+b; 
end 
endmodule 

//Packet 
class packet; 
rand bit [2:0]a,b; 
bit [2:0]s; bit c; 
endclass 

//Interface 
interface intf; 
bit [2:0]a,b;
 bit [2:0]s;bit c; 
modport drv(output a,b); 
modport mon(input s,c); 
endinterface 

//Generator 
class generator; 
packet pkt; 
mailbox #(packet)gen_drv; 
function new(mailbox #(packet)gen_drv); 
this.gen_drv=gen_drv; 
endfunction 
task run; 
pkt=new(); 
assert(pkt.randomize()) 
begin 
gen_drv.put(pkt); 
end 
else 
$display("randomization failed"); 
endtask 
endclass 

//Driver
 
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
task run; 
gen_drv.get(pkt); 
drv_sb.put(pkt); 
i.a =pkt.a; 
i.b=pkt.b; 
endtask 
endclass 
// Monitor

 
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
pkt.c=i.c; 
mon_sb.put(pkt); 
endtask 
endclass 

//Scoreboard 

class scoreboard; 
packet pkt1,pkt2; 
mailbox #(packet)drv_sb; 
mailbox #(packet)mon_sb; 
function new(mailbox #(packet)drv_sb,mailbox #(packet)mon_sb); 
this.drv_sb=drv_sb; 
this.mon_sb=mon_sb; 
endfunction 
task run; 
mon_sb.get(pkt1); 
drv_sb.get(pkt2); 
{pkt2.c,pkt2.s}=pkt2.a+pkt2.b; 
assert(pkt1.c==pkt2.c && pkt1.s==pkt2.s) 
begin 
$display(" design is ok"); 
$display($time,"a=%b b=%b s=%b c=%b",pkt1.a,pkt1.b,pkt1.s,pkt1.c); 
end 
else 
begin 
$display(" design is not ok"); 
$display($time,"a=%b b=%b s=%b c=%b",pkt1.a,pkt1.b,pkt1.s,pkt1.c); 
end 
endtask 
endclass 

//Coverage Class 

class coverage; 
virtual intf i; 
covergroup cg @(i.a,i.b); 
A: coverpoint i.a{bins a_bin = {[5:7]};} 
B: coverpoint i.b; 
S: coverpoint i.s{bins s1 = {0,1};bins s2 = {2,3};} 
D: coverpoint i.c; 
endgroup 
function new (virtual intf i); 
this.i = i ; 
cg = new; 
endfunction 
task sample(); 
cg.sample(); 
endtask 
endclass 

//Environment
 
class environment; 
mailbox #(packet)gen_drv; 
mailbox #(packet)drv_sb; 
mailbox #(packet)mon_sb; 
virtual intf i; 
generator g1; 
coverage c1; 
driver d1; 
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
m1=new(mon_sb,i); 
s1=new(drv_sb,mon_sb); 
c1=new(i); 
endfunction 
task run; 
g1.run(); 
d1.run(); 
c1.sample(); 
#1 m1.run(); 
s1.run(); 
endtask 
endclass 

//Test 

program env_adder_test(intf i); 
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



module env_adder_top; 
intf i(); 
env_adder aa(.a(i.a),.b(i.b),.c(i.c),.s(i.s)); 
env_adder_test t(i); 
endmodule 
