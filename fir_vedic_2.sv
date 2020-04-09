module vedic_4bit_mult(
input [3:0]a,b,
output [7:0]s );
wire [15:0]x;
wire [3:0]y1,y2;
wire c1,c2,c3;
wire [3:0]z1,z2;

vedic_mult_2x2 l1(.a(a[1:0]),.b(b[1:0]),.s(x[3:0]));
vedic_mult_2x2 l2(.a(a[1:0]),.b(b[3:2]),.s(x[7:4]));
vedic_mult_2x2 l3(.a(a[3:2]),.b(b[1:0]),.s(x[11:8]));
vedic_mult_2x2 l4(.a(a[3:2]),.b(b[3:2]),.s(x[15:12]));
ripple_carrier_adder l5(.a(x[7:4]),.b(x[11:8]),.cin(1'b0),.s(y1[3:0]),.cout(c1));
assign z1={2'b00,x[3:2]};
ripple_carrier_adder l6(.a(y1[3:0]),.b(z1),.cin(1'b0),.s(y2[3:0]),.cout(c2));
assign z2={c2,c1,y2[3:2]};
ripple_carrier_adder l7(.a(x[15:12]),.b(z2),.cin(1'b0),.s(s[7:4]),.cout(c3));
assign s[1:0]=x[1:0];
assign s[3:2]=y2[1:0];
 endmodule

//------------------------------------------- vedic_mult_2x2-----------------------------------------------------
module vedic_mult_2x2(
input [1:0]a,b,
output [3:0]s);
wire c,w1,w2,w3;
assign s[0]=a[0]&b[0];
assign w1=a[0]&b[1];
assign w2=a[1]&b[0];
assign w3=a[1]&b[1];

half_adder f1(.a(w1),.b(w2),.s(s[1]),.cout(c));
half_adder f2(.a(w3),.b(c),.s(s[2]),.cout(s[3]));
endmodule

//-------------------------------------------------HALF_ADDDER---------------------------------------------------
module half_adder(
input a,b,
output s,cout   );
assign s=a^b;
assign cout=a&b;
endmodule

//--------------------------------------------------------- ripple_carrier_adder-------------------------------------
module ripple_carrier_adder(
input [3:0]a,b,
input cin,
output [3:0]s,
output cout    );

wire w1,w2,w3;

fulladder l1(.a(a[0]),.b(b[0]),.cin(cin),.s(s[0]),.cout(w1));
fulladder l2(.a(a[1]),.b(b[1]),.cin(w1),.s(s[1]),.cout(w2));
fulladder l3(.a(a[2]),.b(b[2]),.cin(w2),.s(s[2]),.cout(w3));
fulladder l4(.a(a[3]),.b(b[3]),.cin(w3),.s(s[3]),.cout(cout));

endmodule
//---------------------------------------------full adder----------------------------------------
module fulladder(
input a,b,cin,
output s,cout );

assign s=a^b^cin;
assign cout=(a&b)|(b&cin)|(cin&a);


endmodule



//--------------------------packet-----------
class packet;
rand bit [3:0]a,b;
bit [7:0]s;
endclass

//-------interface_1----
interface intf1;

bit [3:0]a,b;
bit [7:0]s;
endinterface

//------interface_2-----
interface intf2;
bit [3:0]a,b;
bit [7:0]s;
endinterface

//------generator-----

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

//-----------driver-----

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
i.a=pkt.a;
i.b=pkt.b;
j.a=pkt.a;
j.b=pkt.b;
endtask
endclass

//--------------monitor---------

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

pkt1.a=i.a;
pkt1.b=i.b;
pkt1.s=i.s;

pkt2.a=j.a;
pkt2.b=j.b;
pkt2.s=j.s;

$display($time," pkt1.a=%0b pkt1.b=%0b pkt1.s=%0b",pkt1.a,pkt1.b,pkt1.s);
$display($time," pkt2.a=%0b pkt2.b=%0b pkt2.s=%0b",pkt2.a,pkt2.b,pkt2.s);

mon_sb.put(pkt1);
mon_sb2.put(pkt2);
endtask
endclass

//-----------------scoreboard----------

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
assert(pkt1.s==pkt2.s)
begin
$display("HIT");
end
else
begin
$display("MISS");
end
endtask
endclass

//---------------coverage-----------

class coverage;
virtual intf1 i;

covergroup cg;
A: coverpoint i.a;
B: coverpoint i.b{bins b1 = {[0:255]}; }
S: coverpoint i.s;
endgroup

function new (virtual intf1 i);
this.i=i;
cg=new();
endfunction

task sample();
cg.sample();
endtask
endclass

//-----coverage_2------------

//class coverage2;
//virtual intf2 j;
//
//covergroup cg2;
//B: coverpoint j.a;
//D: coverpoint j.b{bins b2 = {[0:255]}; }
//S1: coverpoint j.s;
//endgroup
//
//function new (virtual intf2 j);
//this.j=j;
//cg2=new();
//endfunction
//
//task sample();
//cg2.sample();
//endtask
//endclass

//------------environment---------

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
//coverage c2;
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
//c2=new(j);
endfunction

task run;
fork
g1.run();
d1.run();
c1.sample();
//c2.sample();
m1.run();
s1.run();
join
endtask
endclass

//--------------------test--------------

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

///-----------------top-----------

module top_fir_2arch;
bit [3:0]a,b;
bit [7:0]s;

intf1 i();
intf2 j();
test t1(i,j);

vedic_4bit_mult fir1 (.a(i.a),.b(i.b),.s(i.s));
vedic_4bit_mult fir2 (.a(j.a),.b(j.b),.s(j.s));
endmodule