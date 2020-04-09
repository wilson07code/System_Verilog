//dut
module wallace_tree(
input [7:0] a,b,
output [15:0] pro);
wire [53:1]s,c;
wire [7:0] p0,p1,p2,p3,p4,p5,p6,p7;
assign p0= a&{8{b[0]}};
assign p1= a&{8{b[1]}};
assign p2= a&{8{b[2]}};
assign p3= a&{8{b[3]}};
assign p4= a&{8{b[4]}};
assign p5= a&{8{b[5]}};
assign p6= a&{8{b[6]}};
assign p7= a&{8{b[7]}};
half_adder h1(p0[1],p1[0],s[1],c[1]);
full_adder f1(p0[2],p1[1],p2[0],s[2],c[2]);
full_adder f2(p0[3],p1[2],p2[1],s[3],c[3]);
full_adder f3(p0[4],p1[3],p2[2],s[4],c[4]);
full_adder f4(p0[5],p1[4],p2[3],s[5],c[5]);
full_adder f5(p0[6],p1[5],p2[4],s[6],c[6]);
full_adder f6(p0[7],p1[6],p2[5],s[7],c[7]);
half_adder h2(p1[7],p2[6],s[8],c[8]);
full_adder f7(p2[7],p3[6],p4[5],s[9],c[9]);
half_adder h3(p3[1],p4[0],s[10],c[10]);
full_adder f8(p3[2],p4[1],p5[0],s[11],c[11]);
full_adder f9(p3[3],p4[2],p5[1],s[12],c[12]);
full_adder f10(p3[4],p4[3],p5[2],s[13],c[13]);
full_adder f11(p3[5],p4[4],p5[3],s[14],c[14]);
full_adder f12(p3[7],p4[6],p5[5],s[15],c[15]);
half_adder h4(p4[7],p5[6],s[16],c[16]);
half_adder h5(s[2],c[1],s[17],c[17]);
full_adder f13(s[3],c[2],p3[0],s[18],c[18]);
full_adder f14(s[4],c[3],s[10],s[19],c[19]);
full_adder f15(s[5],c[4],s[11],s[20],c[20]);
full_adder f16(s[6],c[5],s[12],s[21],c[21]);
full_adder f17(s[7],c[6],s[13],s[22],c[22]);
full_adder f18(s[8],c[7],s[14],s[23],c[23]);
full_adder f19(s[9],c[8],c[14],s[24],c[24]);
half_adder h6(c[11],p6[0],s[25],c[25]);
full_adder f20(c[12],p6[1],p7[0],s[26],c[26]);
full_adder f21(c[13],p6[2],p7[1],s[27],c[27]);
full_adder f22(p5[4],p6[3],p7[2],s[28],c[28]);
full_adder f23(c[9],p6[4],p7[3],s[29],c[29]);
full_adder f24(c[15],p6[5],p7[4],s[30],c[30]);
full_adder f25(p5[7],p6[6],p7[5],s[31],c[31]);
half_adder h7(p6[7],p7[6],s[32],c[32]);
half_adder h8(s[18],c[17],s[33],c[33]);
half_adder h9(s[19],c[18],s[34],c[34]);
full_adder f26(s[20],c[19],c[10],s[35],c[35]);
full_adder f27(s[21],c[20],s[25],s[36],c[36]);

full_adder f28(s[22],c[21],s[26],s[37],c[37]);
full_adder f29(s[23],c[22],s[27],s[38],c[38]);
full_adder f30(s[24],c[23],s[28],s[39],c[39]);
full_adder f31(s[15],c[24],s[29],s[40],c[40]);
half_adder h10(s[16],s[30],s[41],c[41]);
half_adder h11(c[16],s[31],s[42],c[42]);
half_adder h12(s[34],c[33],s[43],c[43]);
half_adder h13(s[35],c[34],s[44],c[44]);
half_adder h14(s[36],c[35],s[45],c[45]);
full_adder f32(s[37],c[36],c[25],s[46],c[46]);
full_adder f33(s[38],c[37],c[26],s[47],c[47]);
full_adder f34(s[39],c[38],c[27],s[48],c[48]);
full_adder f35(s[40],c[39],c[28],s[49],c[49]);
full_adder f36(s[41],c[40],c[29],s[50],c[50]);
full_adder f37(s[42],c[30],c[41],s[51],c[51]);
full_adder f38(c[42],s[32],c[31],s[52],c[52]);
half_adder h15(p7[7],c[32],s[53],c[53]);
assign pro[0]=p0[0];
assign pro[1]=s[1];
assign pro[2]=s[17];
assign pro[3]=s[33];
assign pro[4]=s[43];
assign pro[5]=s[44]+c[43];
assign pro[6]=s[45]+c[44];
assign pro[7]=s[46]+c[45];
assign pro[8]=s[47]+c[46];
assign pro[9]=s[48]+c[47];
assign pro[10]=s[49]+c[48];
assign pro[11]=s[50]+c[49];
assign pro[12]=s[51]+c[50];
assign pro[13]=s[52]+c[51];
assign pro[14]=s[53]+c[52];
assign pro[15]=c[53];
endmodule

module half_adder(
input a,b,output s,c);
assign {c,s}=a+b;
endmodule

module full_adder(
input a,b,cin ,output s,c);
assign {c,s}=a+b+cin;
endmodule




//packet
class packet;
rand bit [7:0]a,b;
bit [15:0]pro;
endclass


//interface
interface intf;
bit [7:0]a,b;
bit [15:0]pro;
endinterface



//generator
class generator;
packet pkt=new();
mailbox #(packet)gen_drv;
function new (mailbox #(packet)gen_drv);
this.gen_drv=gen_drv;
endfunction
task run();
//pkt=new();
assert(pkt.randomize())
gen_drv.put(pkt);
else
$display("failed");
endtask
endclass


//driver
class driver;
packet pkt;
mailbox #(packet)gen_drv;
mailbox #(packet)drv_sb;
virtual intf i;
function new (mailbox #(packet)gen_drv,mailbox #(packet)drv_sb,virtual intf i);
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
function new (mailbox #(packet)mon_sb,virtual intf i);
this.mon_sb=mon_sb;
this.i=i;
endfunction
task run();
pkt.a=i.a;
pkt.b=i.b;
pkt.pro=i.pro;
mon_sb.put(pkt);
endtask
endclass


//coverage
class coverage;
virtual intf i;
covergroup cg @ (i.a,i.b);
A: coverpoint i.a {bins a_bin ={[5:7]};}
B: coverpoint i.b {bins b_bin ={[8:13]};}
PRO: coverpoint i.pro {bins pro_bin ={[0:65535]};}
endgroup
function new (virtual intf i);
this.i=i;
cg =new;
endfunction
task sample();
cg.sample();
endtask
endclass



//scoreboard
class scoreboard;
packet pkt1,pkt2;
mailbox #(packet)drv_sb;
mailbox #(packet)mon_sb;
function new (mailbox #(packet)drv_sb,mailbox #(packet)mon_sb);
this.drv_sb=drv_sb;
this.mon_sb=mon_sb;
endfunction
task run();
drv_sb.get(pkt1);
mon_sb.get(pkt2);
{pkt1.pro}=pkt1.a*pkt1.b;   //dummy
	if(pkt1.pro==pkt2.pro)
		$display("a=%d b=%d pro=%d",pkt1.a,pkt1.b,pkt1.pro);
	else
		$display("miss");
endtask
endclass


//environment
class environment;
mailbox #(packet)gen_drv;
mailbox #(packet)drv_sb;
mailbox #(packet)mon_sb;
generator g1;
coverage c1;
driver d1;
monitor m1;
scoreboard s1;
virtual intf i;
function new (virtual intf i);
this.i=i;
endfunction
function void build ();
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
c1.sample();
d1.run();
#1 m1.run();
s1.run();
endtask
endclass


//test
module test(intf i);
environment en;
initial begin
en=new(i);
en.build();
repeat(500)
en.run();
end
endmodule


//top
module top_wallace_arch();
intf i();
wallace_tree w1 (.a(i.a),.b(i.b),.pro(i.pro));
test t1 (.i(i));
endmodule
