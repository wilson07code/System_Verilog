///Fetch_dut

module fetch
(input clk,rst,enable_updatepc,enable_fetch,br_taken,
 input [15:0]taddr,
 output reg [15:0]pc,npc,
 output reg instrmem_rd);

assign npc=pc+1;
assign instrmem_rd=enable_fetch?1'b1:1'bz;

always @(posedge clk)
  begin
    if(rst)
	  pc<=16'h3000;
    else
	begin
            pc<=pc;
	   if(enable_updatepc)
		begin
		   pc<=br_taken?taddr:npc;
		end
	end
  end

endmodule

///DEbug_Fetch

module fetch_debug(clock, reset, enable_updatePC, enable_fetch, pc,npc_out,instrmem_rd, taddr, br_taken);
input enable_updatePC,clock, reset, br_taken, enable_fetch;
input [15:0] taddr;
output reg [15:0] pc, npc_out;
output reg instrmem_rd;

reg [15:0]ipc;
wire [15:0]muxout;
wire [15:0] npc_int;

always @(posedge clock)
begin
/*assert (enable_updatePC==0)
$info("-----FETCH------enable_updatePC = %b enable_fetch = %b pc=%h",enable_updatePC,enable_fetch,pc);
else $error("enable_updatePC = %b enable_fetch = %b pc=%h",enable_updatePC,enable_fetch,pc);*/

if(reset==1)
  begin
	ipc<=16'h3000;
	//ipc<=16'h3002;
	//ipc<=16'h3005;
  end
else
    begin
       if(enable_updatePC)
         ipc <= muxout;
       else
         ipc <= ipc;
   end
end

assign muxout=(br_taken)?taddr: npc_int;

assign npc_int=ipc+1;
//assign npc_int=ipc+ 2 + ipc;;
//npc = ipc +1 ;
assign npc_out = npc_int;
//assign npc_out = npc_int+2;
//npc_out = npc_int;

assign pc = ipc;

assign instrmem_rd = (enable_fetch)?1'b1: 1'bz;
//assign instrmem_rd = (enable_fetch)?1'b0: 1'b0;
endmodule

	  
///packet

class packet;
rand bit enable_updatepc,enable_fetch,br_taken;
rand bit [15:0]taddr;
bit [15:0]pc,npc;
bit instrmem_rd;
endclass

///interface

interface intf(input bit clk,rst);
bit enable_updatepc,enable_fetch,br_taken;
bit [15:0]taddr;
bit [15:0]pc,npc;
bit instrmem_rd;

modport drv(output enable_updatepc,enable_fetch,br_taken);
modport mon(input pc,npc,instrmem_rd);
endinterface

//r_interface

interface rintf(input bit clk,rst);
bit enable_updatepc,enable_fetch,br_taken;
bit [15:0]taddr;
bit [15:0]pc,npc;
bit instrmem_rd;

modport drv(output enable_updatepc,enable_fetch,br_taken);
modport mon(input pc,npc,instrmem_rd);
endinterface

//generator

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
else $display("randomization failed");
endtask
endclass

//driver

class driver;
packet pkt;
mailbox #(packet)gen_drv;
//mailbox #(packet)drv_sb;
virtual intf i;
virtual intf ri;

function new(mailbox #(packet)gen_drv,virtual intf i,virtual intf ri);
this.gen_drv=gen_drv;
//this.drv_sb=drv_sb;
this.ri=ri;
this.i=i;
endfunction

task run;
gen_drv.get(pkt);
//drv_sb.put(pkt);
i.enable_updatepc =pkt.enable_updatepc;
i.enable_fetch=pkt.enable_fetch;
i.br_taken=pkt.br_taken;
i.taddr=pkt.taddr;

ri.enable_updatepc =pkt.enable_updatepc;
ri.enable_fetch=pkt.enable_fetch;
ri.br_taken=pkt.br_taken;
ri.taddr=pkt.taddr;

endtask
endclass


//monitor

class monitor;
packet pkt1,pkt2;
mailbox #(packet)mon_sb1;
mailbox #(packet)mon_sb2;
virtual intf i;
virtual intf ri;
function new(mailbox #(packet)mon_sb1,mailbox #(packet)mon_sb2,virtual intf i,virtual intf ri);
this.mon_sb1=mon_sb1;
this.mon_sb2=mon_sb2;
this.i=i;
this.ri=ri;
endfunction

task run;
pkt1=new();
pkt2=new();
pkt1.enable_updatepc=i.enable_updatepc;
pkt1.enable_fetch=i.enable_fetch;
pkt1.br_taken=i.br_taken;
pkt1.taddr=i.taddr;
pkt1.npc=i.npc;
pkt1.pc=i.pc;
pkt1.instrmem_rd=i.instrmem_rd;

pkt2.enable_updatepc=ri.enable_updatepc;
pkt2.enable_fetch=ri.enable_fetch;
pkt2.br_taken=ri.br_taken;
pkt2.taddr=ri.taddr;
pkt2.npc=ri.npc;
pkt2.pc=ri.pc;
pkt2.instrmem_rd=ri.instrmem_rd;


mon_sb1.put(pkt1);
mon_sb2.put(pkt2);
endtask
endclass

//scoreboard

class scoreboard;
packet pkt1,pkt2;
mailbox #(packet)mon_sb1;
mailbox #(packet)mon_sb2;

function new(mailbox #(packet)mon_sb1,mailbox #(packet)mon_sb2);
this.mon_sb1=mon_sb1;
this.mon_sb2=mon_sb2;
endfunction

task run;
mon_sb1.get(pkt1);
mon_sb2.get(pkt2);


assert(pkt1.npc==pkt2.npc && pkt1.pc==pkt2.pc && pkt1.instrmem_rd==pkt2.instrmem_rd)
begin
$display(" design is ok");
$display($time,"enable_updatepc=%b enable_fetch=%d br_taken=%d pc=%d npc=%d instrmem_rd=%b",pkt1.enable_updatepc,pkt1.enable_fetch,pkt1.br_taken,pkt1.pc,pkt1.npc,pkt1.instrmem_rd);
end
else
begin
$display(" design is not ok");
$display($time,"pc=%d npc=%d instrmem_rd=%b",pkt1.pc,pkt1.npc,pkt1.instrmem_rd);
end
endtask
endclass

//coverage

class coverage;
virtual intf i;

covergroup cg @(posedge i.clk);
r: coverpoint i.rst;
ta: coverpoint i.taddr {bins tad={[0:65535]};}
b:coverpoint i.br_taken;
n:coverpoint i.npc {bins ne={[3000:9000]};}
p:coverpoint i.pc {bins aa={[3000:9000]};}
im:coverpoint i.instrmem_rd;
c1:cross i.enable_updatepc,i.enable_fetch;
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
mailbox #(packet)mon_sb1;
mailbox #(packet)mon_sb2;
virtual intf i;
virtual intf ri;

generator g1;
driver d1;
monitor m1;
scoreboard s1;
coverage c1;

function new(virtual intf i,virtual intf ri);
this.i=i;
this.ri=ri;
endfunction

function void build;
gen_drv=new();
mon_sb1=new();
mon_sb2=new();

g1=new(gen_drv);
d1=new(gen_drv,i,ri);
c1=new(i);
m1=new(mon_sb1,mon_sb2,i,ri);
s1=new(mon_sb1,mon_sb2);
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

module fetch_test(intf i,intf ri);
environment en;
initial
begin
en=new(i,ri);

en.build();
repeat(10000) begin
#10 en.run();
end
end
endmodule

//top

module fetch_top;
bit clk,rst;

intf i(.clk,.rst);
intf ri(.clk,.rst);


always #5 clk++;

initial
  begin
     rst++;
   #200 rst++;
   
   #500 $stop;
  end

fetch f1(.clk,.rst,.enable_updatepc(ri.enable_updatepc),.enable_fetch(ri.enable_fetch),.br_taken(ri.br_taken),.taddr(ri.taddr),.pc(ri.pc),.npc(ri.npc),.instrmem_rd(ri.instrmem_rd));

fetch_debug f2(.clock(clk),.reset(rst),.enable_updatePC(i.enable_updatepc),.enable_fetch(i.enable_fetch),.br_taken(i.br_taken),.taddr(i.taddr),.pc(i.pc),.npc_out(i.npc),.instrmem_rd(i.instrmem_rd));

fetch_test t(i,ri);
endmodule

