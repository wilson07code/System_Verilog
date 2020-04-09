module single_port_asyn_rd_ram
(
 input clk,we,
 input [7:0] d_in,
 input [2:0] addr,
 output [7:0] d_out
);

 reg [7:0] memory [0:7];

 always @(posedge clk)
  begin
    if (we)
     memory[addr] <=  d_in;
  end

 assign d_out =  memory[addr];

endmodule



//
class packet;
 
 rand bit we;
 rand bit [7:0] d_in;
 rand bit [2:0] addr;
 bit [7:0] d_out;

endclass



//
interface intf(input clk);
 
 bit we;
 bit [7:0] d_in;
 bit [2:0] addr;
 bit [7:0] d_out;
 p1:assert property (@(posedge clk) we |-> $stable (d_out));
endinterface




//
class generator;
 
 packet pkt;
 mailbox #(packet) gen_drv;
 
 function new(mailbox #(packet) gen_drv);
  this.gen_drv = gen_drv;
 endfunction

 task run();
  
  pkt = new();
   assert(pkt.randomize())
    gen_drv.put(pkt);
   else
    $display("Randomization failed!!");
 endtask

endclass
 



//
class driver;

 packet pkt;

 mailbox #(packet) gen_drv;
 mailbox #(packet) drv_sb;

 virtual intf i;

 function new (mailbox #(packet) gen_drv, mailbox #(packet) drv_sb, virtual intf i);

  this.gen_drv = gen_drv;
  this.drv_sb = drv_sb;
  this.i = i;
 
 endfunction

 task run(); 
  
  @(posedge i.clk);
  
  gen_drv.get(pkt);
  drv_sb.put(pkt);
  
  i.we = pkt.we;
  i.d_in = pkt.d_in;
  i.addr = pkt.addr;

 endtask

endclass



//
class monitor;

 packet pkt = new();
 
 mailbox #(packet) mon_sb;
 
 virtual intf i;

 function new (mailbox #(packet) mon_sb,virtual intf i);
  
  this.mon_sb = mon_sb;
  this.i = i;

 endfunction

 task run (); 

 @(posedge i.clk);
  
  pkt.we = i.we;
  pkt.d_in = i.d_in;
  pkt.addr = i.addr;
  pkt.d_out = i.d_out;
  
  mon_sb.put(pkt);

 endtask

endclass 




//
class scoreboard;

 packet pkt1,pkt2;
 
 mailbox #(packet) drv_sb;
 mailbox #(packet) mon_sb;

 function new (mailbox #(packet) drv_sb ,mailbox #(packet) mon_sb );

  this.drv_sb = drv_sb;
  this.mon_sb = mon_sb;

 endfunction

 reg [7:0] memory [0:7];
 
 task run();
  
  drv_sb.get(pkt1);
  mon_sb.get(pkt2);

  if (pkt1.we)
    memory[pkt1.addr] =  pkt1.d_in;
  
  pkt1.d_out =  memory[pkt1.addr]; 

  if(pkt1.we == pkt2.we && pkt1.addr == pkt2.addr && pkt1.d_in == pkt2.d_in && memory[pkt1.addr] == memory[pkt2.addr] && pkt2.d_out == pkt2.d_out)
   begin
      $display($time,"pkt1.we=%b,pkt1.addr=%d,pkt1.d_in=%d,memory[pkt1.addr=%d]=%d,pkt1.d_out=%d",pkt1.we,pkt1.addr,pkt1.d_in,pkt1.addr,memory[pkt1.addr],pkt1.d_out); 
      $display($time,"pkt2.we=%b,pkt2.addr=%d,pkt2.d_in=%d,memory[pkt2.addr=%d]=%d,pkt2.d_out=%d",pkt2.we,pkt2.addr,pkt2.d_in,pkt2.addr,memory[pkt1.addr],pkt2.d_out);
      $display("Hit!!");  
     end
   else
     begin
      $display($time,"pkt1.we=%b,pkt1.addr=%d,pkt1.d_in=%d,pkt1.d_out=%d",pkt1.we,pkt1.addr,pkt1.d_in,pkt1.d_out); 
      $display($time,"pkt2.we=%b,pkt2.addr=%d,pkt2.d_in=%d,pkt2.d_out=%d",pkt2.we,pkt2.addr,pkt2.d_in,pkt2.d_out);
      $display("Miss!!");  
     end
 
 endtask

endclass
  


//coverage
class coverage;
virtual intf i;

covergroup cg @(posedge i.clk);
sram_d_in_CP: coverpoint i.d_in;
sram_d_out_CP: coverpoint i.d_out;
sram_addr_CP: coverpoint i.addr ;
//sram_we_CP: cross i.we;
endgroup

function new (virtual intf i);
this.i=i;
cg=new();
endfunction

task sample();
cg.sample();
endtask
endclass





//environment

class environment;

 mailbox #(packet) gen_drv;
 mailbox #(packet) drv_sb;
 mailbox #(packet) mon_sb;

 virtual intf i;
 
 generator g1;
coverage c1;
 driver d1;
 monitor m1;
 scoreboard s1;

 function new(virtual intf i);
  
  this.i = i;
 
 endfunction

 function void build ();
  
  gen_drv = new();
  drv_sb = new();
  mon_sb = new();

  g1 = new(gen_drv);
  d1 = new(gen_drv,drv_sb,i);
  m1 = new(mon_sb,i);
  s1 = new(drv_sb,mon_sb);
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

module test (intf i);

 environment en;

 initial 
  begin
   
   en = new(i);
   en.build();

   repeat (1000)
   #10 en.run();

  end

endmodule




//top 

module top_spram();
 
 reg clk;
 
 always #5 clk = ~clk;
 
 initial
  begin 
   clk = 1'b0;
  end
 
 intf i(.clk(clk));

 single_port_asyn_rd_ram spr1 (.clk(clk),.we(i.we),.d_in(i.d_in),.addr(i.addr),.d_out(i.d_out)); 

 test t(.i(i)); 

endmodule

