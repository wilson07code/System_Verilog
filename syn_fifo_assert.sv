module synch_fifo_case
(	input clk,rst,re,we,
	input[7:0]din,
        output reg[7:0]dout,
        output  f,e
);
  
reg [3:0] wp, rp; 
reg [7:0] mem [0:7];
  
assign e = (wp == rp) ? 1 : 0;
assign f = ({!wp[3],wp[2:0]} == rp)? 1 : 0 ;  

always @(posedge clk,posedge rst)
begin
 if(rst)
  begin
   wp <= 0; 
   rp <= 0;
  end
 else 
  case({we,f,re,e})
  4'b0010: begin 
	    wp <= wp;
	    rp <= rp+1;
	    dout <= mem[rp[2:0]];
	   end
  4'b0011: begin
	    wp <= wp;
	    rp <= rp;
	    dout <= dout;
	   end
  4'b0110: begin
	    wp <= wp;
	    rp <= rp+1;
	    dout <= mem[rp[2:0]];
	   end
  4'b1000: begin
	    wp <= wp+1;
	    rp <= rp;
	    mem[wp[2:0]] <= din;
           end
  4'b1001: begin
	    wp <= wp+1;
	    rp <= rp;
	    mem[wp[2:0]] <= din;
	   end
  4'b1010: begin
	    wp <= wp+1;
	    rp <= rp+1;
	    mem[wp[2:0]] <= din;
	    dout <= mem[rp[2:0]];
	   end
  4'b1011: begin
	    wp <= wp;
	    rp <= rp;
	    dout <= din;
	   end
  4'b1100: begin
	    wp <= wp;
	    rp <= rp;
	    dout <= dout;
	   end
  4'b1110: begin
	    wp <= wp+1;
	    rp <= rp+1;
	    mem[wp[2:0]]<= din;
	    dout <= mem[rp[2:0]];
	   end
  default: begin
	    wp <= wp;
	    rp <= rp;
           end
   endcase
 end
endmodule


///------------assertion------///

//`include"synch_fifo_case.v"

module fifo_assertions 
(	     
        input clk,rst,re,we,
	input[7:0]din,
        input reg[7:0]dout,
        input  f,e
);

sequence reset_seq;
((!e) && (!f));
endsequence

property reset_prty;
@(posedge clk) (rst) |-> e ##0 !f; 
endproperty

sequence overflow_seq;
((!e) && (!re && we)) ;
endsequence

property overflow_prty;
@(posedge clk) overflow_seq[*8]  |=> f;
endproperty

sequence underflow_seq;
(!f && !we && re);
endsequence

property underflow_prty;
@(posedge clk) underflow_seq[*8]  |=> e;
endproperty

 
RESET:assert property (reset_prty) $display(" reset pass!!"); else $error("reset fail!!");
FIFO_UNDERFLOW:assert property (underflow_prty) $display("empty pass!!"); else $error("empty fail!!");
FIFO_OVERFLOW:assert property (overflow_prty) $display("full pass!!"); else $error("full fail!!");


endmodule


///------------fifo_TB-----------//

//`include"fifo_assertions.sv"

module synch_fifo_case_tb();
 logic clk,rst,re,we;
 logic [7:0]din;
 logic f,e;
 logic [7:0]dout;

 synch_fifo_case s1(.clk(clk),.rst(rst),.re(re),.we(we),.din(din),.f(f),.e(e),.dout(dout));

 bind synch_fifo_case : s1 fifo_assertions fa1 (.clk(clk),.rst(rst),.re(re),.we(we),.din(din),.f(f),.e(e),.dout(dout)); 
 
 initial
  clk=1'b0;
   
 always #50 clk=~clk;
      
 initial
  begin
   rst=1'b1;
   #80 rst=1'b0;
       {we,re}=2'b00;
   #80 {we,re}=2'b11;
   #80 {we,re}=2'b11;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b11;
   #80 {we,re}=2'b11;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b11;
   #80 {we,re}=2'b11;

   rst=1'b1;
   #80 rst=1'b0;
       {we,re}=2'b00;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b11;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b00;
   #80 {we,re}=2'b11;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b00;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b11;
   #80 {we,re}=2'b01;


   rst=1'b1;
   #80 rst=1'b0;
       {we,re}=2'b00;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
  
   #80 {we,re}=2'b00;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   
   #80 {we,re}=2'b00;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
 
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b11;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b11;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b10;

   #80 {we,re}=2'b00;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;

   #80 {we,re}=2'b00;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;

   #80 {we,re}=2'b00;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;

    rst=1'b1;
   #80 rst=1'b0;
       {we,re}=2'b00;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
  

   rst=1'b1;
   #80 rst=1'b0;
       {we,re}=2'b00;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
  
   #80 {we,re}=2'b00;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;

   
   #80 {we,re}=2'b00;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;
   #80 {we,re}=2'b01;

   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
   #80 {we,re}=2'b10;
  
  end

 initial
   begin
    din=8'b0;
    repeat(256)
    #100 din=din+1'b1;
    #100 $stop ;
   end

 initial
  $monitor($time,"rst=%b,we=%b,f=%b,re=%b,e=%b,din=%d,dout=%d",rst,we,f,re,e,din,dout);

  
endmodule
                 
        
                