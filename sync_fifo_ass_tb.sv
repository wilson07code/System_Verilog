`include"fifo_assertions.sv"

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
                 
        
                