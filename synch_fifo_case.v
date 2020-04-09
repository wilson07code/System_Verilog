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
 if (rst)
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
