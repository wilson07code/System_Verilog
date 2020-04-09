class example_this;
bit [31:0]addr;
bit [20:0]in;
bit[31:0]data;
bit write;
string pkt_type;

function new (bit[31:0]addr,data,bit write, bit [20:0]in,string pkt_type);
this.addr=addr;
this.data=data;
this.write=write;
this.in=in;
this.pkt_type=pkt_type;
endfunction
function void display();
$display("%d%d\t%d\t%b\t%s",addr,in,data,write,pkt_type);
endfunction
endclass

module this_ex;
initial
begin
example_this d1;
d1=new(20,35,1,4,"good_pkt");
d1.display();
end
endmodule

