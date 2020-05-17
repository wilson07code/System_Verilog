
// AND Gate DUT 

module and2
(
        input a,b,
        output reg c
);

always@(a,b)
begin
        c=a&b;
end

endmodule 

// Interface 

interface and2_if();

  logic a,b;
  logic c;
endinterface:and2_if


// Package 
 

 
 package my_agent_pkg;
   
    `include "uvm_macros.svh"
   //Agent Includes- Transaction, Sequence, Sequencer, Driver, Agent 
   
   import uvm_pkg::*;
   
   //////////////////////////
   //Transaction Class
   
   class my_transaction extends uvm_sequence_item;
  
  `uvm_object_utils(my_transaction)
  
     rand bit a,b;
     bit c;
     
     constraint c1 {a>=0;a<=1;}
     constraint c2 {b>=0;b<=1;}
     
     function new(string name="my_transaction");
       super.new(name);
       
    endfunction:new
    
    function string convert2string();
      return $sformatf("%s\na:\t%b\tb:\t%b\tc:\t%b",super.convert2string(),a,b,c);
      
    endfunction:convert2string
    
  endclass:my_transaction 
  
  //////////////////////////
  //END of Transaction Class
  

  //////////////////////////
  //Sequencer Class
  
  class my_sequencer extends uvm_sequencer #(my_transaction);
    `uvm_component_utils(my_sequencer)
    
    function new(string name="my_sequencer",uvm_component parent=null);
      super.new(name,parent);
    endfunction:new
    
  endclass:my_sequencer 
 //////////////////////////
 // END of Sequencer Class 
 
 
 //////////////////////////
 // Sequence Class. NOT an UVM component. Extends Transaction 
 
 class my_sequence extends uvm_sequence#(my_transaction);
   
   `uvm_object_utils(my_sequence)
   
   function new(string name="my_sequence");
     super.new(name);
   endfunction:new
   
   // Task Body. Behavior of the sequence. 
   task body;
     repeat(10) 
     begin
       my_transaction tx;
       tx=my_transaction::type_id::create("tx");
       
       start_item(tx);
       
       assert(tx.randomize());
       finish_item(tx);
      
     end
   endtask:body 
   
 endclass:my_sequence 

//////////////////////////
//END of My Sequence Class 

//////////////////////////
//Driver Class

class my_driver extends uvm_driver #(my_transaction);
  
  `uvm_component_utils(my_driver)
  
  virtual and2_if and2_vi;
  my_transaction tx;

  
  
        function new(string name="my_driver",uvm_component parent=null);
          super.new(name,parent);
        endfunction:new 
   
   function void build_phase(uvm_phase phase);
       super.build_phase(phase);

      
      if(!uvm_config_db#(virtual and2_if)::get(this, "", "and2_vi", and2_vi))
       `uvm_fatal("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"});
      
              endfunction:build_phase
        
  task run_phase(uvm_phase phase);
             
          phase.raise_objection(this);
          repeat(10)
          begin
          seq_item_port.get_next_item(tx);
          #10;
          and2_vi.a= tx.a;
          and2_vi.b= tx.b;
          
          seq_item_port.item_done();
             end
             
             
        phase.drop_objection(this);
        
      endtask:run_phase  

endclass:my_driver
 
//////////////////////////
//END of Driver Class


//////////////////////////
//Monitor Class

class my_monitor extends uvm_monitor;
  
  `uvm_component_utils(my_monitor)
  
  virtual and2_if and2_vi;
  
 function new(string name="my_monitor",uvm_component parent=null);
      super.new(name,parent);
    endfunction:new
    
  function void build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  if(!uvm_config_db#(virtual and2_if)::get(this, "", "and2_vi", and2_vi))
       `uvm_fatal("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"});
       
     endfunction:build_phase 
     
     task run_phase(uvm_phase phase);
       repeat(10)
       begin 
         my_transaction tx;
         @(and2_vi.a,and2_vi.b,and2_vi.c)
         begin
         tx=my_transaction::type_id::create("tx");
         
         tx.a=and2_vi.a;
         tx.b=and2_vi.b;
         tx.c=and2_vi.c;
         
          uvm_report_info("my_monitor",tx.convert2string());
        end
        end     endtask
    endclass:my_monitor 
            

//////////////////////////
//Agent Class

class my_agent extends uvm_agent;
  `uvm_component_utils(my_agent)
  
  my_sequencer my_sequencer_h;
  my_driver my_driver_h;
  my_monitor my_monitor_h;
  
  virtual and2_if and2_vi; // Handle for the interface
  
   function new(string name="my_agent",uvm_component parent=null);
      super.new(name,parent);
    endfunction:new
    
    function void build_phase(uvm_phase phase);
     // super.build_phase(phase);
      
      //propagate interface using config db
      
      if(!uvm_config_db#(virtual and2_if)::get(this, "", "and2_vi", and2_vi))
       `uvm_fatal("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"});

      my_sequencer_h=my_sequencer::type_id::create("my_sequencer_h",this);
      
      my_driver_h=my_driver::type_id::create("my_driver_h",this);
      
      my_monitor_h=my_monitor::type_id::create("my_monitor_h",this);
      
      
    endfunction:build_phase
    
    function void connect_phase(uvm_phase phase);
      
      my_driver_h.seq_item_port.connect(my_sequencer_h.seq_item_export);
    endfunction:connect_phase 

endclass:my_agent 

//////////////////////////
//END of Agent Class


endpackage:my_agent_pkg 
   
// Tests 

 
 
   `include "uvm_macros.svh"
   import uvm_pkg::*;

   import my_agent_pkg::*;
   
class my_test extends uvm_test; 
  
  `uvm_component_utils(my_test)

  my_agent my_agent_h;
  virtual and2_if and2_vi;
  

    function new(string name = "my_test", uvm_component parent = null);
    super.new(name,parent);
  endfunction 
  
  function void build_phase(uvm_phase phase); 
    
    my_agent_h=my_agent::type_id::create("my_agent_h",this);
    
    if(!uvm_config_db#(virtual and2_if)::get(this, "", "and2_vi", and2_vi))
       `uvm_fatal("NOVIF",{"virtual interface must be set for: ",get_full_name(),".vif"});
       
     endfunction:build_phase
       
 
 task run_phase (uvm_phase phase);
   
   my_sequence my_sequence_h=my_sequence::type_id::create("my_sequence_h");
   
   // Skipped Raise Obj

   my_sequence_h.start(my_agent_h.my_sequencer_h);
   
   // Drop 
   
 endtask:run_phase 
 
 endclass:my_test 
 
   
   
    
// Top 



module top_UVM;
  
 
  import uvm_pkg::*;
 //`include"my_test.sv"
  
  and2_if and2_vi();
  and2 dut(.a(and2_vi.a),.b(and2_vi.b),.c(and2_vi.c));
  
  initial
  begin 
    
   uvm_config_db#(virtual and2_if)::set(uvm_root::get(), "*", "and2_vi", and2_vi);

  run_test("my_test");
    end
    
  endmodule 


