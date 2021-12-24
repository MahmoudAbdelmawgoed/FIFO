`timescale 1ns / 1ps
module tb;

	reg clk;
	reg rst;
	reg WREN;
	reg RDEN;
	reg [7:0] data_in;
	reg full;
	reg empty;
	wire [7:0] data_out;


 fifo fifo_si(  .clk(clk),
                .rst(rst),
                .WREN(WREN),
                .RDEN(RDEN),
                .data_in(data_in),
                .full(full),
                .empty(empty),
                .data_out(data_out)
    );

	always begin 
	#5
	clk = ~clk;
	end


	initial
		begin
		clk = 0; rst = 0; RDEN = 0; WREN = 0; data_in  = 1;
	 #10 rst   = 0;  RDEN = 0; WREN = 0;
	 #10 rst   = 1;  WREN = 1;
	#10 data_in  = 2; WREN = 1; RDEN = 0;
	#10 data_in  = 3;
	#10	data_in  = 4;
	#10	data_in  = 5;
	#10	data_in  = 6;
	#10	data_in  = 7;
	#10	data_in  = 8; 
	#10	data_in  = 9;
	#10	data_in  = 10;
	RDEN = 1; WREN = 0;
	#10	data_in  = 11;
			end

  property p1;
    @(posedge clk) disable iff (!rst)
    ((WREN) |=> (!empty ));
  endproperty
  assert property (p1);

	property p2;
    @(posedge clk) disable iff (!rst)
    ((empty && WREN) |=> (!empty));
  endproperty
  assert property (p2);

	property p3;
    @(posedge clk) disable iff (!rst)
    ((full && RDEN) |=> (!full));
  endproperty
  assert property (p3);

	property p4;
    @(posedge clk) disable iff (!rst)
    ((WREN) |=> s_eventually (full));
  endproperty
  assert property (p4);

	property p5;
    @(posedge clk) disable iff (!rst)
    ((RDEN) |=> s_eventually (empty));
  endproperty
  assert property (p5);


//	assert property (s_ab);
endmodule

 //  ((D ##1 Q) or (!D ##1 Q ));
