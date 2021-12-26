`timescale 1ns / 1ps
module tb;

	reg clk;
	reg rst;
	reg WREN;
	reg RDEN;
	reg [7:0] data_in;
	reg full;
	reg empty;
	reg [2:0] next_write_address;
	reg [2:0] next_read_address;
	wire [7:0] data_out;
	wire [2:0] read_address;
	wire [2:0] write_address;


 fifo fifo_si(  .clk(clk),
                .rst(rst),
                .WREN(WREN),
                .RDEN(RDEN),
                .data_in(data_in),
                .full(full),
                .empty(empty),
                .data_out(data_out),
                .read_address(read_address),
                .write_address(write_address)
    );

	always begin 
	#5
	clk = ~clk;
	end

	always_ff @(posedge clk)
		begin
			next_write_address <= write_address;
		end

	always_ff @(posedge clk)
		begin
			next_read_address <= read_address;
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
	#10 RDEN = 1; WREN = 0;
	#10 RDEN = 1; WREN = 0;
	#10 RDEN = 1; WREN = 0;
	#10 RDEN = 1; WREN = 0;
	#10 RDEN = 1; WREN = 0;
	#10 RDEN = 1; WREN = 0;
	#10 RDEN = 1; WREN = 0;
	#10 RDEN = 1; WREN = 0;
	#10 RDEN = 1; WREN = 0;
	RDEN = 1; WREN = 1;
	#10	data_in  = 11;
	#10	data_in  = 12;
	#10	data_in  = 13;
	#10	data_in  = 14;
	#10	data_in  = 15;
	#10	data_in  = 16;
	#10	data_in  = 17; RDEN = 0;
	#10 data_in  = 18;
	#10 data_in  = 19;
	#10 data_in  = 20;
	#10 data_in  = 21;
	#10 data_in  = 22;
	#10 data_in  = 23;
	#10 data_in  = 24;
	#10 data_in  = 25;
	RDEN = 1; WREN = 0;
			end

 

	property not_empty_after_write; // when fifo is empty, so write then it won't be empty anymore
    @(posedge clk) disable iff (!rst) ((empty && WREN) |=> (!empty));
  endproperty
  assert property (not_empty_after_write);

	property not_full_after_read; // when fifo is full, so read then it won't be full anymore
    @(posedge clk) disable iff (!rst) ((full && RDEN) |=> (!full));
  endproperty
  assert property (not_full_after_read);

	property WREN_RDEN; // read enable and write enable are both on
    @(posedge clk) disable iff (!rst) ((WREN && RDEN) |=> (!full && !empty));
  endproperty
  assert property (WREN_RDEN);

  property WREN_RDEN_empty; // read enable and write enable are both on and fifo is empty, so wrie_ptr will runover read_ptr
    @(posedge clk) disable iff (!rst) (((WREN && RDEN) && empty) |=> (write_address == read_address + 1 )); // read + 1, as write_ptr runover read_ptr 
  endproperty
  assert property (WREN_RDEN_empty);

	property WREN_RDEN_full; // read enable and write enable are both on and fifo is empty, so wrie_ptr will runover read_ptr
    @(posedge clk) disable iff (!rst) (((WREN && RDEN) && full) |=> (read_address == write_address + 1 )); // write + 1, as read_ptr runover write_ptr
  endproperty
  assert property (WREN_RDEN_full);

	property valid_output;
    @(posedge clk) disable iff (!rst) ((RDEN && !empty) |=> (!$isunknown(data_out)));   // valid data, this assertion is to check the behavior of the two port mem
  endproperty										          // when getting new data to be stored in the mem, the output from the mem must be valid
  assert property (valid_output);					// if the data is valid
	// (&& !empty), this is for the first situation of teh fifo, when the fifo is empty, so we will not read the initial of the data_out which is XXXX
																// mainly here we are checking if there is any problem in the two port mem when reading from it
																// if empty and RDEN = 1, so read_ptr shouldn't move 

	property empty_and_RDEN; // if empty and RDEN = 1, so read_ptr shouldn't move
    @(posedge clk) disable iff (!rst) ((empty && (RDEN)) |=> (read_address == next_read_address));
  endproperty
  assert property (empty_and_RDEN);

	property full_and_WREN; // if full and WREN = 1, so write_ptr shouldn't move 
    @(posedge clk) disable iff (!rst) ((full && (WREN)) |=> (write_address == next_write_address ));
  endproperty
  assert property (full_and_WREN);

	property eventually_full;																												
    @(posedge clk) disable iff (!rst) ((WREN) |=> s_eventually (full));
  endproperty
  assert property (eventually_full);

	property eventually_empty;
    @(posedge clk) disable iff (!rst) ((RDEN) |=> s_eventually (empty));
  endproperty
  assert property (eventually_empty);


//	assert property (s_ab);
endmodule

 //  ((D ##1 Q) or (!D ##1 Q ));
