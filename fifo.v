`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 12/23/2021 06:58:35 PM
// Design Name: 
// Module Name: fifo
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module fifo(    input clk,
                input rst,
                input WREN,
                input RDEN,
                input [7:0] data_in,
                output reg full,
                output reg empty,
                output [7:0] data_out
    );
reg [2:0] write_address;
reg [2:0] read_address;

reg [2:0] next_write_address;
reg [2:0] next_read_address;

reg temp_full;
reg temp_empty;

assign write_enable = WREN & (!full);
assign read_enable  = RDEN & (!empty);


two_port_mem fifo_mem(  .clk(clk),
                        .read_enable(read_enable),
                        .write_enable(write_enable),
                        .read_address(read_address),  // 8bits
                        .write_address(write_address), // 8bits
                        .write_data(data_in),    // 8bits
                        .read_data(data_out)     // 8bits
    );


always @(*)
    begin
        next_write_address = write_address + 1'b1;
        next_read_address  = read_address + 1'b1;
		  
		  if(temp_full && (write_address == read_address))
				full = 1'b1;
        else 
            full = 1'b0;
				
		  if(temp_empty && (write_address == read_address))
            empty = 1'b1;
        else 
            empty = 1'b0;       
    end

always @(posedge clk or negedge rst) 
    begin
        if(!rst) 
            begin
                write_address <= 3'd0;
                read_address  <= 3'd0;
                temp_full     <= 1'b0;
                temp_empty    <= 1'b0;
                full          <= 1'b0;
                empty         <= 1'b1;   // fifo is empty by default
            end 
        else 
            begin
                case ({WREN, RDEN})
                    2'b10: begin
                            if(!full)
                                begin
                                    empty         <= 1'b0;
									temp_empty    <= 1'b0;
									write_address <= write_address + 1'b1;												
                                    if (next_write_address == read_address)
                                        temp_full <= 1'b1;
                                    else 
                                        temp_full <= 1'b0;
                                end
                        end
                    2'b01: begin
                            if(!empty)
                                begin
									full         <= 1'b0;
									temp_full    <= 1'b0;
									read_address <= read_address + 1'b1;
                                    if (next_read_address == write_address)
                                        temp_empty <= 1'b1;
                                    else 
                                        temp_empty <= 1'b0;
                                end
                        end
                    2'b11: begin
                            case ({full, empty})
                                2'b00: begin                    // not full and not empty
										write_address <= write_address + 1'b1;
                                         if (next_write_address == read_address)
                                                temp_full <= 1'b1;
                                         else 
                                                temp_full <= 1'b0;
																
													  read_address  <= read_address + 1'b1;
                                         if (next_read_address == write_address)
                                                temp_empty <= 1'b1;
                                         else 
                                                temp_empty <= 1'b0;
                                         end

                                2'b01: begin
                                         // not full but empty
                                        read_address  <= read_address + 1'b0;
													 
										 write_address <= write_address + 1'b1;
                                        if (next_write_address == read_address)
                                                temp_full <= 1'b1;
                                        else 
                                                temp_full <= 1'b0;			
                                    end
												
                                2'b10: begin
                                         // full but not empty
                                        write_address <= write_address + 1'b0;
													 
										read_address  <= read_address + 1'b1;
                                        if (next_read_address == write_address)
                                                temp_empty <= 1'b1;
                                        else 
                                                temp_empty <= 1'b0;
                                    end
                                default: begin                    // no change (case full and empty won't happen)
                                        write_address <= write_address + 1'b0; 
                                        read_address  <= read_address + 1'b0; 
                                end
                            endcase
                        end
                endcase
            end
    end
endmodule


/*
34an el full ytl3 lazm ykon el full next bysawy el read l2n kda y3ny el write wra le read b location wahed bs f lw h3ml write 
mra kman kda el write hysawy el read kda b2et full khlas, f 34an kda lw el write next bysawy el read kda el temp_full hytl3 b one 
bs el temp_full da m3mol b non blocking khally balk. 34an el full b2a ttl3 lazm a-check  (temp_full && (write_ptr = read_ptr))
w el full m3mola combinational 34an awl ma el read - el write 3ltol el full ttl3 w msh lazm astna b2a w l7d posedge kman w a-check
3nd el poedge w kda lw 3mltha nonblocking 34an fi scenario hynoz f kda mzbota
*/
