`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 12/23/2021 05:56:11 PM
// Design Name: 
// Module Name: 2_port_mem
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


module two_port_mem(    input clk,
                        input read_enable,
                        input write_enable,
                        input [2:0] read_address,  // 8bits
                        input [2:0] write_address, // 8bits
                        input [7:0] write_data,    // 8bits
                        output reg [7:0] read_data     // 8bits
    );

reg  [7 : 0] fifo_ram [0 : 7];   // 8location each is 8 bits

always @ (posedge clk)
    begin
        case ({write_enable, read_enable})
            2'b10: fifo_ram[write_address] <= write_data;  // Write
            2'b01: read_data <= fifo_ram [read_address];    // Read
            2'b11: begin                                    // Read and Write
                    fifo_ram [write_address] <= write_data; 
                    read_data <= fifo_ram [read_address];    
                end
        endcase
    end
endmodule
