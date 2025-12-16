`timescale 1ns / 1ps

module top();
  reg [31:0] a, b;
  wire [31:0] o;
  reg clk;

  array_RAM_fmul_32cud float(.clk(clk), .reset(1'b0), .ce(1'b1), .din0(a), .din1(b), .dout(o));

  initial begin
    clk = 0;

    @(posedge clk);
    a = 32'h40000000;
    b = 32'h40800000;

    @(posedge clk);    @(posedge clk);    @(posedge clk);    @(posedge clk);    @(posedge clk);    @(posedge clk);
    $display("%h", o);
    $finish;

  end

  always #10 clk = ~clk;

endmodule
