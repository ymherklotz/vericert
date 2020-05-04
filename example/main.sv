module main(input start, reset, clk,
            output finished, output [31:0] return_val);

   reg [31:0]      x;
   reg [31:0]      y;
   reg [31:0]      z;
   reg [2:0]       state;

   reg [31:0]     return_val_w;
   reg            finished_w;

   localparam [2:0] START_STATE = 0;
   localparam [2:0] MAIN_STATE_0 = 1;
   localparam [2:0] MAIN_STATE_1 = 2;
   localparam [2:0] MAIN_STATE_2 = 3;
   localparam [2:0] MAIN_STATE_3 = 4;
   localparam [2:0] MAIN_STATE_4 = 5;
   localparam [2:0] FINISHED_STATE = 6;

   assign return_val = return_val_w;
   assign finished = finished_w;

   always @(posedge clk)
     if (reset) begin
        state <= START_STATE;
        return_val_w <= 0;
        finished_w <= 0;
     end
     else
       case (state)
         START_STATE: x <= 0;
         MAIN_STATE_0: y <= 0;
         MAIN_STATE_1: z <= 0;
         MAIN_STATE_2: y <= 2;
         MAIN_STATE_3: z <= 3;
         MAIN_STATE_4: x <= y * z;
         FINISHED_STATE: begin 
            return_val_w <= x;
            finished_w <= 1;
         end
         default: state <= START_STATE;
       endcase

   always @(posedge clk)
     if (state != FINISHED_STATE)
       state <= state + 1;

endmodule

module testbench;
   reg start, reset, clk;
   wire finished;
   wire [31:0] return_val;
   
   main main(start, reset, clk, finished, return_val);

   initial begin
      $dumpvars;
      start = 0;
      reset = 1;
      clk = 0;

      @(posedge clk) begin
         reset = 0;
         start = 1;
      end
      @(posedge clk) start = 0;

      #100;

      $display("Result: %d", return_val);
      $finish;
   end

   always #5 clk = ~clk;

endmodule
