`timescale 1ns / 1ps

module main(start, reset, clk, finish, return_val);
  logic [31:0] reg_64 = 0;
  logic [31:0] reg_32 = 0;
  logic [31:0] reg_96 = 0;
  logic [31:0] reg_16 = 0;
  logic [31:0] reg_80 = 0;
  logic [31:0] reg_48 = 0;
  logic [31:0] reg_112 = 0;
  logic [31:0] reg_8 = 0;
  logic [31:0] reg_72 = 0;
  logic [31:0] reg_40 = 0;
  logic [31:0] reg_104 = 0;
  logic [31:0] reg_24 = 0;
  logic [31:0] reg_88 = 0;
  logic [31:0] reg_56 = 0;
  logic [31:0] reg_120 = 0;
  logic [31:0] reg_4 = 0;
  logic [31:0] reg_132 = 0;
  logic [31:0] reg_68 = 0;
  logic [31:0] reg_36 = 0;
  logic [31:0] reg_100 = 0;
  logic [31:0] reg_20 = 0;
  logic [31:0] reg_84 = 0;
  logic [31:0] reg_52 = 0;
  logic [31:0] reg_116 = 0;
  logic [31:0] reg_12 = 0;
  logic [31:0] reg_76 = 0;
  logic [31:0] reg_44 = 0;
  logic [31:0] reg_108 = 0;
  logic [31:0] reg_28 = 0;
  logic [31:0] reg_92 = 0;
  logic [31:0] reg_60 = 0;
  logic [31:0] reg_2 = 0;
  logic [31:0] reg_130 = 0;
  logic [31:0] reg_66 = 0;
  logic [31:0] reg_34 = 0;
  logic [31:0] reg_98 = 0;
  logic [31:0] reg_18 = 0;
  logic [31:0] reg_82 = 0;
  logic [31:0] reg_50 = 0;
  logic [31:0] reg_114 = 0;
  logic [31:0] reg_10 = 0;
  logic [31:0] reg_74 = 0;
  logic [31:0] reg_42 = 0;
  logic [31:0] reg_106 = 0;
  logic [31:0] reg_26 = 0;
  logic [31:0] reg_90 = 0;
  logic [31:0] reg_58 = 0;
  logic [31:0] reg_122 = 0;
  logic [31:0] reg_6 = 0;
  logic [31:0] reg_134 = 0;
  logic [31:0] reg_70 = 0;
  logic [31:0] reg_38 = 0;
  logic [31:0] reg_102 = 0;
  logic [31:0] reg_22 = 0;
  logic [31:0] reg_86 = 0;
  logic [31:0] reg_54 = 0;
  logic [31:0] reg_118 = 0;
  logic [31:0] reg_14 = 0;
  logic [31:0] reg_78 = 0;
  logic [31:0] reg_46 = 0;
  logic [31:0] reg_110 = 0;
  logic [31:0] reg_30 = 0;
  logic [31:0] reg_94 = 0;
  logic [31:0] reg_62 = 0;
  logic [31:0] reg_133 = 0;
  logic [31:0] reg_131 = 0;
  logic [31:0] reg_135 = 0;
  (* ram_style = "block" *)
  logic [31:0] stack [1019:0];
  logic [31:0] state = 0;
  output logic [31:0] return_val = 0;
  output logic [0:0] finish = 0;
  input [0:0] clk;
  input [0:0] reset;
  input [0:0] start;
  reg [31:0] f_add_a, f_add_b, f_mul_a, f_mul_b;
  wire [31:0] f_add_res, f_mul_res;
  array_RAM_fadd_32bkb f_add(.clk(clk), .reset(1'b0), .ce(1'b1), .din0(f_add_a), .din1(f_add_b), .dout(f_add_res));
  array_RAM_fmul_32cud f_mul(.clk(clk), .reset(1'b0), .ce(1'b1), .din0(f_mul_a), .din1(f_mul_b), .dout(f_mul_res));

  always @(negedge clk) begin
    if ({reg_135 != reg_131}) begin
      if (reg_134) begin
        stack[reg_130] <= reg_132;
      end else begin
        reg_133 <= stack[reg_130];
      end
      reg_131 <= reg_135;
    end else begin
    end
  end

  always @(posedge clk) begin
    if ({reset == 32'd1}) begin
      state <= 32'd93;
    end else begin
      case (state)
        32'd163: begin
          state <= 32'd110;
          reg_98 <= reg_133;
        end
        32'd157: begin
          state <= 32'd114;
          reg_110 <= reg_133;
        end
        32'd150: begin
          state <= 32'd107;
          reg_114 <= reg_133;
        end
        32'd145: begin
          state <= 32'd109;
          reg_118 <= reg_133;
        end
        32'd139: begin
          state <= 32'd100;
          reg_100 <= reg_133;
        end
        32'd134: begin
          state <= 32'd65;
          state <= (32'd0 ? 32'd135 : 32'd65);
        end
        32'd133: begin
          state <= 32'd134;
          reg_135 <= ( ~ reg_135);
          reg_134 <= 32'd1;
          reg_132 <= reg_58;
          reg_130 <= {{{reg_56 + 32'd0} + {reg_6 * 32'd4}} / 32'd4};
        end
        32'd132: begin
          state <= 32'd133;
          reg_135 <= ( ~ reg_135);
          reg_134 <= 32'd1;
          reg_132 <= reg_66;
          reg_130 <= {{{reg_64 + 32'd0} + {reg_6 * 32'd4}} / 32'd4};
        end
        32'd131: begin
          state <= 32'd132;
          reg_135 <= ( ~ reg_135);
          reg_134 <= 32'd1;
          reg_132 <= reg_74;
          reg_130 <= {{{reg_72 + 32'd0} + {reg_6 * 32'd4}} / 32'd4};
        end
        32'd130: begin
          state <= 32'd131;
          reg_135 <= ( ~ reg_135);
          reg_134 <= 32'd1;
          reg_132 <= reg_82;
          reg_130 <= {{{reg_80 + 32'd0} + {reg_6 * 32'd4}} / 32'd4};
        end
        32'd129: begin
          reg_80 <= {{reg_84 + reg_86} + 32'd0};
          reg_72 <= {{reg_76 + reg_78} + 32'd0};
          reg_64 <= {{reg_68 + reg_70} + 32'd0};
          reg_56 <= {{reg_60 + reg_62} + 32'd0};
          state <= 32'd130;
        end
        32'd127: begin
          reg_102 <= {reg_102 + 32'd1};
          state <= 32'd25;
          state <= (32'd0 ? 32'd128 : 32'd25);
        end
        32'd124: begin
          state <= 32'd25;
          state <= (32'd0 ? 32'd125 : 32'd25);
        end
        32'd123: begin
          reg_12 <= {{reg_40 + reg_42} + 32'd0};
          reg_96 <= {{reg_40 + reg_42} + 32'd0};
          reg_14 <= {{reg_36 + reg_38} + 32'd0};
          reg_94 <= {{reg_36 + reg_38} + 32'd0};
          reg_16 <= {{reg_32 + reg_34} + 32'd0};
          reg_92 <= {{reg_32 + reg_34} + 32'd0};
          reg_18 <= {{reg_28 + reg_30} + 32'd0};
          reg_90 <= {{reg_28 + reg_30} + 32'd0};
          reg_20 <= {{reg_24 + reg_26} + 32'd0};
          reg_88 <= {{reg_24 + reg_26} + 32'd0};
          state <= 32'd124;
        end
        32'd115: begin
          reg_100 <= {{reg_100 + reg_108} + 32'd0};
          state <= 32'd21;
          state <= (32'd0 ? 32'd116 : 32'd21);
        end
        32'd114: begin
          reg_108 <= {reg_98 * reg_110};
          reg_104 <= {reg_104 + 32'd1};
          state <= 32'd115;
        end
        32'd113: begin
          state <= 32'd157;
          reg_135 <= ( ~ reg_135);
          reg_134 <= 32'd0;
          reg_130 <= {{{reg_90 + 32'd0} + {reg_104 * 32'd4}} / 32'd4};
        end
        32'd112: begin
          state <= 32'd113;
          reg_135 <= ( ~ reg_135);
          reg_134 <= 32'd1;
          reg_132 <= reg_112;
          reg_130 <= {{{reg_94 + 32'd0} + {reg_104 * 32'd4}} / 32'd4};
        end
        32'd111: begin
          reg_112 <= {{reg_114 + reg_116} + 32'd0};
          state <= 32'd112;
        end
        32'd110: begin
          reg_116 <= {reg_118 * reg_98};
          state <= 32'd111;
        end
        32'd109: begin
          state <= 32'd163;
          reg_135 <= ( ~ reg_135);
          reg_134 <= 32'd0;
          reg_130 <= {{{reg_120 + 32'd0} + {reg_104 * 32'd4}} / 32'd4};
        end
        32'd108: begin
          state <= 32'd145;
          reg_135 <= ( ~ reg_135);
          reg_134 <= 32'd0;
          reg_130 <= {{{reg_88 + 32'd0} + {reg_102 * 32'd4}} / 32'd4};
        end
        32'd107: begin
          reg_120 <= {{reg_96 + reg_122} + 32'd0};
          state <= 32'd108;
        end
        32'd106: begin
          state <= 32'd150;
          reg_135 <= ( ~ reg_135);
          reg_134 <= 32'd0;
          reg_130 <= {{{reg_94 + 32'd0} + {reg_104 * 32'd4}} / 32'd4};
        end
        32'd104: begin
          finish <= 32'd1;
          return_val <= reg_10;
          state <= 32'd104;
          state <= (32'd0 ? 32'd105 : 32'd104);
        end
        32'd101: begin
          state <= 32'd21;
          state <= (32'd0 ? 32'd102 : 32'd21);
        end
        32'd100: begin
          reg_104 <= 32'd0;
          state <= 32'd101;
        end
        32'd98: begin
          reg_4 <= {reg_4 + 32'd1};
          state <= 32'd65;
          state <= (32'd0 ? 32'd99 : 32'd65);
        end
        32'd97: begin
          state <= 32'd98;
          reg_135 <= ( ~ reg_135);
          reg_134 <= 32'd1;
          reg_132 <= reg_46;
          reg_130 <= {{{reg_44 + 32'd0} + {reg_4 * 32'd4}} / 32'd4};
        end
        32'd96: begin
          reg_44 <= {{reg_48 + reg_50} + 32'd0};
          state <= 32'd97;
        end
        32'd95: begin
          reg_48 <= {{reg_52 + reg_54} + 32'd0};
          state <= 32'd96;
        end
        32'd93: begin
          reg_8 <= 32'd0;
          state <= 32'd91;
          state <= (32'd0 ? 32'd122 : 32'd91);
        end
        32'd91: begin
          state <= ({$signed(reg_8) < $signed(32'd1)} ? 32'd90 : 32'd51);
          state <= (32'd0 ? 32'd126 : ({$signed(reg_8) < $signed(32'd1)} ? 32'd90 : 32'd51));
        end
        32'd90: begin
          reg_6 <= 32'd0;
          state <= 32'd88;
          state <= (32'd0 ? 32'd117 : 32'd88);
        end
        32'd88: begin
          state <= ({$signed(reg_6) < $signed(32'd30)} ? 32'd87 : 32'd53);
          state <= (32'd0 ? 32'd103 : ({$signed(reg_6) < $signed(32'd30)} ? 32'd87 : 32'd53));
        end
        32'd87: begin
          reg_84 <= 32'd120;
          reg_86 <= {reg_8 * 32'd120};
          reg_82 <= {reg_6 + 32'd1};
          reg_76 <= 32'd240;
          reg_78 <= {reg_8 * 32'd120};
          reg_74 <= {reg_6 + 32'd2};
          reg_68 <= 32'd360;
          reg_70 <= {reg_8 * 32'd120};
          reg_66 <= {reg_6 + 32'd3};
          reg_60 <= 32'd0;
          reg_62 <= {reg_8 * 32'd120};
          reg_58 <= {reg_6 + 32'd4};
          reg_4 <= 32'd0;
          state <= 32'd129;
        end
        32'd65: begin
          state <= ({$signed(reg_4) < $signed(32'd30)} ? 32'd64 : 32'd55);
          state <= (32'd0 ? 32'd118 : ({$signed(reg_4) < $signed(32'd30)} ? 32'd64 : 32'd55));
        end
        32'd64: begin
          reg_52 <= 32'd480;
          reg_54 <= {reg_8 * 32'd3600};
          reg_50 <= {reg_6 * 32'd120};
          reg_46 <= {{reg_4 + reg_6} + 32'd1};
          state <= 32'd95;
        end
        32'd55: begin
          reg_6 <= {reg_6 + 32'd1};
          state <= 32'd88;
          state <= (32'd0 ? 32'd136 : 32'd88);
        end
        32'd53: begin
          reg_8 <= {reg_8 + 32'd1};
          state <= 32'd91;
          state <= (32'd0 ? 32'd121 : 32'd91);
        end
        32'd51: begin
          reg_2 <= 32'd0;
          reg_26 <= {32'd0 * 32'd120};
          reg_30 <= {32'd0 * 32'd120};
          reg_34 <= {32'd0 * 32'd120};
          reg_38 <= {32'd0 * 32'd120};
          reg_42 <= {32'd0 * 32'd3600};
          reg_40 <= 32'd480;
          reg_36 <= 32'd120;
          reg_32 <= 32'd240;
          reg_28 <= 32'd360;
          reg_24 <= 32'd0;
          reg_102 <= 32'd0;
          reg_102 <= 32'd0;
          reg_100 <= 32'd0;
          state <= 32'd123;
        end
        32'd25: begin
          state <= ({$signed(reg_102) < $signed(32'd30)} ? 32'd24 : 32'd4);
          state <= (32'd0 ? 32'd119 : ({$signed(reg_102) < $signed(32'd30)} ? 32'd24 : 32'd4));
        end
        32'd24: begin
          state <= 32'd139;
          reg_135 <= ( ~ reg_135);
          reg_134 <= 32'd0;
          reg_130 <= {{{reg_92 + 32'd0} + {reg_102 * 32'd4}} / 32'd4};
        end
        32'd21: begin
          state <= ({$signed(reg_104) < $signed(32'd30)} ? 32'd20 : 32'd7);
          state <= (32'd0 ? 32'd120 : ({$signed(reg_104) < $signed(32'd30)} ? 32'd20 : 32'd7));
        end
        32'd20: begin
          reg_122 <= {reg_102 * 32'd120};
          state <= 32'd106;
        end
        32'd7: begin
          state <= 32'd127;
          reg_135 <= ( ~ reg_135);
          reg_134 <= 32'd1;
          reg_132 <= reg_100;
          reg_130 <= {{{reg_92 + 32'd0} + {reg_102 * 32'd4}} / 32'd4};
        end
        32'd4: begin
          reg_106 <= reg_102;
          reg_22 <= reg_102;
          reg_10 <= 32'd0;
          state <= 32'd104;
        end
        default:;
      endcase
    end
  end
endmodule

`ifndef SYNTHESIS
module testbench;
   reg start, reset, clk;
   wire finish;
   wire [31:0] return_val;
   reg [31:0] cycles;

   main m(start, reset, clk, finish, return_val);

   initial begin
      clk = 0;
      start = 0;
      reset = 0;
      @(posedge clk) reset = 1;
      @(posedge clk) reset = 0;
      cycles = 0;
   end

   always #5 clk = ~clk;

   always @(posedge clk) begin
      if (finish == 1) begin
         $display("cycles: %0d", cycles);
         $display("finished: %0d", return_val);
         $finish;
      end
      cycles <= cycles + 1;
   end
endmodule
`endif
