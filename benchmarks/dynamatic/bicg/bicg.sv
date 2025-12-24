`timescale 1ns / 1ps

module main(start, reset, clk, finish, return_val);
  logic [31:0] reg_128 = 0;
  logic [31:0] reg_64 = 0;
  logic [31:0] reg_96 = 0;
  logic [31:0] reg_80 = 0;
  logic [31:0] reg_112 = 0;
  logic [31:0] reg_8 = 0;
  logic [31:0] reg_136 = 0;
  logic [31:0] reg_72 = 0;
  logic [31:0] reg_104 = 0;
  logic [31:0] reg_56 = 0;
  logic [31:0] reg_120 = 0;
  logic [31:0] reg_4 = 0;
  logic [31:0] reg_132 = 0;
  logic [31:0] reg_100 = 0;
  logic [31:0] reg_148 = 0;
  logic [31:0] reg_84 = 0;
  logic [31:0] reg_52 = 0;
  logic [31:0] reg_116 = 0;
  logic [31:0] reg_12 = 0;
  logic [31:0] reg_76 = 0;
  logic [31:0] reg_108 = 0;
  logic [31:0] reg_92 = 0;
  logic [31:0] reg_60 = 0;
  logic [31:0] reg_124 = 0;
  logic [31:0] reg_130 = 0;
  logic [31:0] reg_66 = 0;
  logic [31:0] reg_146 = 0;
  logic [31:0] reg_82 = 0;
  logic [31:0] reg_50 = 0;
  logic [31:0] reg_114 = 0;
  logic [31:0] reg_10 = 0;
  logic [31:0] reg_138 = 0;
  logic [31:0] reg_74 = 0;
  logic [31:0] reg_106 = 0;
  logic [31:0] reg_90 = 0;
  logic [31:0] reg_58 = 0;
  logic [31:0] reg_6 = 0;
  logic [31:0] reg_134 = 0;
  logic [31:0] reg_70 = 0;
  logic [31:0] reg_102 = 0;
  logic [31:0] reg_150 = 0;
  logic [31:0] reg_86 = 0;
  logic [31:0] reg_118 = 0;
  logic [31:0] reg_110 = 0;
  logic [31:0] reg_94 = 0;
  logic [31:0] reg_62 = 0;
  logic [31:0] reg_126 = 0;
  logic [31:0] reg_9 = 0;
  logic [31:0] reg_5 = 0;
  logic [31:0] reg_149 = 0;
  logic [31:0] reg_13 = 0;
  logic [31:0] reg_147 = 0;
  logic [31:0] reg_11 = 0;
  logic [31:0] reg_7 = 0;
  logic [31:0] reg_151 = 0;
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
    if ({reg_151 != reg_147}) begin
      if (reg_150) begin
        stack[reg_146] <= reg_148;
      end else begin
        reg_149 <= stack[reg_146];
      end
      reg_147 <= reg_151;
    end else begin
    end
  end

  always @(posedge clk) begin
    if ({reset == 32'd1}) begin
      state <= 32'd90;
    end else begin
      case (state)
        32'd217: begin
          state <= 32'd136;
          reg_126 <= reg_149;
        end
        32'd216: begin
          state <= 32'd112;
          reg_12 <= reg_149;
        end
        32'd204: begin
          state <= 32'd118;
          reg_114 <= reg_149;
        end
        32'd197: begin
          state <= 32'd106;
          reg_116 <= reg_149;
        end
        32'd179: begin
          state <= 32'd115;
          reg_130 <= reg_149;
        end
        32'd172: begin
          state <= 32'd117;
          reg_134 <= reg_149;
        end
        32'd160: begin
          reg_7 <= ({reg_13 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_7);
          state <= ({{reg_13 == 32'd0} & ({reg_13 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_7)} ? 32'd88 : state);
          state <= ({{reg_13 | {({reg_13 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_7) == 32'd0}} & {{reg_13 == 32'd0} & {({reg_13 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_7) == 32'd0}}} ? 32'd51 : ({{reg_13 == 32'd0} & ({reg_13 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_7)} ? 32'd88 : state));
          state <= ({{reg_13 | {({reg_13 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_7) == 32'd0}} & {reg_13 | ({reg_13 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_7)}} ? 32'd161 : ({{reg_13 | {({reg_13 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_7) == 32'd0}} & {{reg_13 == 32'd0} & {({reg_13 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_7) == 32'd0}}} ? 32'd51 : ({{reg_13 == 32'd0} & ({reg_13 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_7)} ? 32'd88 : state)));
        end
        32'd159: begin
          reg_4 <= {reg_4 + 32'd1};
          reg_13 <= {$signed({reg_4 + 32'd1}) < $signed(32'd30)};
          state <= ({$signed({reg_4 + 32'd1}) < $signed(32'd30)} ? 32'd63 : state);
          reg_6 <= ({{$signed({reg_4 + 32'd1}) < $signed(32'd30)} == 32'd0} ? {reg_6 + 32'd1} : reg_6);
          state <= ({{$signed({reg_4 + 32'd1}) < $signed(32'd30)} == 32'd0} ? 32'd160 : ({$signed({reg_4 + 32'd1}) < $signed(32'd30)} ? 32'd63 : state));
        end
        32'd158: begin
          state <= 32'd159;
          reg_151 <= ( ~ reg_151);
          reg_150 <= 32'd1;
          reg_148 <= reg_52;
          reg_146 <= {{{reg_50 + 32'd0} + {reg_4 * 32'd4}} / 32'd4};
        end
        32'd157: begin
          reg_50 <= {{reg_56 + reg_58} + 32'd0};
          state <= 32'd158;
        end
        32'd156: begin
          reg_56 <= {{reg_60 + reg_62} + 32'd0};
          state <= 32'd157;
        end
        32'd154: begin
          reg_118 <= ({reg_11 == 32'd0} ? {reg_118 + 32'd1} : reg_118);
          reg_5 <= ({reg_11 == 32'd0} ? {$signed(({reg_11 == 32'd0} ? {reg_118 + 32'd1} : reg_118)) < $signed(32'd30)} : reg_5);
          state <= ({{reg_11 == 32'd0} & ({reg_11 == 32'd0} ? {$signed(({reg_11 == 32'd0} ? {reg_118 + 32'd1} : reg_118)) < $signed(32'd30)} : reg_5)} ? 32'd25 : state);
          state <= ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(({reg_11 == 32'd0} ? {reg_118 + 32'd1} : reg_118)) < $signed(32'd30)} : reg_5) == 32'd0}} & {{reg_11 == 32'd0} & {({reg_11 == 32'd0} ? {$signed(({reg_11 == 32'd0} ? {reg_118 + 32'd1} : reg_118)) < $signed(32'd30)} : reg_5) == 32'd0}}} ? 32'd7 : ({{reg_11 == 32'd0} & ({reg_11 == 32'd0} ? {$signed(({reg_11 == 32'd0} ? {reg_118 + 32'd1} : reg_118)) < $signed(32'd30)} : reg_5)} ? 32'd25 : state));
          state <= ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(({reg_11 == 32'd0} ? {reg_118 + 32'd1} : reg_118)) < $signed(32'd30)} : reg_5) == 32'd0}} & {reg_11 | ({reg_11 == 32'd0} ? {$signed(({reg_11 == 32'd0} ? {reg_118 + 32'd1} : reg_118)) < $signed(32'd30)} : reg_5)}} ? 32'd155 : ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(({reg_11 == 32'd0} ? {reg_118 + 32'd1} : reg_118)) < $signed(32'd30)} : reg_5) == 32'd0}} & {{reg_11 == 32'd0} & {({reg_11 == 32'd0} ? {$signed(({reg_11 == 32'd0} ? {reg_118 + 32'd1} : reg_118)) < $signed(32'd30)} : reg_5) == 32'd0}}} ? 32'd7 : ({{reg_11 == 32'd0} & ({reg_11 == 32'd0} ? {$signed(({reg_11 == 32'd0} ? {reg_118 + 32'd1} : reg_118)) < $signed(32'd30)} : reg_5)} ? 32'd25 : state)));
        end
        32'd153: begin
          reg_151 <= {( - {{32'd1 & {reg_11 == 32'd0}} != 32'd0}) ^ reg_151};
          reg_150 <= 32'd1;
          reg_148 <= ({32'd1 & {reg_11 == 32'd0}} ? reg_116 : reg_148);
          reg_146 <= ({32'd1 & {reg_11 == 32'd0}} ? {{{reg_108 + 32'd0} + {reg_118 * 32'd4}} / 32'd4} : reg_146);
          state <= 32'd154;
        end
        32'd152: begin
          state <= (reg_11 ? 32'd23 : state);
          state <= ({reg_11 == 32'd0} ? 32'd153 : (reg_11 ? 32'd23 : state));
        end
        32'd151: begin
          state <= 32'd152;
        end
        32'd150: begin
          state <= 32'd151;
        end
        32'd149: begin
          state <= 32'd150;
        end
        32'd148: begin
          state <= 32'd149;
        end
        32'd147: begin
          state <= 32'd148;
        end
        32'd146: begin
          state <= 32'd147;
        end
        32'd145: begin
          state <= 32'd146;
        end
        32'd144: begin
          state <= 32'd145;
        end
        32'd143: begin
          state <= 32'd144;
        end
        32'd142: begin
          f_add_a <= reg_116;
          f_add_b <= reg_124;
          reg_116 <= f_add_res;
          state <= 32'd143;
        end
        32'd141: begin
          state <= 32'd142;
        end
        32'd140: begin
          state <= 32'd141;
        end
        32'd139: begin
          state <= 32'd140;
        end
        32'd138: begin
          state <= 32'd139;
        end
        32'd137: begin
          state <= 32'd138;
        end
        32'd136: begin
          f_mul_a <= reg_114;
          f_mul_b <= reg_126;
          reg_124 <= f_mul_res;
          reg_120 <= {reg_120 + 32'd1};
          reg_11 <= {$signed({reg_120 + 32'd1}) < $signed(32'd30)};
          state <= 32'd137;
        end
        32'd135: begin
          state <= 32'd217;
          reg_151 <= ( ~ reg_151);
          reg_150 <= 32'd0;
          reg_146 <= {{{reg_106 + 32'd0} + {reg_120 * 32'd4}} / 32'd4};
        end
        32'd134: begin
          state <= 32'd135;
          reg_151 <= ( ~ reg_151);
          reg_150 <= 32'd1;
          reg_148 <= reg_128;
          reg_146 <= {{{reg_110 + 32'd0} + {reg_120 * 32'd4}} / 32'd4};
        end
        32'd133: begin
          state <= 32'd134;
        end
        32'd132: begin
          state <= 32'd133;
        end
        32'd131: begin
          state <= 32'd132;
        end
        32'd130: begin
          state <= 32'd131;
        end
        32'd129: begin
          state <= 32'd130;
        end
        32'd128: begin
          state <= 32'd129;
        end
        32'd127: begin
          state <= 32'd128;
        end
        32'd126: begin
          state <= 32'd127;
        end
        32'd125: begin
          state <= 32'd126;
        end
        32'd124: begin
          f_add_a <= reg_130;
          f_add_b <= reg_132;
          reg_128 <= f_add_res;
          state <= 32'd125;
        end
        32'd123: begin
          state <= 32'd124;
        end
        32'd122: begin
          state <= 32'd123;
        end
        32'd121: begin
          state <= 32'd122;
        end
        32'd120: begin
          state <= 32'd121;
        end
        32'd119: begin
          state <= 32'd120;
        end
        32'd118: begin
          f_mul_a <= reg_134;
          f_mul_b <= reg_114;
          reg_132 <= f_mul_res;
          state <= 32'd119;
        end
        32'd117: begin
          state <= 32'd204;
          reg_151 <= ( ~ reg_151);
          reg_150 <= 32'd0;
          reg_146 <= {{{reg_136 + 32'd0} + {reg_120 * 32'd4}} / 32'd4};
        end
        32'd116: begin
          state <= 32'd172;
          reg_151 <= ( ~ reg_151);
          reg_150 <= 32'd0;
          reg_146 <= {{{reg_104 + 32'd0} + {reg_118 * 32'd4}} / 32'd4};
        end
        32'd115: begin
          reg_136 <= {{reg_112 + reg_138} + 32'd0};
          state <= 32'd116;
        end
        32'd114: begin
          state <= 32'd179;
          reg_151 <= ( ~ reg_151);
          reg_150 <= 32'd0;
          reg_146 <= {{{reg_110 + 32'd0} + {reg_120 * 32'd4}} / 32'd4};
        end
        32'd112: begin
          reg_10 <= reg_12;
          finish <= 32'd1;
          return_val <= reg_12;
          state <= 32'd112;
          state <= (32'd0 ? 32'd113 : 32'd112);
        end
        32'd110: begin
          state <= ({reg_9 == 32'd0} ? 32'd25 : state);
          state <= (reg_9 ? 32'd111 : ({reg_9 == 32'd0} ? 32'd25 : state));
        end
        32'd107: begin
          state <= 32'd23;
          state <= (32'd0 ? 32'd108 : 32'd23);
        end
        32'd106: begin
          reg_120 <= 32'd0;
          state <= 32'd107;
        end
        32'd103: begin
          state <= 32'd63;
          state <= (32'd0 ? 32'd104 : 32'd63);
        end
        32'd102: begin
          state <= 32'd103;
          reg_151 <= ( ~ reg_151);
          reg_150 <= 32'd1;
          reg_148 <= reg_66;
          reg_146 <= {{{reg_64 + 32'd0} + {reg_6 * 32'd4}} / 32'd4};
        end
        32'd101: begin
          state <= 32'd102;
          reg_151 <= ( ~ reg_151);
          reg_150 <= 32'd1;
          reg_148 <= reg_76;
          reg_146 <= {{{reg_74 + 32'd0} + {reg_6 * 32'd4}} / 32'd4};
        end
        32'd100: begin
          state <= 32'd101;
          reg_151 <= ( ~ reg_151);
          reg_150 <= 32'd1;
          reg_148 <= reg_86;
          reg_146 <= {{{reg_84 + 32'd0} + {reg_6 * 32'd4}} / 32'd4};
        end
        32'd99: begin
          reg_74 <= {{reg_80 + reg_82} + 32'd0};
          reg_72 <= reg_82;
          reg_64 <= {{reg_70 + reg_82} + 32'd0};
          state <= 32'd100;
        end
        32'd98: begin
          state <= 32'd99;
          reg_151 <= ( ~ reg_151);
          reg_150 <= 32'd1;
          reg_148 <= reg_96;
          reg_146 <= {{{reg_94 + 32'd0} + {reg_6 * 32'd4}} / 32'd4};
        end
        32'd97: begin
          reg_94 <= {{reg_100 + reg_102} + 32'd0};
          reg_92 <= reg_102;
          reg_82 <= reg_102;
          reg_84 <= {{reg_90 + reg_102} + 32'd0};
          state <= 32'd98;
        end
        32'd90: begin
          reg_8 <= 32'd0;
          state <= 32'd89;
          state <= (32'd0 ? 32'd105 : 32'd89);
        end
        32'd89: begin
          reg_6 <= 32'd0;
          state <= 32'd88;
          state <= (32'd0 ? 32'd109 : 32'd88);
        end
        32'd88: begin
          reg_100 <= 32'd120;
          reg_102 <= {reg_8 * 32'd120};
          reg_96 <= 32'd1065353216;
          reg_90 <= 32'd240;
          reg_86 <= 32'd1073741824;
          reg_80 <= 32'd360;
          reg_76 <= 32'd1077936128;
          reg_70 <= 32'd0;
          reg_66 <= 32'd1082130432;
          reg_4 <= 32'd0;
          state <= 32'd97;
        end
        32'd63: begin
          reg_60 <= 32'd480;
          reg_62 <= {reg_8 * 32'd3600};
          reg_58 <= {reg_6 * 32'd120};
          reg_52 <= 32'd1084227584;
          state <= 32'd156;
        end
        32'd51: begin
          reg_8 <= {reg_8 + 32'd1};
          reg_9 <= {$signed({reg_8 + 32'd1}) < $signed(32'd1)};
          state <= ({$signed({reg_8 + 32'd1}) < $signed(32'd1)} ? 32'd89 : state);
          reg_118 <= ({{$signed({reg_8 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd0 : reg_118);
          reg_112 <= ({{$signed({reg_8 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd480 : reg_112);
          reg_110 <= ({{$signed({reg_8 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd120 : reg_110);
          reg_108 <= ({{$signed({reg_8 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd240 : reg_108);
          reg_106 <= ({{$signed({reg_8 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd360 : reg_106);
          reg_104 <= ({{$signed({reg_8 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd0 : reg_104);
          state <= ({{$signed({reg_8 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd110 : ({$signed({reg_8 + 32'd1}) < $signed(32'd1)} ? 32'd89 : state));
        end
        32'd25: begin
          state <= 32'd197;
          reg_151 <= ( ~ reg_151);
          reg_150 <= 32'd0;
          reg_146 <= {{{reg_108 + 32'd0} + {reg_118 * 32'd4}} / 32'd4};
        end
        32'd23: begin
          reg_138 <= {reg_118 * 32'd120};
          state <= 32'd114;
        end
        32'd7: begin
          state <= 32'd216;
          reg_151 <= ( ~ reg_151);
          reg_150 <= 32'd0;
          reg_146 <= 32'd70;
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
