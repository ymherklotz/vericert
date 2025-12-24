`timescale 1ns / 1ps

module main(start, reset, clk, finish, return_val);
  logic [31:0] reg_128 = 0;
  logic [31:0] reg_64 = 0;
  logic [31:0] reg_96 = 0;
  logic [31:0] reg_144 = 0;
  logic [31:0] reg_80 = 0;
  logic [31:0] reg_112 = 0;
  logic [31:0] reg_8 = 0;
  logic [31:0] reg_136 = 0;
  logic [31:0] reg_72 = 0;
  logic [31:0] reg_104 = 0;
  logic [31:0] reg_88 = 0;
  logic [31:0] reg_56 = 0;
  logic [31:0] reg_120 = 0;
  logic [31:0] reg_4 = 0;
  logic [31:0] reg_132 = 0;
  logic [31:0] reg_68 = 0;
  logic [31:0] reg_100 = 0;
  logic [31:0] reg_148 = 0;
  logic [31:0] reg_84 = 0;
  logic [31:0] reg_52 = 0;
  logic [31:0] reg_12 = 0;
  logic [31:0] reg_76 = 0;
  logic [31:0] reg_108 = 0;
  logic [31:0] reg_92 = 0;
  logic [31:0] reg_60 = 0;
  logic [31:0] reg_124 = 0;
  logic [31:0] reg_130 = 0;
  logic [31:0] reg_66 = 0;
  logic [31:0] reg_98 = 0;
  logic [31:0] reg_146 = 0;
  logic [31:0] reg_82 = 0;
  logic [31:0] reg_50 = 0;
  logic [31:0] reg_114 = 0;
  logic [31:0] reg_10 = 0;
  logic [31:0] reg_74 = 0;
  logic [31:0] reg_106 = 0;
  logic [31:0] reg_90 = 0;
  logic [31:0] reg_58 = 0;
  logic [31:0] reg_122 = 0;
  logic [31:0] reg_6 = 0;
  logic [31:0] reg_134 = 0;
  logic [31:0] reg_70 = 0;
  logic [31:0] reg_102 = 0;
  logic [31:0] reg_86 = 0;
  logic [31:0] reg_54 = 0;
  logic [31:0] reg_118 = 0;
  logic [31:0] reg_78 = 0;
  logic [31:0] reg_110 = 0;
  logic [31:0] reg_94 = 0;
  logic [31:0] reg_62 = 0;
  logic [31:0] reg_126 = 0;
  logic [31:0] reg_17 = 0;
  logic [31:0] reg_145 = 0;
  logic [31:0] reg_9 = 0;
  logic [31:0] reg_5 = 0;
  logic [31:0] reg_149 = 0;
  logic [31:0] reg_13 = 0;
  logic [31:0] reg_147 = 0;
  logic [31:0] reg_11 = 0;
  logic [31:0] reg_7 = 0;
  logic [31:0] reg_15 = 0;
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
    if ({reg_149 != reg_145}) begin
      if (reg_148) begin
        stack[reg_144] <= reg_146;
      end else begin
        reg_147 <= stack[reg_144];
      end
      reg_145 <= reg_149;
    end else begin
    end
  end

  always @(posedge clk) begin
    if ({reset == 32'd1}) begin
      state <= 32'd92;
    end else begin
      case (state)
        32'd237: begin
          state <= 32'd170;
          reg_12 <= reg_147;
        end
        32'd229: begin
          state <= 32'd100;
          reg_132 <= reg_147;
        end
        32'd227: begin
          state <= 32'd132;
          reg_120 <= reg_147;
        end
        32'd220: begin
          state <= 32'd102;
          reg_130 <= reg_147;
        end
        32'd211: begin
          state <= 32'd130;
          reg_122 <= reg_147;
        end
        32'd190: begin
          state <= 32'd126;
          reg_112 <= reg_147;
        end
        32'd182: begin
          state <= 32'd122;
          reg_106 <= reg_147;
        end
        32'd170: begin
          reg_10 <= reg_12;
          finish <= 32'd1;
          return_val <= reg_12;
          state <= 32'd170;
          state <= (32'd0 ? 32'd171 : 32'd170);
        end
        32'd166: begin
          reg_9 <= ({reg_17 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_9);
          state <= ({{reg_17 == 32'd0} & ({reg_17 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_9)} ? 32'd90 : state);
          state <= ({{reg_17 | {({reg_17 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_9) == 32'd0}} & {{reg_17 == 32'd0} & {({reg_17 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_9) == 32'd0}}} ? 32'd58 : ({{reg_17 == 32'd0} & ({reg_17 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_9)} ? 32'd90 : state));
          state <= ({{reg_17 | {({reg_17 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_9) == 32'd0}} & {reg_17 | ({reg_17 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_9)}} ? 32'd167 : ({{reg_17 | {({reg_17 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_9) == 32'd0}} & {{reg_17 == 32'd0} & {({reg_17 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_9) == 32'd0}}} ? 32'd58 : ({{reg_17 == 32'd0} & ({reg_17 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_9)} ? 32'd90 : state)));
        end
        32'd165: begin
          reg_4 <= {reg_4 + 32'd1};
          reg_17 <= {$signed({reg_4 + 32'd1}) < $signed(32'd30)};
          state <= ({$signed({reg_4 + 32'd1}) < $signed(32'd30)} ? 32'd69 : state);
          reg_6 <= ({{$signed({reg_4 + 32'd1}) < $signed(32'd30)} == 32'd0} ? {reg_6 + 32'd1} : reg_6);
          state <= ({{$signed({reg_4 + 32'd1}) < $signed(32'd30)} == 32'd0} ? 32'd166 : ({$signed({reg_4 + 32'd1}) < $signed(32'd30)} ? 32'd69 : state));
        end
        32'd164: begin
          state <= 32'd165;
          reg_149 <= ( ~ reg_149);
          reg_148 <= 32'd1;
          reg_146 <= reg_52;
          reg_144 <= {{{reg_50 + 32'd0} + {reg_4 * 32'd4}} / 32'd4};
        end
        32'd163: begin
          reg_50 <= {{reg_54 + reg_56} + 32'd0};
          state <= 32'd164;
        end
        32'd162: begin
          reg_54 <= {{reg_58 + reg_60} + 32'd0};
          state <= 32'd163;
        end
        32'd160: begin
          state <= ({reg_15 == 32'd0} ? 32'd34 : state);
          state <= (reg_15 ? 32'd161 : ({reg_15 == 32'd0} ? 32'd34 : state));
        end
        32'd158: begin
          state <= 32'd69;
          state <= (32'd0 ? 32'd159 : 32'd69);
        end
        32'd157: begin
          state <= 32'd158;
          reg_149 <= ( ~ reg_149);
          reg_148 <= 32'd1;
          reg_146 <= reg_64;
          reg_144 <= {{{reg_62 + 32'd0} + {reg_6 * 32'd4}} / 32'd4};
        end
        32'd156: begin
          state <= 32'd157;
          reg_149 <= ( ~ reg_149);
          reg_148 <= 32'd1;
          reg_146 <= reg_72;
          reg_144 <= {{{reg_70 + 32'd0} + {reg_6 * 32'd4}} / 32'd4};
        end
        32'd155: begin
          state <= 32'd156;
          reg_149 <= ( ~ reg_149);
          reg_148 <= 32'd1;
          reg_146 <= reg_80;
          reg_144 <= {{{reg_78 + 32'd0} + {reg_6 * 32'd4}} / 32'd4};
        end
        32'd154: begin
          reg_70 <= {{reg_74 + reg_76} + 32'd0};
          reg_68 <= reg_76;
          reg_62 <= {{reg_66 + reg_76} + 32'd0};
          state <= 32'd155;
        end
        32'd153: begin
          state <= 32'd154;
          reg_149 <= ( ~ reg_149);
          reg_148 <= 32'd1;
          reg_146 <= reg_88;
          reg_144 <= {{{reg_86 + 32'd0} + {reg_6 * 32'd4}} / 32'd4};
        end
        32'd152: begin
          reg_86 <= {{reg_90 + reg_92} + 32'd0};
          reg_84 <= reg_92;
          reg_76 <= reg_92;
          reg_78 <= {{reg_82 + reg_92} + 32'd0};
          state <= 32'd153;
        end
        32'd150: begin
          reg_108 <= ({reg_11 == 32'd0} ? {reg_108 + 32'd1} : reg_108);
          reg_13 <= ({reg_11 == 32'd0} ? {$signed(({reg_11 == 32'd0} ? {reg_108 + 32'd1} : reg_108)) < $signed(32'd30)} : reg_13);
          state <= ({{reg_11 == 32'd0} & ({reg_11 == 32'd0} ? {$signed(({reg_11 == 32'd0} ? {reg_108 + 32'd1} : reg_108)) < $signed(32'd30)} : reg_13)} ? 32'd20 : state);
          state <= ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(({reg_11 == 32'd0} ? {reg_108 + 32'd1} : reg_108)) < $signed(32'd30)} : reg_13) == 32'd0}} & {{reg_11 == 32'd0} & {({reg_11 == 32'd0} ? {$signed(({reg_11 == 32'd0} ? {reg_108 + 32'd1} : reg_108)) < $signed(32'd30)} : reg_13) == 32'd0}}} ? 32'd7 : ({{reg_11 == 32'd0} & ({reg_11 == 32'd0} ? {$signed(({reg_11 == 32'd0} ? {reg_108 + 32'd1} : reg_108)) < $signed(32'd30)} : reg_13)} ? 32'd20 : state));
          state <= ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(({reg_11 == 32'd0} ? {reg_108 + 32'd1} : reg_108)) < $signed(32'd30)} : reg_13) == 32'd0}} & {reg_11 | ({reg_11 == 32'd0} ? {$signed(({reg_11 == 32'd0} ? {reg_108 + 32'd1} : reg_108)) < $signed(32'd30)} : reg_13)}} ? 32'd151 : ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(({reg_11 == 32'd0} ? {reg_108 + 32'd1} : reg_108)) < $signed(32'd30)} : reg_13) == 32'd0}} & {{reg_11 == 32'd0} & {({reg_11 == 32'd0} ? {$signed(({reg_11 == 32'd0} ? {reg_108 + 32'd1} : reg_108)) < $signed(32'd30)} : reg_13) == 32'd0}}} ? 32'd7 : ({{reg_11 == 32'd0} & ({reg_11 == 32'd0} ? {$signed(({reg_11 == 32'd0} ? {reg_108 + 32'd1} : reg_108)) < $signed(32'd30)} : reg_13)} ? 32'd20 : state)));
        end
        32'd149: begin
          reg_149 <= {( - {{32'd1 & {reg_11 == 32'd0}} != 32'd0}) ^ reg_149};
          reg_148 <= 32'd1;
          reg_146 <= ({32'd1 & {reg_11 == 32'd0}} ? reg_106 : reg_146);
          reg_144 <= ({32'd1 & {reg_11 == 32'd0}} ? {{{reg_98 + 32'd0} + {reg_108 * 32'd4}} / 32'd4} : reg_144);
          state <= 32'd150;
        end
        32'd148: begin
          state <= (reg_11 ? 32'd18 : state);
          state <= ({reg_11 == 32'd0} ? 32'd149 : (reg_11 ? 32'd18 : state));
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
          f_add_a <= reg_106;
          f_add_b <= reg_118;
          reg_106 <= f_add_res;
          state <= 32'd139;
        end
        32'd137: begin
          state <= 32'd138;
        end
        32'd136: begin
          state <= 32'd137;
        end
        32'd135: begin
          state <= 32'd136;
        end
        32'd134: begin
          state <= 32'd135;
        end
        32'd133: begin
          state <= 32'd134;
        end
        32'd132: begin
          f_mul_a <= reg_120;
          f_mul_b <= reg_122;
          reg_118 <= f_mul_res;
          state <= 32'd133;
        end
        32'd131: begin
          state <= 32'd227;
          reg_149 <= ( ~ reg_149);
          reg_148 <= 32'd0;
          reg_144 <= {{{reg_124 + 32'd0} + {reg_108 * 32'd4}} / 32'd4};
        end
        32'd130: begin
          reg_124 <= {{reg_102 + reg_126} + 32'd0};
          reg_104 <= {reg_104 + 32'd1};
          reg_11 <= {$signed({reg_104 + 32'd1}) < $signed(32'd30)};
          state <= 32'd131;
        end
        32'd129: begin
          state <= 32'd211;
          reg_149 <= ( ~ reg_149);
          reg_148 <= 32'd0;
          reg_144 <= {{{reg_94 + 32'd0} + {reg_104 * 32'd4}} / 32'd4};
        end
        32'd127: begin
          state <= 32'd32;
          state <= (32'd0 ? 32'd128 : 32'd32);
        end
        32'd126: begin
          reg_110 <= 32'd0;
          state <= 32'd127;
        end
        32'd123: begin
          state <= 32'd18;
          state <= (32'd0 ? 32'd124 : 32'd18);
        end
        32'd122: begin
          reg_104 <= 32'd0;
          state <= 32'd123;
        end
        32'd120: begin
          reg_114 <= ({reg_5 == 32'd0} ? {reg_114 + 32'd1} : reg_114);
          reg_7 <= ({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_114 + 32'd1} : reg_114)) < $signed(32'd30)} : reg_7);
          state <= ({{reg_5 == 32'd0} & ({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_114 + 32'd1} : reg_114)) < $signed(32'd30)} : reg_7)} ? 32'd34 : state);
          state <= ({{reg_5 | {({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_114 + 32'd1} : reg_114)) < $signed(32'd30)} : reg_7) == 32'd0}} & {{reg_5 == 32'd0} & {({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_114 + 32'd1} : reg_114)) < $signed(32'd30)} : reg_7) == 32'd0}}} ? 32'd21 : ({{reg_5 == 32'd0} & ({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_114 + 32'd1} : reg_114)) < $signed(32'd30)} : reg_7)} ? 32'd34 : state));
          state <= ({{reg_5 | {({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_114 + 32'd1} : reg_114)) < $signed(32'd30)} : reg_7) == 32'd0}} & {reg_5 | ({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_114 + 32'd1} : reg_114)) < $signed(32'd30)} : reg_7)}} ? 32'd121 : ({{reg_5 | {({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_114 + 32'd1} : reg_114)) < $signed(32'd30)} : reg_7) == 32'd0}} & {{reg_5 == 32'd0} & {({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_114 + 32'd1} : reg_114)) < $signed(32'd30)} : reg_7) == 32'd0}}} ? 32'd21 : ({{reg_5 == 32'd0} & ({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_114 + 32'd1} : reg_114)) < $signed(32'd30)} : reg_7)} ? 32'd34 : state)));
        end
        32'd119: begin
          reg_149 <= {( - {{32'd1 & {reg_5 == 32'd0}} != 32'd0}) ^ reg_149};
          reg_148 <= 32'd1;
          reg_146 <= ({32'd1 & {reg_5 == 32'd0}} ? reg_112 : reg_146);
          reg_144 <= ({32'd1 & {reg_5 == 32'd0}} ? {{{reg_100 + 32'd0} + {reg_114 * 32'd4}} / 32'd4} : reg_144);
          state <= 32'd120;
        end
        32'd118: begin
          state <= (reg_5 ? 32'd32 : state);
          state <= ({reg_5 == 32'd0} ? 32'd119 : (reg_5 ? 32'd32 : state));
        end
        32'd117: begin
          state <= 32'd118;
        end
        32'd116: begin
          state <= 32'd117;
        end
        32'd115: begin
          state <= 32'd116;
        end
        32'd114: begin
          state <= 32'd115;
        end
        32'd113: begin
          state <= 32'd114;
        end
        32'd112: begin
          state <= 32'd113;
        end
        32'd111: begin
          state <= 32'd112;
        end
        32'd110: begin
          state <= 32'd111;
        end
        32'd109: begin
          state <= 32'd110;
        end
        32'd108: begin
          f_add_a <= reg_112;
          f_add_b <= reg_128;
          reg_112 <= f_add_res;
          state <= 32'd109;
        end
        32'd107: begin
          state <= 32'd108;
        end
        32'd106: begin
          state <= 32'd107;
        end
        32'd105: begin
          state <= 32'd106;
        end
        32'd104: begin
          state <= 32'd105;
        end
        32'd103: begin
          state <= 32'd104;
        end
        32'd102: begin
          f_mul_a <= reg_130;
          f_mul_b <= reg_132;
          reg_128 <= f_mul_res;
          reg_110 <= {reg_110 + 32'd1};
          reg_5 <= {$signed({reg_110 + 32'd1}) < $signed(32'd30)};
          state <= 32'd103;
        end
        32'd101: begin
          state <= 32'd220;
          reg_149 <= ( ~ reg_149);
          reg_148 <= 32'd0;
          reg_144 <= {{{reg_134 + 32'd0} + {reg_110 * 32'd4}} / 32'd4};
        end
        32'd100: begin
          reg_134 <= {{reg_102 + reg_136} + 32'd0};
          state <= 32'd101;
        end
        32'd99: begin
          state <= 32'd229;
          reg_149 <= ( ~ reg_149);
          reg_148 <= 32'd0;
          reg_144 <= {{{reg_96 + 32'd0} + {reg_110 * 32'd4}} / 32'd4};
        end
        32'd92: begin
          reg_8 <= 32'd0;
          state <= 32'd91;
          state <= (32'd0 ? 32'd125 : 32'd91);
        end
        32'd91: begin
          reg_6 <= 32'd0;
          state <= 32'd90;
          state <= (32'd0 ? 32'd169 : 32'd90);
        end
        32'd90: begin
          reg_90 <= 32'd120;
          reg_92 <= {reg_8 * 32'd120};
          reg_88 <= 32'd1065353216;
          reg_82 <= 32'd240;
          reg_80 <= 32'd1073741824;
          reg_74 <= 32'd360;
          reg_72 <= 32'd1077936128;
          reg_66 <= 32'd0;
          reg_64 <= 32'd1082130432;
          reg_4 <= 32'd0;
          state <= 32'd152;
        end
        32'd69: begin
          reg_58 <= 32'd480;
          reg_60 <= {reg_8 * 32'd3600};
          reg_56 <= {reg_6 * 32'd120};
          reg_52 <= 32'd1084227584;
          state <= 32'd162;
        end
        32'd58: begin
          reg_8 <= {reg_8 + 32'd1};
          reg_15 <= {$signed({reg_8 + 32'd1}) < $signed(32'd1)};
          state <= ({$signed({reg_8 + 32'd1}) < $signed(32'd1)} ? 32'd91 : state);
          reg_114 <= ({{$signed({reg_8 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd0 : reg_114);
          reg_102 <= ({{$signed({reg_8 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd480 : reg_102);
          reg_100 <= ({{$signed({reg_8 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd120 : reg_100);
          reg_98 <= ({{$signed({reg_8 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd240 : reg_98);
          reg_96 <= ({{$signed({reg_8 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd360 : reg_96);
          reg_94 <= ({{$signed({reg_8 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd0 : reg_94);
          state <= ({{$signed({reg_8 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd160 : ({$signed({reg_8 + 32'd1}) < $signed(32'd1)} ? 32'd91 : state));
        end
        32'd34: begin
          state <= 32'd190;
          reg_149 <= ( ~ reg_149);
          reg_148 <= 32'd0;
          reg_144 <= {{{reg_100 + 32'd0} + {reg_114 * 32'd4}} / 32'd4};
        end
        32'd32: begin
          reg_136 <= {reg_114 * 32'd120};
          state <= 32'd99;
        end
        32'd21: begin
          reg_108 <= 32'd0;
          state <= 32'd20;
          state <= (32'd0 ? 32'd168 : 32'd20);
        end
        32'd20: begin
          state <= 32'd182;
          reg_149 <= ( ~ reg_149);
          reg_148 <= 32'd0;
          reg_144 <= {{{reg_98 + 32'd0} + {reg_108 * 32'd4}} / 32'd4};
        end
        32'd18: begin
          reg_126 <= {reg_104 * 32'd120};
          state <= 32'd129;
        end
        32'd7: begin
          state <= 32'd237;
          reg_149 <= ( ~ reg_149);
          reg_148 <= 32'd0;
          reg_144 <= 32'd100;
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
