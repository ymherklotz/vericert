`timescale 1ns / 1ps

module main(start, reset, clk, finish, return_val);
  logic [31:0] reg_128 = 0;
  logic [31:0] reg_64 = 0;
  logic [31:0] reg_192 = 0;
  logic [31:0] reg_32 = 0;
  logic [31:0] reg_160 = 0;
  logic [31:0] reg_96 = 0;
  logic [31:0] reg_16 = 0;
  logic [31:0] reg_144 = 0;
  logic [31:0] reg_80 = 0;
  logic [31:0] reg_48 = 0;
  logic [31:0] reg_176 = 0;
  logic [31:0] reg_112 = 0;
  logic [31:0] reg_8 = 0;
  logic [31:0] reg_136 = 0;
  logic [31:0] reg_72 = 0;
  logic [31:0] reg_168 = 0;
  logic [31:0] reg_104 = 0;
  logic [31:0] reg_24 = 0;
  logic [31:0] reg_152 = 0;
  logic [31:0] reg_88 = 0;
  logic [31:0] reg_56 = 0;
  logic [31:0] reg_120 = 0;
  logic [31:0] reg_4 = 0;
  logic [31:0] reg_132 = 0;
  logic [31:0] reg_68 = 0;
  logic [31:0] reg_100 = 0;
  logic [31:0] reg_20 = 0;
  logic [31:0] reg_148 = 0;
  logic [31:0] reg_84 = 0;
  logic [31:0] reg_180 = 0;
  logic [31:0] reg_116 = 0;
  logic [31:0] reg_12 = 0;
  logic [31:0] reg_76 = 0;
  logic [31:0] reg_108 = 0;
  logic [31:0] reg_28 = 0;
  logic [31:0] reg_92 = 0;
  logic [31:0] reg_124 = 0;
  logic [31:0] reg_2 = 0;
  logic [31:0] reg_130 = 0;
  logic [31:0] reg_66 = 0;
  logic [31:0] reg_194 = 0;
  logic [31:0] reg_162 = 0;
  logic [31:0] reg_98 = 0;
  logic [31:0] reg_18 = 0;
  logic [31:0] reg_146 = 0;
  logic [31:0] reg_82 = 0;
  logic [31:0] reg_114 = 0;
  logic [31:0] reg_10 = 0;
  logic [31:0] reg_138 = 0;
  logic [31:0] reg_74 = 0;
  logic [31:0] reg_170 = 0;
  logic [31:0] reg_106 = 0;
  logic [31:0] reg_154 = 0;
  logic [31:0] reg_90 = 0;
  logic [31:0] reg_122 = 0;
  logic [31:0] reg_6 = 0;
  logic [31:0] reg_134 = 0;
  logic [31:0] reg_70 = 0;
  logic [31:0] reg_166 = 0;
  logic [31:0] reg_102 = 0;
  logic [31:0] reg_22 = 0;
  logic [31:0] reg_150 = 0;
  logic [31:0] reg_86 = 0;
  logic [31:0] reg_54 = 0;
  logic [31:0] reg_182 = 0;
  logic [31:0] reg_118 = 0;
  logic [31:0] reg_14 = 0;
  logic [31:0] reg_142 = 0;
  logic [31:0] reg_78 = 0;
  logic [31:0] reg_46 = 0;
  logic [31:0] reg_174 = 0;
  logic [31:0] reg_110 = 0;
  logic [31:0] reg_30 = 0;
  logic [31:0] reg_158 = 0;
  logic [31:0] reg_94 = 0;
  logic [31:0] reg_62 = 0;
  logic [31:0] reg_190 = 0;
  logic [31:0] reg_126 = 0;
  logic [31:0] reg_193 = 0;
  logic [31:0] reg_9 = 0;
  logic [31:0] reg_5 = 0;
  logic [31:0] reg_13 = 0;
  logic [31:0] reg_195 = 0;
  logic [31:0] reg_11 = 0;
  logic [31:0] reg_7 = 0;
  logic [31:0] reg_191 = 0;
  (* ram_style = "block" *)
  logic [31:0] stack [3999:0];
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
    if ({reg_195 != reg_191}) begin
      if (reg_194) begin
        stack[reg_190] <= reg_192;
      end else begin
        reg_193 <= stack[reg_190];
      end
      reg_191 <= reg_195;
    end else begin
    end
  end

  always @(posedge clk) begin
    if ({reset == 32'd1}) begin
      state <= 32'd110;
    end else begin
      case (state)
        32'd295: begin
          state <= 32'd206;
          reg_180 <= reg_193;
        end
        32'd271: begin
          state <= 32'd204;
          reg_142 <= reg_193;
        end
        32'd220: begin
          state <= ({reg_9 == 32'd0} ? 32'd30 : state);
          state <= (reg_9 ? 32'd221 : ({reg_9 == 32'd0} ? 32'd30 : state));
        end
        32'd218: begin
          finish <= 32'd1;
          return_val <= reg_32;
          state <= 32'd218;
          state <= (32'd0 ? 32'd219 : 32'd218);
        end
        32'd216: begin
          reg_9 <= ({reg_13 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_9);
          state <= ({{reg_13 == 32'd0} & ({reg_13 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_9)} ? 32'd109 : state);
          reg_144 <= ({{reg_13 | {({reg_13 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_9) == 32'd0}} & {{reg_13 == 32'd0} & {({reg_13 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_9) == 32'd0}}} ? 32'd0 : reg_144);
          reg_138 <= ({{reg_13 | {({reg_13 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_9) == 32'd0}} & {{reg_13 == 32'd0} & {({reg_13 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_9) == 32'd0}}} ? 32'd0 : reg_138);
          reg_136 <= ({{reg_13 | {({reg_13 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_9) == 32'd0}} & {{reg_13 == 32'd0} & {({reg_13 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_9) == 32'd0}}} ? 32'd0 : reg_136);
          reg_134 <= ({{reg_13 | {({reg_13 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_9) == 32'd0}} & {{reg_13 == 32'd0} & {({reg_13 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_9) == 32'd0}}} ? 32'd4000 : reg_134);
          state <= ({{reg_13 | {({reg_13 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_9) == 32'd0}} & {{reg_13 == 32'd0} & {({reg_13 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_9) == 32'd0}}} ? 32'd30 : ({{reg_13 == 32'd0} & ({reg_13 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_9)} ? 32'd109 : state));
          state <= ({{reg_13 | {({reg_13 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_9) == 32'd0}} & {reg_13 | ({reg_13 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_9)}} ? 32'd217 : ({{reg_13 | {({reg_13 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_9) == 32'd0}} & {{reg_13 == 32'd0} & {({reg_13 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_9) == 32'd0}}} ? 32'd30 : ({{reg_13 == 32'd0} & ({reg_13 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_9)} ? 32'd109 : state)));
        end
        32'd215: begin
          reg_28 <= {reg_28 + 32'd1};
          reg_13 <= {$signed({reg_28 + 32'd1}) < $signed(32'd1000)};
          state <= ({$signed({reg_28 + 32'd1}) < $signed(32'd1000)} ? 32'd108 : state);
          reg_30 <= ({{$signed({reg_28 + 32'd1}) < $signed(32'd1000)} == 32'd0} ? {reg_30 + 32'd1} : reg_30);
          state <= ({{$signed({reg_28 + 32'd1}) < $signed(32'd1000)} == 32'd0} ? 32'd216 : ({$signed({reg_28 + 32'd1}) < $signed(32'd1000)} ? 32'd108 : state));
        end
        32'd214: begin
          state <= 32'd215;
          reg_195 <= ( ~ reg_195);
          reg_194 <= 32'd1;
          reg_192 <= reg_48;
          reg_190 <= {{{reg_46 + 32'd0} + {reg_28 * 32'd4}} / 32'd4};
        end
        32'd213: begin
          state <= 32'd214;
          reg_195 <= ( ~ reg_195);
          reg_194 <= 32'd1;
          reg_192 <= reg_56;
          reg_190 <= {{{reg_54 + 32'd0} + {reg_28 * 32'd4}} / 32'd4};
        end
        32'd211: begin
          state <= ({{reg_7 == 32'd0} & {reg_11 == 32'd0}} ? 32'd5 : state);
          state <= ({reg_7 | reg_11} ? 32'd212 : ({{reg_7 == 32'd0} & {reg_11 == 32'd0}} ? 32'd5 : state));
        end
        32'd210: begin
          state <= (reg_7 ? 32'd24 : state);
          reg_144 <= ({reg_7 == 32'd0} ? {reg_144 + 32'd1} : reg_144);
          reg_11 <= ({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_144 + 32'd1} : reg_144)) < $signed(32'd1000)} : reg_11);
          state <= ({{reg_7 == 32'd0} & {{reg_7 == 32'd0} & ({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_144 + 32'd1} : reg_144)) < $signed(32'd1000)} : reg_11)}} ? 32'd30 : (reg_7 ? 32'd24 : state));
          state <= ({{reg_7 == 32'd0} & {reg_7 | {({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_144 + 32'd1} : reg_144)) < $signed(32'd1000)} : reg_11) == 32'd0}}} ? 32'd211 : ({{reg_7 == 32'd0} & {{reg_7 == 32'd0} & ({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_144 + 32'd1} : reg_144)) < $signed(32'd1000)} : reg_11)}} ? 32'd30 : (reg_7 ? 32'd24 : state)));
        end
        32'd209: begin
          state <= 32'd210;
        end
        32'd208: begin
          state <= 32'd209;
        end
        32'd207: begin
          state <= 32'd208;
        end
        32'd206: begin
          reg_7 <= {$signed(reg_180) >= $signed(32'd0)};
          state <= 32'd207;
        end
        32'd205: begin
          state <= 32'd295;
          reg_195 <= ( ~ reg_195);
          reg_194 <= 32'd0;
          reg_190 <= {{{reg_134 + 32'd0} + {reg_144 * 32'd4}} / 32'd4};
        end
        32'd204: begin
          reg_182 <= 32'd1066192077;
          f_mul_a <= reg_138;
          f_mul_b <= 32'd1066192077;
          reg_138 <= f_mul_res;
          state <= 32'd205;
        end
        32'd201: begin
          state <= ({{reg_5 == 32'd0} & {reg_13 == 32'd0}} ? 32'd45 : state);
          state <= ({reg_5 | reg_13} ? 32'd202 : ({{reg_5 == 32'd0} & {reg_13 == 32'd0}} ? 32'd45 : state));
        end
        32'd200: begin
          state <= (reg_5 ? 32'd57 : state);
          reg_28 <= ({reg_5 == 32'd0} ? {reg_28 + 32'd1} : reg_28);
          reg_13 <= ({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_28 + 32'd1} : reg_28)) < $signed(32'd1000)} : reg_13);
          state <= ({{reg_5 == 32'd0} & {{reg_5 == 32'd0} & ({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_28 + 32'd1} : reg_28)) < $signed(32'd1000)} : reg_13)}} ? 32'd108 : (reg_5 ? 32'd57 : state));
          state <= ({{reg_5 == 32'd0} & {reg_5 | {({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_28 + 32'd1} : reg_28)) < $signed(32'd1000)} : reg_13) == 32'd0}}} ? 32'd201 : ({{reg_5 == 32'd0} & {{reg_5 == 32'd0} & ({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_28 + 32'd1} : reg_28)) < $signed(32'd1000)} : reg_13)}} ? 32'd108 : (reg_5 ? 32'd57 : state)));
        end
        32'd199: begin
          state <= 32'd200;
          reg_195 <= ( ~ reg_195);
          reg_194 <= 32'd1;
          reg_192 <= reg_104;
          reg_190 <= {{{reg_102 + 32'd0} + {reg_28 * 32'd4}} / 32'd4};
        end
        32'd198: begin
          state <= 32'd199;
          reg_195 <= ( ~ reg_195);
          reg_194 <= 32'd1;
          reg_192 <= reg_112;
          reg_190 <= {{{reg_110 + 32'd0} + {reg_28 * 32'd4}} / 32'd4};
        end
        32'd197: begin
          state <= 32'd198;
          reg_195 <= ( ~ reg_195);
          reg_194 <= 32'd1;
          reg_192 <= reg_120;
          reg_190 <= {{{reg_118 + 32'd0} + {reg_28 * 32'd4}} / 32'd4};
        end
        32'd196: begin
          reg_110 <= {{reg_114 + reg_116} + 32'd0};
          reg_108 <= reg_116;
          reg_102 <= {{reg_106 + reg_116} + 32'd0};
          reg_16 <= ({reg_14 != 32'd0} ? reg_70 : reg_72);
          reg_18 <= ({({reg_14 != 32'd0} ? reg_70 : reg_72) != 32'd0} ? reg_66 : reg_68);
          reg_20 <= ({({({reg_14 != 32'd0} ? reg_70 : reg_72) != 32'd0} ? reg_66 : reg_68) != 32'd0} ? reg_62 : reg_64);
          reg_5 <= {({({({reg_14 != 32'd0} ? reg_70 : reg_72) != 32'd0} ? reg_66 : reg_68) != 32'd0} ? reg_62 : reg_64) != 32'd0};
          state <= 32'd197;
        end
        32'd195: begin
          state <= 32'd196;
          reg_195 <= ( ~ reg_195);
          reg_194 <= 32'd1;
          reg_192 <= reg_128;
          reg_190 <= {{{reg_126 + 32'd0} + {reg_28 * 32'd4}} / 32'd4};
        end
        32'd194: begin
          reg_126 <= {{reg_130 + reg_132} + 32'd0};
          reg_124 <= reg_132;
          reg_116 <= reg_132;
          reg_118 <= {{reg_122 + reg_132} + 32'd0};
          reg_8 <= ({reg_6 != 32'd0} ? reg_86 : reg_88);
          reg_10 <= ({({reg_6 != 32'd0} ? reg_86 : reg_88) != 32'd0} ? reg_82 : reg_84);
          reg_12 <= ({({({reg_6 != 32'd0} ? reg_86 : reg_88) != 32'd0} ? reg_82 : reg_84) != 32'd0} ? reg_78 : reg_80);
          reg_14 <= ({({({({reg_6 != 32'd0} ? reg_86 : reg_88) != 32'd0} ? reg_82 : reg_84) != 32'd0} ? reg_78 : reg_80) != 32'd0} ? reg_74 : reg_76);
          state <= 32'd195;
        end
        32'd192: begin
          reg_32 <= ({reg_11 == 32'd0} ? reg_24 : reg_32);
          finish <= ({reg_11 == 32'd0} ? 32'd1 : finish);
          return_val <= ({reg_11 == 32'd0} ? ({reg_11 == 32'd0} ? reg_24 : reg_32) : return_val);
          state <= ({reg_11 == 32'd0} ? 32'd192 : state);
          state <= (reg_11 ? 32'd193 : ({reg_11 == 32'd0} ? 32'd192 : state));
        end
        32'd191: begin
          state <= (reg_11 ? 32'd30 : state);
          reg_146 <= ({reg_11 == 32'd0} ? reg_138 : reg_146);
          reg_22 <= ({reg_11 == 32'd0} ? ({reg_11 == 32'd0} ? reg_138 : reg_146) : reg_22);
          reg_24 <= ({reg_11 == 32'd0} ? ({reg_11 == 32'd0} ? ({reg_11 == 32'd0} ? reg_138 : reg_146) : reg_22) : reg_24);
          state <= ({reg_11 == 32'd0} ? 32'd192 : (reg_11 ? 32'd30 : state));
        end
        32'd190: begin
          state <= 32'd191;
        end
        32'd189: begin
          state <= 32'd190;
        end
        32'd188: begin
          state <= 32'd189;
        end
        32'd187: begin
          state <= 32'd188;
        end
        32'd186: begin
          state <= 32'd187;
        end
        32'd185: begin
          state <= 32'd186;
        end
        32'd184: begin
          state <= 32'd185;
        end
        32'd183: begin
          state <= 32'd184;
        end
        32'd182: begin
          state <= 32'd183;
        end
        32'd181: begin
          f_add_a <= reg_138;
          f_add_b <= reg_148;
          reg_138 <= f_add_res;
          state <= 32'd182;
        end
        32'd180: begin
          state <= 32'd181;
        end
        32'd179: begin
          state <= 32'd180;
        end
        32'd178: begin
          state <= 32'd179;
        end
        32'd177: begin
          state <= 32'd178;
        end
        32'd176: begin
          state <= 32'd177;
        end
        32'd175: begin
          f_mul_a <= reg_150;
          f_mul_b <= reg_142;
          reg_148 <= f_mul_res;
          state <= 32'd176;
        end
        32'd174: begin
          state <= 32'd175;
        end
        32'd173: begin
          state <= 32'd174;
        end
        32'd172: begin
          state <= 32'd173;
        end
        32'd171: begin
          state <= 32'd172;
        end
        32'd170: begin
          state <= 32'd171;
        end
        32'd169: begin
          state <= 32'd170;
        end
        32'd168: begin
          state <= 32'd169;
        end
        32'd167: begin
          state <= 32'd168;
        end
        32'd166: begin
          state <= 32'd167;
        end
        32'd165: begin
          f_add_a <= reg_152;
          f_add_b <= reg_154;
          reg_150 <= f_add_res;
          state <= 32'd166;
        end
        32'd164: begin
          state <= 32'd165;
        end
        32'd163: begin
          state <= 32'd164;
        end
        32'd162: begin
          state <= 32'd163;
        end
        32'd161: begin
          state <= 32'd162;
        end
        32'd160: begin
          state <= 32'd161;
        end
        32'd159: begin
          f_mul_a <= reg_158;
          f_mul_b <= reg_142;
          reg_152 <= f_mul_res;
          state <= 32'd160;
        end
        32'd158: begin
          state <= 32'd159;
        end
        32'd157: begin
          state <= 32'd158;
        end
        32'd156: begin
          state <= 32'd157;
        end
        32'd155: begin
          state <= 32'd156;
        end
        32'd154: begin
          state <= 32'd155;
        end
        32'd153: begin
          state <= 32'd154;
        end
        32'd152: begin
          state <= 32'd153;
        end
        32'd151: begin
          state <= 32'd152;
        end
        32'd150: begin
          state <= 32'd151;
        end
        32'd149: begin
          f_add_a <= reg_160;
          f_add_b <= reg_162;
          reg_158 <= f_add_res;
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
          f_mul_a <= reg_166;
          f_mul_b <= reg_142;
          reg_160 <= f_mul_res;
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
          f_add_a <= reg_168;
          f_add_b <= reg_170;
          reg_166 <= f_add_res;
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
          f_mul_a <= reg_174;
          f_mul_b <= reg_142;
          reg_168 <= f_mul_res;
          state <= 32'd128;
        end
        32'd126: begin
          state <= 32'd127;
        end
        32'd125: begin
          state <= 32'd126;
        end
        32'd124: begin
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
          state <= 32'd119;
        end
        32'd110: begin
          reg_30 <= 32'd0;
          state <= 32'd109;
          state <= (32'd0 ? 32'd203 : 32'd109);
        end
        32'd109: begin
          reg_28 <= 32'd0;
          state <= 32'd108;
          state <= (32'd0 ? 32'd222 : 32'd108);
        end
        32'd108: begin
          reg_130 <= 32'd0;
          reg_132 <= {reg_30 * 32'd4000};
          reg_128 <= 32'd1065353216;
          reg_122 <= 32'd8000;
          reg_120 <= 32'd1073741824;
          reg_114 <= 32'd12000;
          reg_112 <= 32'd1077936128;
          reg_106 <= 32'd4000;
          reg_104 <= (- 32'd1);
          reg_98 <= 32'd1;
          reg_100 <= {reg_28 == 32'd100};
          reg_94 <= 32'd1;
          reg_96 <= {reg_28 == 32'd200};
          reg_90 <= 32'd1;
          reg_92 <= {reg_28 == 32'd300};
          reg_2 <= ({reg_28 == 32'd0} ? 32'd1 : {reg_28 == 32'd100});
          reg_4 <= ({({reg_28 == 32'd0} ? 32'd1 : {reg_28 == 32'd100}) != 32'd0} ? 32'd1 : {reg_28 == 32'd200});
          reg_6 <= ({({({reg_28 == 32'd0} ? 32'd1 : {reg_28 == 32'd100}) != 32'd0} ? 32'd1 : {reg_28 == 32'd200}) != 32'd0} ? 32'd1 : {reg_28 == 32'd300});
          reg_86 <= 32'd1;
          reg_88 <= {reg_28 == 32'd400};
          reg_82 <= 32'd1;
          reg_84 <= {reg_28 == 32'd500};
          reg_78 <= 32'd1;
          reg_80 <= {reg_28 == 32'd600};
          reg_74 <= 32'd1;
          reg_76 <= {reg_28 == 32'd700};
          reg_70 <= 32'd1;
          reg_72 <= {reg_28 == 32'd800};
          reg_66 <= 32'd1;
          reg_68 <= {reg_28 == 32'd900};
          reg_62 <= 32'd1;
          reg_64 <= {reg_28 == 32'd1000};
          state <= 32'd194;
        end
        32'd57: begin
          reg_54 <= reg_126;
          reg_56 <= 32'd1082130432;
          reg_46 <= reg_102;
          reg_48 <= 32'd1;
          state <= 32'd213;
        end
        32'd45: begin
          reg_30 <= {reg_30 + 32'd1};
          reg_9 <= {$signed({reg_30 + 32'd1}) < $signed(32'd1)};
          state <= ({$signed({reg_30 + 32'd1}) < $signed(32'd1)} ? 32'd109 : state);
          reg_144 <= ({{$signed({reg_30 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd0 : reg_144);
          reg_138 <= ({{$signed({reg_30 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd0 : reg_138);
          reg_136 <= ({{$signed({reg_30 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd0 : reg_136);
          reg_134 <= ({{$signed({reg_30 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd4000 : reg_134);
          state <= ({{$signed({reg_30 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd220 : ({$signed({reg_30 + 32'd1}) < $signed(32'd1)} ? 32'd109 : state));
        end
        32'd30: begin
          state <= 32'd271;
          reg_195 <= ( ~ reg_195);
          reg_194 <= 32'd0;
          reg_190 <= {{{reg_136 + 32'd0} + {reg_144 * 32'd4}} / 32'd4};
        end
        32'd24: begin
          reg_176 <= 32'd1059313418;
          f_add_a <= reg_142;
          f_add_b <= 32'd1059313418;
          reg_174 <= f_add_res;
          reg_170 <= 32'd1060320051;
          reg_162 <= 32'd1045891645;
          reg_154 <= 32'd1051260355;
          reg_144 <= {reg_144 + 32'd1};
          reg_11 <= {$signed({reg_144 + 32'd1}) < $signed(32'd1000)};
          state <= 32'd118;
        end
        32'd5: begin
          reg_146 <= reg_138;
          reg_22 <= reg_138;
          reg_24 <= reg_138;
          reg_32 <= reg_138;
          state <= 32'd218;
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
