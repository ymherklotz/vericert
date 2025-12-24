`timescale 1ns / 1ps

module main(start, reset, clk, finish, return_val);
  logic [31:0] reg_128 = 0;
  logic [31:0] reg_192 = 0;
  logic [31:0] reg_32 = 0;
  logic [31:0] reg_160 = 0;
  logic [31:0] reg_96 = 0;
  logic [31:0] reg_16 = 0;
  logic [31:0] reg_144 = 0;
  logic [31:0] reg_80 = 0;
  logic [31:0] reg_176 = 0;
  logic [31:0] reg_112 = 0;
  logic [31:0] reg_8 = 0;
  logic [31:0] reg_136 = 0;
  logic [31:0] reg_200 = 0;
  logic [31:0] reg_168 = 0;
  logic [31:0] reg_104 = 0;
  logic [31:0] reg_24 = 0;
  logic [31:0] reg_152 = 0;
  logic [31:0] reg_88 = 0;
  logic [31:0] reg_216 = 0;
  logic [31:0] reg_184 = 0;
  logic [31:0] reg_120 = 0;
  logic [31:0] reg_4 = 0;
  logic [31:0] reg_132 = 0;
  logic [31:0] reg_68 = 0;
  logic [31:0] reg_164 = 0;
  logic [31:0] reg_100 = 0;
  logic [31:0] reg_20 = 0;
  logic [31:0] reg_148 = 0;
  logic [31:0] reg_84 = 0;
  logic [31:0] reg_116 = 0;
  logic [31:0] reg_12 = 0;
  logic [31:0] reg_140 = 0;
  logic [31:0] reg_76 = 0;
  logic [31:0] reg_204 = 0;
  logic [31:0] reg_172 = 0;
  logic [31:0] reg_108 = 0;
  logic [31:0] reg_28 = 0;
  logic [31:0] reg_156 = 0;
  logic [31:0] reg_92 = 0;
  logic [31:0] reg_60 = 0;
  logic [31:0] reg_124 = 0;
  logic [31:0] reg_2 = 0;
  logic [31:0] reg_130 = 0;
  logic [31:0] reg_194 = 0;
  logic [31:0] reg_34 = 0;
  logic [31:0] reg_162 = 0;
  logic [31:0] reg_98 = 0;
  logic [31:0] reg_18 = 0;
  logic [31:0] reg_146 = 0;
  logic [31:0] reg_82 = 0;
  logic [31:0] reg_178 = 0;
  logic [31:0] reg_114 = 0;
  logic [31:0] reg_10 = 0;
  logic [31:0] reg_138 = 0;
  logic [31:0] reg_106 = 0;
  logic [31:0] reg_154 = 0;
  logic [31:0] reg_90 = 0;
  logic [31:0] reg_218 = 0;
  logic [31:0] reg_186 = 0;
  logic [31:0] reg_122 = 0;
  logic [31:0] reg_6 = 0;
  logic [31:0] reg_134 = 0;
  logic [31:0] reg_70 = 0;
  logic [31:0] reg_198 = 0;
  logic [31:0] reg_166 = 0;
  logic [31:0] reg_102 = 0;
  logic [31:0] reg_22 = 0;
  logic [31:0] reg_150 = 0;
  logic [31:0] reg_86 = 0;
  logic [31:0] reg_214 = 0;
  logic [31:0] reg_182 = 0;
  logic [31:0] reg_118 = 0;
  logic [31:0] reg_14 = 0;
  logic [31:0] reg_142 = 0;
  logic [31:0] reg_78 = 0;
  logic [31:0] reg_206 = 0;
  logic [31:0] reg_174 = 0;
  logic [31:0] reg_110 = 0;
  logic [31:0] reg_30 = 0;
  logic [31:0] reg_158 = 0;
  logic [31:0] reg_94 = 0;
  logic [31:0] reg_62 = 0;
  logic [31:0] reg_190 = 0;
  logic [31:0] reg_126 = 0;
  logic [31:0] reg_9 = 0;
  logic [31:0] reg_217 = 0;
  logic [31:0] reg_5 = 0;
  logic [31:0] reg_13 = 0;
  logic [31:0] reg_11 = 0;
  logic [31:0] reg_219 = 0;
  logic [31:0] reg_7 = 0;
  logic [31:0] reg_215 = 0;
  logic [31:0] reg_15 = 0;
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
    if ({reg_219 != reg_215}) begin
      if (reg_218) begin
        stack[reg_214] <= reg_216;
      end else begin
        reg_217 <= stack[reg_214];
      end
      reg_215 <= reg_219;
    end else begin
    end
  end

  always @(posedge clk) begin
    if ({reset == 32'd1}) begin
      state <= 32'd126;
    end else begin
      case (state)
        32'd332: begin
          state <= 32'd228;
          reg_34 <= ({{reg_5 == 32'd0} & {reg_9 == 32'd0}} ? reg_217 : reg_34);
        end
        32'd330: begin
          state <= 32'd236;
          reg_166 <= reg_217;
        end
        32'd322: begin
          state <= 32'd238;
          reg_204 <= reg_217;
        end
        32'd275: begin
          state <= 32'd147;
          reg_34 <= ({reg_9 == 32'd0} ? reg_217 : reg_34);
        end
        32'd245: begin
          state <= ({reg_15 == 32'd0} ? 32'd38 : state);
          state <= (reg_15 ? 32'd246 : ({reg_15 == 32'd0} ? 32'd38 : state));
        end
        32'd243: begin
          state <= ({{reg_13 == 32'd0} & {reg_5 == 32'd0}} ? 32'd10 : state);
          state <= ({reg_13 | reg_5} ? 32'd244 : ({{reg_13 == 32'd0} & {reg_5 == 32'd0}} ? 32'd10 : state));
        end
        32'd242: begin
          state <= (reg_13 ? 32'd29 : state);
          reg_168 <= ({reg_13 == 32'd0} ? {reg_168 + 32'd1} : reg_168);
          reg_5 <= ({reg_13 == 32'd0} ? {$signed(({reg_13 == 32'd0} ? {reg_168 + 32'd1} : reg_168)) < $signed(32'd1000)} : reg_5);
          state <= ({{reg_13 == 32'd0} & {{reg_13 == 32'd0} & ({reg_13 == 32'd0} ? {$signed(({reg_13 == 32'd0} ? {reg_168 + 32'd1} : reg_168)) < $signed(32'd1000)} : reg_5)}} ? 32'd35 : (reg_13 ? 32'd29 : state));
          state <= ({{reg_13 == 32'd0} & {reg_13 | {({reg_13 == 32'd0} ? {$signed(({reg_13 == 32'd0} ? {reg_168 + 32'd1} : reg_168)) < $signed(32'd1000)} : reg_5) == 32'd0}}} ? 32'd243 : ({{reg_13 == 32'd0} & {{reg_13 == 32'd0} & ({reg_13 == 32'd0} ? {$signed(({reg_13 == 32'd0} ? {reg_168 + 32'd1} : reg_168)) < $signed(32'd1000)} : reg_5)}} ? 32'd35 : (reg_13 ? 32'd29 : state)));
        end
        32'd241: begin
          state <= 32'd242;
        end
        32'd240: begin
          state <= 32'd241;
        end
        32'd239: begin
          state <= 32'd240;
        end
        32'd238: begin
          reg_13 <= {$signed(reg_204) >= $signed(32'd0)};
          state <= 32'd239;
        end
        32'd237: begin
          state <= 32'd322;
          reg_219 <= ( ~ reg_219);
          reg_218 <= 32'd0;
          reg_214 <= {{{reg_158 + 32'd0} + {reg_168 * 32'd4}} / 32'd4};
        end
        32'd236: begin
          reg_206 <= 32'd1066192077;
          f_mul_a <= reg_162;
          f_mul_b <= 32'd1066192077;
          reg_162 <= f_mul_res;
          state <= 32'd237;
        end
        32'd234: begin
          reg_15 <= ({reg_11 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_15);
          state <= ({{reg_11 == 32'd0} & ({reg_11 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_15)} ? 32'd125 : state);
          reg_164 <= ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_15) == 32'd0}} & {{reg_11 == 32'd0} & {({reg_11 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_15) == 32'd0}}} ? 32'd0 : reg_164);
          reg_160 <= ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_15) == 32'd0}} & {{reg_11 == 32'd0} & {({reg_11 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_15) == 32'd0}}} ? 32'd0 : reg_160);
          reg_158 <= ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_15) == 32'd0}} & {{reg_11 == 32'd0} & {({reg_11 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_15) == 32'd0}}} ? 32'd4000 : reg_158);
          reg_156 <= ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_15) == 32'd0}} & {{reg_11 == 32'd0} & {({reg_11 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_15) == 32'd0}}} ? 32'd12000 : reg_156);
          state <= ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_15) == 32'd0}} & {{reg_11 == 32'd0} & {({reg_11 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_15) == 32'd0}}} ? 32'd38 : ({{reg_11 == 32'd0} & ({reg_11 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_15)} ? 32'd125 : state));
          state <= ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_15) == 32'd0}} & {reg_11 | ({reg_11 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_15)}} ? 32'd235 : ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_15) == 32'd0}} & {{reg_11 == 32'd0} & {({reg_11 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_15) == 32'd0}}} ? 32'd38 : ({{reg_11 == 32'd0} & ({reg_11 == 32'd0} ? {$signed(reg_30) < $signed(32'd1)} : reg_15)} ? 32'd125 : state)));
        end
        32'd233: begin
          reg_28 <= {reg_28 + 32'd1};
          reg_11 <= {$signed({reg_28 + 32'd1}) < $signed(32'd1000)};
          state <= ({$signed({reg_28 + 32'd1}) < $signed(32'd1000)} ? 32'd124 : state);
          reg_30 <= ({{$signed({reg_28 + 32'd1}) < $signed(32'd1000)} == 32'd0} ? {reg_30 + 32'd1} : reg_30);
          state <= ({{$signed({reg_28 + 32'd1}) < $signed(32'd1000)} == 32'd0} ? 32'd234 : ({$signed({reg_28 + 32'd1}) < $signed(32'd1000)} ? 32'd124 : state));
        end
        32'd232: begin
          state <= 32'd233;
          reg_219 <= ( ~ reg_219);
          reg_218 <= 32'd1;
          reg_216 <= reg_62;
          reg_214 <= {{{reg_60 + 32'd0} + {reg_28 * 32'd4}} / 32'd4};
        end
        32'd231: begin
          state <= 32'd232;
          reg_219 <= ( ~ reg_219);
          reg_218 <= 32'd1;
          reg_216 <= reg_70;
          reg_214 <= {{{reg_68 + 32'd0} + {reg_28 * 32'd4}} / 32'd4};
        end
        32'd228: begin
          reg_32 <= ({{reg_5 == 32'd0} & {reg_9 == 32'd0}} ? reg_34 : reg_32);
          finish <= ({{reg_5 == 32'd0} & {reg_9 == 32'd0}} ? 32'd1 : finish);
          return_val <= ({{reg_5 == 32'd0} & {reg_9 == 32'd0}} ? ({{reg_5 == 32'd0} & {reg_9 == 32'd0}} ? reg_34 : reg_32) : return_val);
          state <= ({{reg_5 == 32'd0} & {reg_9 == 32'd0}} ? 32'd228 : state);
          state <= ({reg_5 | reg_9} ? 32'd229 : ({{reg_5 == 32'd0} & {reg_9 == 32'd0}} ? 32'd228 : state));
        end
        32'd227: begin
          state <= 32'd332;
          reg_219 <= {( - {{{reg_5 == 32'd0} & {reg_9 == 32'd0}} != 32'd0}) ^ reg_219};
          reg_218 <= 32'd0;
          reg_214 <= ({{reg_5 == 32'd0} & {reg_9 == 32'd0}} ? 32'd3010 : reg_214);
        end
        32'd226: begin
          reg_164 <= ({reg_5 == 32'd0} ? {reg_164 + 32'd1} : reg_164);
          reg_9 <= ({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_164 + 32'd1} : reg_164)) < $signed(32'd10)} : reg_9);
          state <= ({{reg_5 == 32'd0} & ({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_164 + 32'd1} : reg_164)) < $signed(32'd10)} : reg_9)} ? 32'd38 : state);
          state <= ({reg_5 | {({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_164 + 32'd1} : reg_164)) < $signed(32'd10)} : reg_9) == 32'd0}} ? 32'd227 : ({{reg_5 == 32'd0} & ({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_164 + 32'd1} : reg_164)) < $signed(32'd10)} : reg_9)} ? 32'd38 : state));
        end
        32'd225: begin
          reg_219 <= {( - {{32'd1 & {reg_5 == 32'd0}} != 32'd0}) ^ reg_219};
          reg_218 <= 32'd1;
          reg_216 <= ({32'd1 & {reg_5 == 32'd0}} ? reg_162 : reg_216);
          reg_214 <= ({32'd1 & {reg_5 == 32'd0}} ? {{{reg_156 + 32'd0} + {reg_164 * 32'd4}} / 32'd4} : reg_214);
          state <= 32'd226;
        end
        32'd224: begin
          state <= (reg_5 ? 32'd35 : state);
          state <= ({reg_5 == 32'd0} ? 32'd225 : (reg_5 ? 32'd35 : state));
        end
        32'd223: begin
          state <= 32'd224;
        end
        32'd222: begin
          state <= 32'd223;
        end
        32'd221: begin
          state <= 32'd222;
        end
        32'd220: begin
          state <= 32'd221;
        end
        32'd219: begin
          state <= 32'd220;
        end
        32'd218: begin
          state <= 32'd219;
        end
        32'd217: begin
          state <= 32'd218;
        end
        32'd216: begin
          state <= 32'd217;
        end
        32'd215: begin
          state <= 32'd216;
        end
        32'd214: begin
          f_add_a <= reg_162;
          f_add_b <= reg_172;
          reg_162 <= f_add_res;
          state <= 32'd215;
        end
        32'd213: begin
          state <= 32'd214;
        end
        32'd212: begin
          state <= 32'd213;
        end
        32'd211: begin
          state <= 32'd212;
        end
        32'd210: begin
          state <= 32'd211;
        end
        32'd209: begin
          state <= 32'd210;
        end
        32'd208: begin
          f_mul_a <= reg_174;
          f_mul_b <= reg_166;
          reg_172 <= f_mul_res;
          state <= 32'd209;
        end
        32'd207: begin
          state <= 32'd208;
        end
        32'd206: begin
          state <= 32'd207;
        end
        32'd205: begin
          state <= 32'd206;
        end
        32'd204: begin
          state <= 32'd205;
        end
        32'd203: begin
          state <= 32'd204;
        end
        32'd202: begin
          state <= 32'd203;
        end
        32'd201: begin
          state <= 32'd202;
        end
        32'd200: begin
          state <= 32'd201;
        end
        32'd199: begin
          state <= 32'd200;
        end
        32'd198: begin
          f_add_a <= reg_176;
          f_add_b <= reg_178;
          reg_174 <= f_add_res;
          state <= 32'd199;
        end
        32'd197: begin
          state <= 32'd198;
        end
        32'd196: begin
          state <= 32'd197;
        end
        32'd195: begin
          state <= 32'd196;
        end
        32'd194: begin
          state <= 32'd195;
        end
        32'd193: begin
          state <= 32'd194;
        end
        32'd192: begin
          f_mul_a <= reg_182;
          f_mul_b <= reg_166;
          reg_176 <= f_mul_res;
          state <= 32'd193;
        end
        32'd191: begin
          state <= 32'd192;
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
          f_add_a <= reg_184;
          f_add_b <= reg_186;
          reg_182 <= f_add_res;
          state <= 32'd183;
        end
        32'd181: begin
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
          f_mul_a <= reg_190;
          f_mul_b <= reg_166;
          reg_184 <= f_mul_res;
          state <= 32'd177;
        end
        32'd175: begin
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
          f_add_a <= reg_192;
          f_add_b <= reg_194;
          reg_190 <= f_add_res;
          state <= 32'd167;
        end
        32'd165: begin
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
          f_mul_a <= reg_198;
          f_mul_b <= reg_166;
          reg_192 <= f_mul_res;
          state <= 32'd161;
        end
        32'd159: begin
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
        32'd147: begin
          reg_32 <= ({reg_9 == 32'd0} ? reg_34 : reg_32);
          finish <= ({reg_9 == 32'd0} ? 32'd1 : finish);
          return_val <= ({reg_9 == 32'd0} ? ({reg_9 == 32'd0} ? reg_34 : reg_32) : return_val);
          state <= ({reg_9 == 32'd0} ? 32'd147 : state);
          state <= (reg_9 ? 32'd148 : ({reg_9 == 32'd0} ? 32'd147 : state));
        end
        32'd146: begin
          state <= 32'd275;
          reg_219 <= {( - {{reg_9 == 32'd0} != 32'd0}) ^ reg_219};
          reg_218 <= 32'd0;
          reg_214 <= ({reg_9 == 32'd0} ? 32'd3010 : reg_214);
        end
        32'd145: begin
          reg_164 <= {reg_164 + 32'd1};
          reg_9 <= {$signed({reg_164 + 32'd1}) < $signed(32'd10)};
          state <= ({$signed({reg_164 + 32'd1}) < $signed(32'd10)} ? 32'd38 : state);
          state <= ({{$signed({reg_164 + 32'd1}) < $signed(32'd10)} == 32'd0} ? 32'd146 : ({$signed({reg_164 + 32'd1}) < $signed(32'd10)} ? 32'd38 : state));
        end
        32'd143: begin
          state <= ({{reg_7 == 32'd0} & {reg_11 == 32'd0}} ? 32'd55 : state);
          state <= ({reg_7 | reg_11} ? 32'd144 : ({{reg_7 == 32'd0} & {reg_11 == 32'd0}} ? 32'd55 : state));
        end
        32'd142: begin
          state <= (reg_7 ? 32'd67 : state);
          reg_28 <= ({reg_7 == 32'd0} ? {reg_28 + 32'd1} : reg_28);
          reg_11 <= ({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_28 + 32'd1} : reg_28)) < $signed(32'd1000)} : reg_11);
          state <= ({{reg_7 == 32'd0} & {{reg_7 == 32'd0} & ({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_28 + 32'd1} : reg_28)) < $signed(32'd1000)} : reg_11)}} ? 32'd124 : (reg_7 ? 32'd67 : state));
          state <= ({{reg_7 == 32'd0} & {reg_7 | {({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_28 + 32'd1} : reg_28)) < $signed(32'd1000)} : reg_11) == 32'd0}}} ? 32'd143 : ({{reg_7 == 32'd0} & {{reg_7 == 32'd0} & ({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_28 + 32'd1} : reg_28)) < $signed(32'd1000)} : reg_11)}} ? 32'd124 : (reg_7 ? 32'd67 : state)));
        end
        32'd141: begin
          state <= 32'd142;
          reg_219 <= ( ~ reg_219);
          reg_218 <= 32'd1;
          reg_216 <= reg_126;
          reg_214 <= {{{reg_124 + 32'd0} + {reg_28 * 32'd4}} / 32'd4};
        end
        32'd140: begin
          state <= 32'd141;
          reg_219 <= ( ~ reg_219);
          reg_218 <= 32'd1;
          reg_216 <= reg_134;
          reg_214 <= {{{reg_132 + 32'd0} + {reg_28 * 32'd4}} / 32'd4};
        end
        32'd139: begin
          reg_24 <= ({reg_22 != 32'd0} ? reg_76 : reg_78);
          reg_7 <= {({reg_22 != 32'd0} ? reg_76 : reg_78) != 32'd0};
          state <= 32'd140;
        end
        32'd138: begin
          state <= 32'd139;
          reg_219 <= ( ~ reg_219);
          reg_218 <= 32'd1;
          reg_216 <= reg_142;
          reg_214 <= {{{reg_140 + 32'd0} + {reg_28 * 32'd4}} / 32'd4};
        end
        32'd137: begin
          reg_132 <= {{reg_136 + reg_138} + 32'd0};
          reg_130 <= reg_138;
          reg_124 <= {{reg_128 + reg_138} + 32'd0};
          reg_16 <= ({reg_14 != 32'd0} ? reg_92 : reg_94);
          reg_18 <= ({({reg_14 != 32'd0} ? reg_92 : reg_94) != 32'd0} ? reg_88 : reg_90);
          reg_20 <= ({({({reg_14 != 32'd0} ? reg_92 : reg_94) != 32'd0} ? reg_88 : reg_90) != 32'd0} ? reg_84 : reg_86);
          reg_22 <= ({({({({reg_14 != 32'd0} ? reg_92 : reg_94) != 32'd0} ? reg_88 : reg_90) != 32'd0} ? reg_84 : reg_86) != 32'd0} ? reg_80 : reg_82);
          state <= 32'd138;
        end
        32'd136: begin
          state <= 32'd137;
          reg_219 <= ( ~ reg_219);
          reg_218 <= 32'd1;
          reg_216 <= reg_150;
          reg_214 <= {{{reg_148 + 32'd0} + {reg_28 * 32'd4}} / 32'd4};
        end
        32'd135: begin
          reg_148 <= {{reg_152 + reg_154} + 32'd0};
          reg_146 <= reg_154;
          reg_138 <= reg_154;
          reg_140 <= {{reg_144 + reg_154} + 32'd0};
          reg_8 <= ({reg_6 != 32'd0} ? reg_108 : reg_110);
          reg_10 <= ({({reg_6 != 32'd0} ? reg_108 : reg_110) != 32'd0} ? reg_104 : reg_106);
          reg_12 <= ({({({reg_6 != 32'd0} ? reg_108 : reg_110) != 32'd0} ? reg_104 : reg_106) != 32'd0} ? reg_100 : reg_102);
          reg_14 <= ({({({({reg_6 != 32'd0} ? reg_108 : reg_110) != 32'd0} ? reg_104 : reg_106) != 32'd0} ? reg_100 : reg_102) != 32'd0} ? reg_96 : reg_98);
          state <= 32'd136;
        end
        32'd126: begin
          reg_30 <= 32'd0;
          state <= 32'd125;
          state <= (32'd0 ? 32'd150 : 32'd125);
        end
        32'd125: begin
          reg_28 <= 32'd0;
          state <= 32'd124;
          state <= (32'd0 ? 32'd230 : 32'd124);
        end
        32'd124: begin
          reg_152 <= 32'd0;
          reg_154 <= {reg_30 * 32'd4000};
          reg_150 <= 32'd1077936128;
          reg_144 <= 32'd4000;
          reg_142 <= (- 32'd1);
          reg_136 <= 32'd8000;
          reg_134 <= 32'd1082130432;
          reg_128 <= 32'd12000;
          reg_126 <= 32'd1084227584;
          reg_120 <= 32'd1;
          reg_122 <= {reg_28 == 32'd1};
          reg_116 <= 32'd1;
          reg_118 <= {reg_28 == 32'd2};
          reg_112 <= 32'd1;
          reg_114 <= {reg_28 == 32'd100};
          reg_2 <= ({reg_28 == 32'd0} ? 32'd1 : {reg_28 == 32'd1});
          reg_4 <= ({({reg_28 == 32'd0} ? 32'd1 : {reg_28 == 32'd1}) != 32'd0} ? 32'd1 : {reg_28 == 32'd2});
          reg_6 <= ({({({reg_28 == 32'd0} ? 32'd1 : {reg_28 == 32'd1}) != 32'd0} ? 32'd1 : {reg_28 == 32'd2}) != 32'd0} ? 32'd1 : {reg_28 == 32'd100});
          reg_108 <= 32'd1;
          reg_110 <= {reg_28 == 32'd200};
          reg_104 <= 32'd1;
          reg_106 <= {reg_28 == 32'd300};
          reg_100 <= 32'd1;
          reg_102 <= {reg_28 == 32'd400};
          reg_96 <= 32'd1;
          reg_98 <= {reg_28 == 32'd500};
          reg_92 <= 32'd1;
          reg_94 <= {reg_28 == 32'd600};
          reg_88 <= 32'd1;
          reg_90 <= {reg_28 == 32'd700};
          reg_84 <= 32'd1;
          reg_86 <= {reg_28 == 32'd800};
          reg_80 <= 32'd1;
          reg_82 <= {reg_28 == 32'd900};
          reg_76 <= 32'd1;
          reg_78 <= {reg_28 == 32'd1000};
          state <= 32'd135;
        end
        32'd67: begin
          reg_68 <= reg_148;
          reg_70 <= 32'd1073741824;
          reg_60 <= reg_140;
          reg_62 <= 32'd1;
          state <= 32'd231;
        end
        32'd55: begin
          reg_30 <= {reg_30 + 32'd1};
          reg_15 <= {$signed({reg_30 + 32'd1}) < $signed(32'd1)};
          state <= ({$signed({reg_30 + 32'd1}) < $signed(32'd1)} ? 32'd125 : state);
          reg_164 <= ({{$signed({reg_30 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd0 : reg_164);
          reg_160 <= ({{$signed({reg_30 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd0 : reg_160);
          reg_158 <= ({{$signed({reg_30 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd4000 : reg_158);
          reg_156 <= ({{$signed({reg_30 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd12000 : reg_156);
          state <= ({{$signed({reg_30 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd245 : ({$signed({reg_30 + 32'd1}) < $signed(32'd1)} ? 32'd125 : state));
        end
        32'd38: begin
          reg_162 <= 32'd0;
          reg_168 <= 32'd0;
          state <= 32'd35;
          state <= (32'd0 ? 32'd149 : 32'd35);
        end
        32'd35: begin
          state <= 32'd330;
          reg_219 <= ( ~ reg_219);
          reg_218 <= 32'd0;
          reg_214 <= {{{reg_160 + 32'd0} + {reg_168 * 32'd4}} / 32'd4};
        end
        32'd29: begin
          reg_200 <= 32'd1059313418;
          f_add_a <= reg_166;
          f_add_b <= 32'd1059313418;
          reg_198 <= f_add_res;
          reg_194 <= 32'd1060320051;
          reg_186 <= 32'd1045891645;
          reg_178 <= 32'd1051260355;
          reg_168 <= {reg_168 + 32'd1};
          reg_5 <= {$signed({reg_168 + 32'd1}) < $signed(32'd1000)};
          state <= 32'd151;
        end
        32'd10: begin
          state <= 32'd145;
          reg_219 <= ( ~ reg_219);
          reg_218 <= 32'd1;
          reg_216 <= reg_162;
          reg_214 <= {{{reg_156 + 32'd0} + {reg_164 * 32'd4}} / 32'd4};
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
