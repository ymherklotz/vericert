module main(start, reset, clk, finish, return_val);
  logic [31:0] reg_128 = 0;
  logic [31:0] reg_64 = 0;
  logic [31:0] reg_96 = 0;
  logic [31:0] reg_144 = 0;
  logic [31:0] reg_80 = 0;
  logic [31:0] reg_48 = 0;
  logic [31:0] reg_112 = 0;
  logic [31:0] reg_8 = 0;
  logic [31:0] reg_72 = 0;
  logic [31:0] reg_104 = 0;
  logic [31:0] reg_88 = 0;
  logic [31:0] reg_56 = 0;
  logic [31:0] reg_120 = 0;
  logic [31:0] reg_4 = 0;
  logic [31:0] reg_132 = 0;
  logic [31:0] reg_68 = 0;
  logic [31:0] reg_100 = 0;
  logic [31:0] reg_84 = 0;
  logic [31:0] reg_52 = 0;
  logic [31:0] reg_116 = 0;
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
  logic [31:0] reg_142 = 0;
  logic [31:0] reg_78 = 0;
  logic [31:0] reg_110 = 0;
  logic [31:0] reg_94 = 0;
  logic [31:0] reg_62 = 0;
  logic [31:0] reg_126 = 0;
  logic [31:0] reg_17 = 0;
  logic [31:0] reg_145 = 0;
  logic [31:0] reg_9 = 0;
  logic [31:0] reg_5 = 0;
  logic [31:0] reg_13 = 0;
  logic [31:0] reg_147 = 0;
  logic [31:0] reg_11 = 0;
  logic [31:0] reg_7 = 0;
  logic [31:0] reg_15 = 0;
  logic [31:0] reg_143 = 0;
  (* ram_style = "block" *)
  logic [31:0] stack [1019:0];
  logic [31:0] state = 0;
  output logic [31:0] return_val = 0;
  output logic [0:0] finish = 0;
  input [0:0] clk;
  input [0:0] reset;
  input [0:0] start;

  always @(negedge clk) begin
    if ({reg_147 != reg_143}) begin
      if (reg_146) begin
        stack[reg_142] <= reg_144;
      end else begin
        reg_145 <= stack[reg_142];
      end
      reg_143 <= reg_147;
    end else begin
    end
  end

  always @(posedge clk) begin
    if ({reset == 32'd1}) begin
      state <= 32'd91;
    end else begin
      case (state)
        32'd419: begin
          state <= 32'd290;
          reg_128 <= reg_145;
        end
        32'd391: begin
          state <= 32'd175;
          reg_10 <= reg_145;
        end
        32'd318: begin
          reg_15 <= ({reg_17 == 32'd0} ? {$signed(reg_112) < $signed(32'd30)} : reg_15);
          state <= ({{reg_17 == 32'd0} & ({reg_17 == 32'd0} ? {$signed(reg_112) < $signed(32'd30)} : reg_15)} ? 32'd33 : state);
          state <= ({{reg_17 | {({reg_17 == 32'd0} ? {$signed(reg_112) < $signed(32'd30)} : reg_15) == 32'd0}} & {{reg_17 == 32'd0} & {({reg_17 == 32'd0} ? {$signed(reg_112) < $signed(32'd30)} : reg_15) == 32'd0}}} ? 32'd20 : ({{reg_17 == 32'd0} & ({reg_17 == 32'd0} ? {$signed(reg_112) < $signed(32'd30)} : reg_15)} ? 32'd33 : state));
          state <= ({{reg_17 | {({reg_17 == 32'd0} ? {$signed(reg_112) < $signed(32'd30)} : reg_15) == 32'd0}} & {reg_17 | ({reg_17 == 32'd0} ? {$signed(reg_112) < $signed(32'd30)} : reg_15)}} ? 32'd319 : ({{reg_17 | {({reg_17 == 32'd0} ? {$signed(reg_112) < $signed(32'd30)} : reg_15) == 32'd0}} & {{reg_17 == 32'd0} & {({reg_17 == 32'd0} ? {$signed(reg_112) < $signed(32'd30)} : reg_15) == 32'd0}}} ? 32'd20 : ({{reg_17 == 32'd0} & ({reg_17 == 32'd0} ? {$signed(reg_112) < $signed(32'd30)} : reg_15)} ? 32'd33 : state)));
        end
        32'd317: begin
          state <= 32'd318;
        end
        32'd316: begin
          state <= 32'd317;
        end
        32'd315: begin
          state <= 32'd316;
        end
        32'd314: begin
          state <= 32'd315;
        end
        32'd313: begin
          state <= 32'd314;
        end
        32'd312: begin
          state <= 32'd313;
        end
        32'd311: begin
          state <= 32'd312;
        end
        32'd310: begin
          state <= 32'd311;
        end
        32'd309: begin
          state <= 32'd310;
        end
        32'd308: begin
          reg_112 <= ({reg_17 == 32'd0} ? {reg_112 + 32'd1} : reg_112);
          state <= 32'd309;
        end
        32'd307: begin
          reg_147 <= {( - {{32'd1 & {reg_17 == 32'd0}} != 32'd0}) ^ reg_147};
          reg_146 <= 32'd1;
          reg_144 <= ({32'd1 & {reg_17 == 32'd0}} ? reg_110 : reg_144);
          reg_142 <= ({32'd1 & {reg_17 == 32'd0}} ? {{{reg_98 + 32'd0} + {reg_112 * 32'd4}} / 32'd4} : reg_142);
          state <= 32'd308;
        end
        32'd306: begin
          state <= (reg_17 ? 32'd31 : state);
          state <= ({reg_17 == 32'd0} ? 32'd307 : (reg_17 ? 32'd31 : state));
        end
        32'd305: begin
          state <= 32'd306;
        end
        32'd304: begin
          state <= 32'd305;
        end
        32'd303: begin
          state <= 32'd304;
        end
        32'd302: begin
          state <= 32'd303;
        end
        32'd301: begin
          state <= 32'd302;
        end
        32'd300: begin
          reg_17 <= {$signed(reg_108) < $signed(32'd30)};
          state <= 32'd301;
        end
        32'd299: begin
          state <= 32'd300;
        end
        32'd298: begin
          state <= 32'd299;
        end
        32'd297: begin
          state <= 32'd298;
        end
        32'd296: begin
          reg_110 <= {{reg_110 + reg_126} + 32'd0};
          state <= 32'd297;
        end
        32'd295: begin
          state <= 32'd296;
        end
        32'd294: begin
          state <= 32'd295;
        end
        32'd293: begin
          state <= 32'd294;
        end
        32'd292: begin
          state <= 32'd293;
        end
        32'd291: begin
          state <= 32'd292;
        end
        32'd290: begin
          reg_126 <= {reg_128 * reg_130};
          reg_108 <= {reg_108 + 32'd1};
          state <= 32'd291;
        end
        32'd289: begin
          state <= 32'd419;
          reg_147 <= ( ~ reg_147);
          reg_146 <= 32'd0;
          reg_142 <= {{{reg_132 + 32'd0} + {reg_108 * 32'd4}} / 32'd4};
        end
        32'd288: begin
          state <= 32'd289;
        end
        32'd287: begin
          state <= 32'd288;
        end
        32'd286: begin
          state <= 32'd287;
        end
        32'd285: begin
          state <= 32'd286;
        end
        32'd284: begin
          state <= 32'd285;
        end
        32'd283: begin
          state <= 32'd284;
        end
        32'd282: begin
          state <= 32'd283;
        end
        32'd281: begin
          state <= 32'd282;
        end
        32'd280: begin
          state <= 32'd281;
        end
        32'd279: begin
          reg_132 <= {{reg_100 + reg_134} + 32'd0};
          state <= 32'd280;
        end
        32'd278: begin
          state <= 32'd279;
        end
        32'd277: begin
          state <= 32'd278;
        end
        32'd276: begin
          state <= 32'd277;
        end
        32'd275: begin
          state <= 32'd276;
        end
        32'd274: begin
          state <= 32'd275;
        end
        32'd271: begin
          state <= 32'd17;
          state <= (32'd0 ? 32'd272 : 32'd17);
        end
        32'd269: begin
          state <= ({reg_11 == 32'd0} ? 32'd33 : state);
          state <= (reg_11 ? 32'd270 : ({reg_11 == 32'd0} ? 32'd33 : state));
        end
        32'd268: begin
          state <= 32'd269;
        end
        32'd267: begin
          state <= 32'd268;
        end
        32'd266: begin
          state <= 32'd267;
        end
        32'd265: begin
          state <= 32'd266;
        end
        32'd264: begin
          state <= 32'd265;
        end
        32'd263: begin
          state <= 32'd264;
        end
        32'd262: begin
          state <= 32'd263;
        end
        32'd261: begin
          state <= 32'd262;
        end
        32'd260: begin
          state <= 32'd261;
        end
        32'd259: begin
          reg_11 <= {$signed(reg_8) < $signed(32'd1)};
          state <= ({$signed(reg_8) < $signed(32'd1)} ? 32'd90 : state);
          reg_112 <= ({{$signed(reg_8) < $signed(32'd1)} == 32'd0} ? 32'd0 : reg_112);
          reg_100 <= ({{$signed(reg_8) < $signed(32'd1)} == 32'd0} ? 32'd480 : reg_100);
          reg_98 <= ({{$signed(reg_8) < $signed(32'd1)} == 32'd0} ? 32'd120 : reg_98);
          reg_96 <= ({{$signed(reg_8) < $signed(32'd1)} == 32'd0} ? 32'd240 : reg_96);
          reg_94 <= ({{$signed(reg_8) < $signed(32'd1)} == 32'd0} ? 32'd360 : reg_94);
          reg_92 <= ({{$signed(reg_8) < $signed(32'd1)} == 32'd0} ? 32'd0 : reg_92);
          state <= ({{$signed(reg_8) < $signed(32'd1)} == 32'd0} ? 32'd260 : ({$signed(reg_8) < $signed(32'd1)} ? 32'd90 : state));
        end
        32'd258: begin
          state <= 32'd259;
        end
        32'd257: begin
          state <= 32'd258;
        end
        32'd256: begin
          state <= 32'd257;
        end
        32'd255: begin
          state <= 32'd256;
        end
        32'd254: begin
          state <= 32'd255;
        end
        32'd253: begin
          state <= 32'd254;
        end
        32'd252: begin
          state <= 32'd253;
        end
        32'd251: begin
          state <= 32'd252;
        end
        32'd250: begin
          state <= 32'd251;
        end
        32'd248: begin
          state <= 32'd68;
          state <= (32'd0 ? 32'd249 : 32'd68);
        end
        32'd247: begin
          state <= 32'd248;
          reg_147 <= ( ~ reg_147);
          reg_146 <= 32'd1;
          reg_144 <= reg_62;
          reg_142 <= {{{reg_60 + 32'd0} + {reg_6 * 32'd4}} / 32'd4};
        end
        32'd246: begin
          state <= 32'd247;
          reg_147 <= ( ~ reg_147);
          reg_146 <= 32'd1;
          reg_144 <= reg_70;
          reg_142 <= {{{reg_68 + 32'd0} + {reg_6 * 32'd4}} / 32'd4};
        end
        32'd245: begin
          state <= 32'd246;
          reg_147 <= ( ~ reg_147);
          reg_146 <= 32'd1;
          reg_144 <= reg_78;
          reg_142 <= {{{reg_76 + 32'd0} + {reg_6 * 32'd4}} / 32'd4};
        end
        32'd244: begin
          state <= 32'd245;
          reg_147 <= ( ~ reg_147);
          reg_146 <= 32'd1;
          reg_144 <= reg_86;
          reg_142 <= {{{reg_84 + 32'd0} + {reg_6 * 32'd4}} / 32'd4};
        end
        32'd243: begin
          state <= 32'd244;
        end
        32'd242: begin
          state <= 32'd243;
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
          state <= 32'd239;
        end
        32'd237: begin
          state <= 32'd238;
        end
        32'd236: begin
          state <= 32'd237;
        end
        32'd235: begin
          state <= 32'd236;
        end
        32'd234: begin
          reg_84 <= {{reg_88 + reg_90} + 32'd0};
          reg_76 <= {{reg_80 + reg_82} + 32'd0};
          reg_68 <= {{reg_72 + reg_74} + 32'd0};
          reg_60 <= {{reg_64 + reg_66} + 32'd0};
          state <= 32'd235;
        end
        32'd233: begin
          state <= 32'd234;
        end
        32'd232: begin
          state <= 32'd233;
        end
        32'd231: begin
          reg_66 <= reg_74;
          state <= 32'd232;
        end
        32'd230: begin
          reg_82 <= reg_90;
          reg_74 <= reg_90;
          state <= 32'd231;
        end
        32'd229: begin
          state <= 32'd230;
        end
        32'd228: begin
          state <= 32'd229;
        end
        32'd227: begin
          state <= 32'd228;
        end
        32'd226: begin
          state <= 32'd227;
        end
        32'd225: begin
          state <= 32'd226;
        end
        32'd223: begin
          reg_9 <= ({reg_7 == 32'd0} ? {$signed(reg_106) < $signed(32'd30)} : reg_9);
          state <= ({{reg_7 == 32'd0} & ({reg_7 == 32'd0} ? {$signed(reg_106) < $signed(32'd30)} : reg_9)} ? 32'd19 : state);
          state <= ({{reg_7 | {({reg_7 == 32'd0} ? {$signed(reg_106) < $signed(32'd30)} : reg_9) == 32'd0}} & {{reg_7 == 32'd0} & {({reg_7 == 32'd0} ? {$signed(reg_106) < $signed(32'd30)} : reg_9) == 32'd0}}} ? 32'd6 : ({{reg_7 == 32'd0} & ({reg_7 == 32'd0} ? {$signed(reg_106) < $signed(32'd30)} : reg_9)} ? 32'd19 : state));
          state <= ({{reg_7 | {({reg_7 == 32'd0} ? {$signed(reg_106) < $signed(32'd30)} : reg_9) == 32'd0}} & {reg_7 | ({reg_7 == 32'd0} ? {$signed(reg_106) < $signed(32'd30)} : reg_9)}} ? 32'd224 : ({{reg_7 | {({reg_7 == 32'd0} ? {$signed(reg_106) < $signed(32'd30)} : reg_9) == 32'd0}} & {{reg_7 == 32'd0} & {({reg_7 == 32'd0} ? {$signed(reg_106) < $signed(32'd30)} : reg_9) == 32'd0}}} ? 32'd6 : ({{reg_7 == 32'd0} & ({reg_7 == 32'd0} ? {$signed(reg_106) < $signed(32'd30)} : reg_9)} ? 32'd19 : state)));
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
          state <= 32'd215;
        end
        32'd213: begin
          reg_106 <= ({reg_7 == 32'd0} ? {reg_106 + 32'd1} : reg_106);
          state <= 32'd214;
        end
        32'd212: begin
          reg_147 <= {( - {{32'd1 & {reg_7 == 32'd0}} != 32'd0}) ^ reg_147};
          reg_146 <= 32'd1;
          reg_144 <= ({32'd1 & {reg_7 == 32'd0}} ? reg_104 : reg_144);
          reg_142 <= ({32'd1 & {reg_7 == 32'd0}} ? {{{reg_96 + 32'd0} + {reg_106 * 32'd4}} / 32'd4} : reg_142);
          state <= 32'd213;
        end
        32'd211: begin
          state <= (reg_7 ? 32'd17 : state);
          state <= ({reg_7 == 32'd0} ? 32'd212 : (reg_7 ? 32'd17 : state));
        end
        32'd210: begin
          state <= 32'd211;
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
          reg_104 <= {{reg_104 + reg_116} + 32'd0};
          state <= 32'd202;
        end
        32'd200: begin
          state <= 32'd201;
        end
        32'd199: begin
          state <= 32'd200;
        end
        32'd198: begin
          state <= 32'd199;
        end
        32'd197: begin
          state <= 32'd198;
        end
        32'd196: begin
          state <= 32'd197;
        end
        32'd195: begin
          reg_116 <= {reg_118 * reg_120};
          state <= 32'd196;
        end
        32'd194: begin
          reg_118 <= stack[{{{reg_122 + 32'd0} + {reg_106 * 32'd4}} / 32'd4}];
          reg_7 <= {$signed(reg_102) < $signed(32'd30)};
          state <= 32'd195;
        end
        32'd193: begin
          state <= 32'd194;
        end
        32'd192: begin
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
          reg_122 <= {{reg_100 + reg_124} + 32'd0};
          reg_102 <= {reg_102 + 32'd1};
          state <= 32'd185;
        end
        32'd183: begin
          state <= 32'd184;
        end
        32'd182: begin
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
        32'd177: begin
          state <= 32'd31;
          state <= (32'd0 ? 32'd178 : 32'd31);
        end
        32'd175: begin
          finish <= 32'd1;
          return_val <= reg_10;
          state <= 32'd175;
          state <= (32'd0 ? 32'd176 : 32'd175);
        end
        32'd171: begin
          reg_13 <= ({reg_5 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_13);
          state <= ({{reg_5 == 32'd0} & ({reg_5 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_13)} ? 32'd89 : state);
          state <= ({{reg_5 | {({reg_5 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_13) == 32'd0}} & {{reg_5 == 32'd0} & {({reg_5 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_13) == 32'd0}}} ? 32'd57 : ({{reg_5 == 32'd0} & ({reg_5 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_13)} ? 32'd89 : state));
          state <= ({{reg_5 | {({reg_5 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_13) == 32'd0}} & {reg_5 | ({reg_5 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_13)}} ? 32'd172 : ({{reg_5 | {({reg_5 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_13) == 32'd0}} & {{reg_5 == 32'd0} & {({reg_5 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_13) == 32'd0}}} ? 32'd57 : ({{reg_5 == 32'd0} & ({reg_5 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_13)} ? 32'd89 : state)));
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
          reg_5 <= {$signed(reg_4) < $signed(32'd30)};
          state <= ({$signed(reg_4) < $signed(32'd30)} ? 32'd68 : state);
          reg_6 <= ({{$signed(reg_4) < $signed(32'd30)} == 32'd0} ? {reg_6 + 32'd1} : reg_6);
          state <= ({{$signed(reg_4) < $signed(32'd30)} == 32'd0} ? 32'd162 : ({$signed(reg_4) < $signed(32'd30)} ? 32'd68 : state));
        end
        32'd160: begin
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
          reg_4 <= {reg_4 + 32'd1};
          state <= 32'd152;
        end
        32'd150: begin
          state <= 32'd151;
          reg_147 <= ( ~ reg_147);
          reg_146 <= 32'd1;
          reg_144 <= reg_50;
          reg_142 <= {{{reg_48 + 32'd0} + {reg_4 * 32'd4}} / 32'd4};
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
          state <= 32'd143;
        end
        32'd141: begin
          state <= 32'd142;
        end
        32'd140: begin
          reg_48 <= {{reg_52 + reg_54} + 32'd0};
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
          state <= 32'd134;
        end
        32'd132: begin
          state <= 32'd133;
        end
        32'd131: begin
          state <= 32'd132;
        end
        32'd130: begin
          reg_52 <= {{reg_56 + reg_58} + 32'd0};
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
        32'd91: begin
          reg_8 <= 32'd0;
          state <= 32'd90;
          state <= (32'd0 ? 32'd273 : 32'd90);
        end
        32'd90: begin
          reg_6 <= 32'd0;
          state <= 32'd89;
          state <= (32'd0 ? 32'd174 : 32'd89);
        end
        32'd89: begin
          reg_88 <= 32'd120;
          reg_90 <= {reg_8 * 32'd120};
          reg_86 <= {reg_6 & 32'd1};
          reg_78 <= {reg_6 & 32'd1};
          reg_70 <= {reg_6 & 32'd1};
          reg_62 <= {reg_6 & 32'd1};
          reg_80 <= 32'd240;
          reg_72 <= 32'd360;
          reg_64 <= 32'd0;
          reg_4 <= 32'd0;
          state <= 32'd225;
        end
        32'd68: begin
          reg_56 <= 32'd480;
          reg_58 <= {reg_8 * 32'd3600};
          reg_54 <= {reg_6 * 32'd120};
          reg_50 <= {reg_6 & 32'd1};
          state <= 32'd121;
        end
        32'd57: begin
          reg_8 <= {reg_8 + 32'd1};
          state <= 32'd250;
        end
        32'd33: begin
          reg_110 <= stack[{{{reg_98 + 32'd0} + {reg_112 * 32'd4}} / 32'd4}];
          reg_108 <= 32'd0;
          state <= 32'd177;
        end
        32'd31: begin
          reg_134 <= {reg_112 * 32'd120};
          reg_130 <= stack[{{{reg_94 + 32'd0} + {reg_108 * 32'd4}} / 32'd4}];
          state <= 32'd274;
        end
        32'd20: begin
          reg_106 <= 32'd0;
          state <= 32'd19;
          state <= (32'd0 ? 32'd173 : 32'd19);
        end
        32'd19: begin
          reg_104 <= stack[{{{reg_96 + 32'd0} + {reg_106 * 32'd4}} / 32'd4}];
          reg_102 <= 32'd0;
          state <= 32'd271;
        end
        32'd17: begin
          reg_124 <= {reg_102 * 32'd120};
          reg_120 <= stack[{{{reg_92 + 32'd0} + {reg_102 * 32'd4}} / 32'd4}];
          state <= 32'd179;
        end
        32'd6: begin
          state <= 32'd391;
          reg_147 <= ( ~ reg_147);
          reg_146 <= 32'd0;
          reg_142 <= 32'd64;
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
