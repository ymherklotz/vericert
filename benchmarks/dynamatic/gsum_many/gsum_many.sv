module main(start, reset, clk, finish, return_val);
  logic [31:0] reg_64 = 0;
  logic [31:0] reg_32 = 0;
  logic [31:0] reg_80 = 0;
  logic [31:0] reg_48 = 0;
  logic [31:0] reg_8 = 0;
  logic [31:0] reg_72 = 0;
  logic [31:0] reg_40 = 0;
  logic [31:0] reg_104 = 0;
  logic [31:0] reg_24 = 0;
  logic [31:0] reg_88 = 0;
  logic [31:0] reg_56 = 0;
  logic [31:0] reg_4 = 0;
  logic [31:0] reg_68 = 0;
  logic [31:0] reg_36 = 0;
  logic [31:0] reg_84 = 0;
  logic [31:0] reg_52 = 0;
  logic [31:0] reg_76 = 0;
  logic [31:0] reg_44 = 0;
  logic [31:0] reg_92 = 0;
  logic [31:0] reg_60 = 0;
  logic [31:0] reg_66 = 0;
  logic [31:0] reg_82 = 0;
  logic [31:0] reg_50 = 0;
  logic [31:0] reg_74 = 0;
  logic [31:0] reg_42 = 0;
  logic [31:0] reg_106 = 0;
  logic [31:0] reg_90 = 0;
  logic [31:0] reg_58 = 0;
  logic [31:0] reg_6 = 0;
  logic [31:0] reg_70 = 0;
  logic [31:0] reg_38 = 0;
  logic [31:0] reg_102 = 0;
  logic [31:0] reg_86 = 0;
  logic [31:0] reg_54 = 0;
  logic [31:0] reg_46 = 0;
  logic [31:0] reg_30 = 0;
  logic [31:0] reg_94 = 0;
  logic [31:0] reg_62 = 0;
  logic [31:0] reg_9 = 0;
  logic [31:0] reg_105 = 0;
  logic [31:0] reg_5 = 0;
  logic [31:0] reg_13 = 0;
  logic [31:0] reg_11 = 0;
  logic [31:0] reg_107 = 0;
  logic [31:0] reg_7 = 0;
  logic [31:0] reg_103 = 0;
  logic [31:0] reg_15 = 0;
  (* ram_style = "block" *)
  logic [31:0] stack [3999:0];
  logic [31:0] state = 0;
  output logic [31:0] return_val = 0;
  output logic [0:0] finish = 0;
  input [0:0] clk;
  input [0:0] reset;
  input [0:0] start;

  always @(negedge clk) begin
    if ({reg_107 != reg_103}) begin
      if (reg_106) begin
        stack[reg_102] <= reg_104;
      end else begin
        reg_105 <= stack[reg_102];
      end
      reg_103 <= reg_107;
    end else begin
    end
  end

  always @(posedge clk) begin
    if ({reset == 32'd1}) begin
      state <= 32'd66;
    end else begin
      case (state)
        32'd337: begin
          state <= 32'd141;
          reg_74 <= reg_105;
        end
        32'd307: begin
          reg_15 <= {$signed(reg_72) < $signed(32'd10)};
          state <= ({$signed(reg_72) < $signed(32'd10)} ? 32'd22 : state);
          reg_8 <= ({{$signed(reg_72) < $signed(32'd10)} == 32'd0} ? 32'd0 : reg_8);
          finish <= ({{$signed(reg_72) < $signed(32'd10)} == 32'd0} ? 32'd1 : finish);
          return_val <= ({{$signed(reg_72) < $signed(32'd10)} == 32'd0} ? ({{$signed(reg_72) < $signed(32'd10)} == 32'd0} ? 32'd0 : reg_8) : return_val);
          state <= ({{$signed(reg_72) < $signed(32'd10)} == 32'd0} ? 32'd307 : ({$signed(reg_72) < $signed(32'd10)} ? 32'd22 : state));
          state <= ({{{$signed(reg_72) < $signed(32'd10)} == 32'd0} & {$signed(reg_72) < $signed(32'd10)}} ? 32'd308 : ({{$signed(reg_72) < $signed(32'd10)} == 32'd0} ? 32'd307 : ({$signed(reg_72) < $signed(32'd10)} ? 32'd22 : state)));
        end
        32'd306: begin
          state <= 32'd307;
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
          state <= 32'd301;
        end
        32'd299: begin
          state <= 32'd300;
        end
        32'd298: begin
          state <= 32'd299;
        end
        32'd297: begin
          reg_72 <= {reg_72 + 32'd1};
          state <= 32'd298;
        end
        32'd295: begin
          state <= ({reg_13 == 32'd0} ? 32'd22 : state);
          state <= (reg_13 ? 32'd296 : ({reg_13 == 32'd0} ? 32'd22 : state));
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
          state <= 32'd291;
        end
        32'd289: begin
          state <= 32'd290;
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
          reg_13 <= {$signed(reg_6) < $signed(32'd1)};
          state <= ({$signed(reg_6) < $signed(32'd1)} ? 32'd65 : state);
          reg_72 <= ({{$signed(reg_6) < $signed(32'd1)} == 32'd0} ? 32'd0 : reg_72);
          reg_68 <= ({{$signed(reg_6) < $signed(32'd1)} == 32'd0} ? 32'd0 : reg_68);
          reg_66 <= ({{$signed(reg_6) < $signed(32'd1)} == 32'd0} ? 32'd12000 : reg_66);
          state <= ({{$signed(reg_6) < $signed(32'd1)} == 32'd0} ? 32'd286 : ({$signed(reg_6) < $signed(32'd1)} ? 32'd65 : state));
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
        32'd274: begin
          state <= ({{reg_11 == 32'd0} & {reg_13 == 32'd0}} ? 32'd22 : state);
          state <= ({reg_11 | reg_13} ? 32'd275 : ({{reg_11 == 32'd0} & {reg_13 == 32'd0}} ? 32'd22 : state));
        end
        32'd273: begin
          state <= 32'd274;
        end
        32'd272: begin
          state <= 32'd273;
        end
        32'd271: begin
          state <= 32'd272;
        end
        32'd270: begin
          state <= 32'd271;
        end
        32'd269: begin
          state <= 32'd270;
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
          reg_13 <= ({reg_11 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_13);
          state <= ({{reg_11 == 32'd0} & ({reg_11 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_13)} ? 32'd65 : state);
          reg_72 <= ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_13) == 32'd0}} & {{reg_11 == 32'd0} & {({reg_11 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_13) == 32'd0}}} ? 32'd0 : reg_72);
          reg_68 <= ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_13) == 32'd0}} & {{reg_11 == 32'd0} & {({reg_11 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_13) == 32'd0}}} ? 32'd0 : reg_68);
          reg_66 <= ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_13) == 32'd0}} & {{reg_11 == 32'd0} & {({reg_11 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_13) == 32'd0}}} ? 32'd12000 : reg_66);
          state <= ({reg_11 | {({reg_11 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_13) == 32'd0}} ? 32'd265 : ({{reg_11 == 32'd0} & ({reg_11 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_13)} ? 32'd65 : state));
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
          state <= 32'd260;
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
          reg_11 <= {$signed(reg_4) < $signed(32'd1000)};
          state <= ({$signed(reg_4) < $signed(32'd1000)} ? 32'd64 : state);
          reg_6 <= ({{$signed(reg_4) < $signed(32'd1000)} == 32'd0} ? {reg_6 + 32'd1} : reg_6);
          state <= ({{$signed(reg_4) < $signed(32'd1000)} == 32'd0} ? 32'd255 : ({$signed(reg_4) < $signed(32'd1000)} ? 32'd64 : state));
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
        32'd249: begin
          state <= 32'd250;
        end
        32'd248: begin
          state <= 32'd249;
        end
        32'd247: begin
          state <= 32'd248;
        end
        32'd246: begin
          state <= 32'd247;
        end
        32'd245: begin
          state <= 32'd246;
        end
        32'd244: begin
          reg_4 <= {reg_4 + 32'd1};
          state <= 32'd245;
        end
        32'd243: begin
          state <= 32'd244;
          reg_107 <= ( ~ reg_107);
          reg_106 <= 32'd1;
          reg_104 <= reg_4;
          reg_102 <= {{{reg_24 + 32'd0} + {reg_4 * 32'd4}} / 32'd4};
        end
        32'd239: begin
          reg_15 <= ({reg_9 == 32'd0} ? {$signed(reg_72) < $signed(32'd10)} : reg_15);
          state <= ({{reg_9 == 32'd0} & ({reg_9 == 32'd0} ? {$signed(reg_72) < $signed(32'd10)} : reg_15)} ? 32'd22 : state);
          reg_8 <= ({{reg_9 | {({reg_9 == 32'd0} ? {$signed(reg_72) < $signed(32'd10)} : reg_15) == 32'd0}} & {{reg_9 == 32'd0} & {({reg_9 == 32'd0} ? {$signed(reg_72) < $signed(32'd10)} : reg_15) == 32'd0}}} ? 32'd0 : reg_8);
          finish <= ({{reg_9 | {({reg_9 == 32'd0} ? {$signed(reg_72) < $signed(32'd10)} : reg_15) == 32'd0}} & {{reg_9 == 32'd0} & {({reg_9 == 32'd0} ? {$signed(reg_72) < $signed(32'd10)} : reg_15) == 32'd0}}} ? 32'd1 : finish);
          return_val <= ({{reg_9 | {({reg_9 == 32'd0} ? {$signed(reg_72) < $signed(32'd10)} : reg_15) == 32'd0}} & {{reg_9 == 32'd0} & {({reg_9 == 32'd0} ? {$signed(reg_72) < $signed(32'd10)} : reg_15) == 32'd0}}} ? ({{reg_9 | {({reg_9 == 32'd0} ? {$signed(reg_72) < $signed(32'd10)} : reg_15) == 32'd0}} & {{reg_9 == 32'd0} & {({reg_9 == 32'd0} ? {$signed(reg_72) < $signed(32'd10)} : reg_15) == 32'd0}}} ? 32'd0 : reg_8) : return_val);
          state <= ({{reg_9 | {({reg_9 == 32'd0} ? {$signed(reg_72) < $signed(32'd10)} : reg_15) == 32'd0}} & {{reg_9 == 32'd0} & {({reg_9 == 32'd0} ? {$signed(reg_72) < $signed(32'd10)} : reg_15) == 32'd0}}} ? 32'd239 : ({{reg_9 == 32'd0} & ({reg_9 == 32'd0} ? {$signed(reg_72) < $signed(32'd10)} : reg_15)} ? 32'd22 : state));
          state <= ({{reg_9 | {({reg_9 == 32'd0} ? {$signed(reg_72) < $signed(32'd10)} : reg_15) == 32'd0}} & {reg_9 | ({reg_9 == 32'd0} ? {$signed(reg_72) < $signed(32'd10)} : reg_15)}} ? 32'd240 : ({{reg_9 | {({reg_9 == 32'd0} ? {$signed(reg_72) < $signed(32'd10)} : reg_15) == 32'd0}} & {{reg_9 == 32'd0} & {({reg_9 == 32'd0} ? {$signed(reg_72) < $signed(32'd10)} : reg_15) == 32'd0}}} ? 32'd239 : ({{reg_9 == 32'd0} & ({reg_9 == 32'd0} ? {$signed(reg_72) < $signed(32'd10)} : reg_15)} ? 32'd22 : state)));
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
          state <= 32'd235;
        end
        32'd233: begin
          state <= 32'd234;
        end
        32'd232: begin
          state <= 32'd233;
        end
        32'd231: begin
          state <= 32'd232;
        end
        32'd230: begin
          state <= 32'd231;
        end
        32'd229: begin
          reg_72 <= ({reg_9 == 32'd0} ? {reg_72 + 32'd1} : reg_72);
          state <= 32'd230;
        end
        32'd228: begin
          reg_107 <= {( - {{32'd1 & {reg_9 == 32'd0}} != 32'd0}) ^ reg_107};
          reg_106 <= 32'd1;
          reg_104 <= ({32'd1 & {reg_9 == 32'd0}} ? reg_70 : reg_104);
          reg_102 <= ({32'd1 & {reg_9 == 32'd0}} ? {{{reg_66 + 32'd0} + {reg_72 * 32'd4}} / 32'd4} : reg_102);
          state <= 32'd229;
        end
        32'd227: begin
          state <= (reg_9 ? 32'd20 : state);
          state <= ({reg_9 == 32'd0} ? 32'd228 : (reg_9 ? 32'd20 : state));
        end
        32'd226: begin
          state <= 32'd227;
        end
        32'd225: begin
          state <= 32'd226;
        end
        32'd224: begin
          state <= 32'd225;
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
          reg_70 <= {{reg_70 + reg_80} + 32'd0};
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
          state <= 32'd214;
        end
        32'd212: begin
          state <= 32'd213;
        end
        32'd211: begin
          reg_80 <= {reg_82 * reg_74};
          state <= 32'd212;
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
          reg_82 <= {reg_84 + 32'd1};
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
          reg_84 <= {reg_86 * reg_74};
          state <= 32'd196;
        end
        32'd194: begin
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
          reg_86 <= {reg_88 + 32'd1};
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
          state <= 32'd182;
        end
        32'd180: begin
          state <= 32'd181;
        end
        32'd179: begin
          reg_88 <= {reg_90 * reg_74};
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
          reg_90 <= {reg_92 + 32'd1};
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
          reg_92 <= {reg_94 * reg_74};
          reg_9 <= {$signed(reg_76) < $signed(32'd1000)};
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
        32'd151: begin
          reg_9 <= ({reg_7 == 32'd0} ? {$signed(reg_76) < $signed(32'd1000)} : reg_9);
          state <= ({{reg_7 == 32'd0} & ({reg_7 == 32'd0} ? {$signed(reg_76) < $signed(32'd1000)} : reg_9)} ? 32'd20 : state);
          state <= ({{reg_7 | {({reg_7 == 32'd0} ? {$signed(reg_76) < $signed(32'd1000)} : reg_9) == 32'd0}} & {{reg_7 == 32'd0} & {({reg_7 == 32'd0} ? {$signed(reg_76) < $signed(32'd1000)} : reg_9) == 32'd0}}} ? 32'd7 : ({{reg_7 == 32'd0} & ({reg_7 == 32'd0} ? {$signed(reg_76) < $signed(32'd1000)} : reg_9)} ? 32'd20 : state));
          state <= ({{reg_7 | {({reg_7 == 32'd0} ? {$signed(reg_76) < $signed(32'd1000)} : reg_9) == 32'd0}} & {reg_7 | ({reg_7 == 32'd0} ? {$signed(reg_76) < $signed(32'd1000)} : reg_9)}} ? 32'd152 : ({{reg_7 | {({reg_7 == 32'd0} ? {$signed(reg_76) < $signed(32'd1000)} : reg_9) == 32'd0}} & {{reg_7 == 32'd0} & {({reg_7 == 32'd0} ? {$signed(reg_76) < $signed(32'd1000)} : reg_9) == 32'd0}}} ? 32'd7 : ({{reg_7 == 32'd0} & ({reg_7 == 32'd0} ? {$signed(reg_76) < $signed(32'd1000)} : reg_9)} ? 32'd20 : state)));
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
          state <= 32'd143;
        end
        32'd141: begin
          reg_7 <= {$signed(reg_74) >= $signed(32'd0)};
          state <= ({$signed(reg_74) >= $signed(32'd0)} ? 32'd18 : state);
          reg_76 <= ({{$signed(reg_74) >= $signed(32'd0)} == 32'd0} ? {reg_76 + 32'd1} : reg_76);
          state <= ({{$signed(reg_74) >= $signed(32'd0)} == 32'd0} ? 32'd142 : ({$signed(reg_74) >= $signed(32'd0)} ? 32'd18 : state));
        end
        32'd139: begin
          reg_11 <= ({reg_5 == 32'd0} ? {$signed(reg_4) < $signed(32'd1000)} : reg_11);
          state <= ({{reg_5 == 32'd0} & ({reg_5 == 32'd0} ? {$signed(reg_4) < $signed(32'd1000)} : reg_11)} ? 32'd64 : state);
          state <= ({{reg_5 | {({reg_5 == 32'd0} ? {$signed(reg_4) < $signed(32'd1000)} : reg_11) == 32'd0}} & {{reg_5 == 32'd0} & {({reg_5 == 32'd0} ? {$signed(reg_4) < $signed(32'd1000)} : reg_11) == 32'd0}}} ? 32'd35 : ({{reg_5 == 32'd0} & ({reg_5 == 32'd0} ? {$signed(reg_4) < $signed(32'd1000)} : reg_11)} ? 32'd64 : state));
          state <= ({{reg_5 | {({reg_5 == 32'd0} ? {$signed(reg_4) < $signed(32'd1000)} : reg_11) == 32'd0}} & {reg_5 | ({reg_5 == 32'd0} ? {$signed(reg_4) < $signed(32'd1000)} : reg_11)}} ? 32'd140 : ({{reg_5 | {({reg_5 == 32'd0} ? {$signed(reg_4) < $signed(32'd1000)} : reg_11) == 32'd0}} & {{reg_5 == 32'd0} & {({reg_5 == 32'd0} ? {$signed(reg_4) < $signed(32'd1000)} : reg_11) == 32'd0}}} ? 32'd35 : ({{reg_5 == 32'd0} & ({reg_5 == 32'd0} ? {$signed(reg_4) < $signed(32'd1000)} : reg_11)} ? 32'd64 : state)));
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
          state <= 32'd131;
        end
        32'd129: begin
          state <= (reg_5 ? 32'd41 : state);
          reg_4 <= ({reg_5 == 32'd0} ? {reg_4 + 32'd1} : reg_4);
          state <= ({reg_5 == 32'd0} ? 32'd130 : (reg_5 ? 32'd41 : state));
        end
        32'd128: begin
          state <= 32'd129;
          reg_107 <= ( ~ reg_107);
          reg_106 <= 32'd1;
          reg_104 <= reg_32;
          reg_102 <= {{{reg_30 + 32'd0} + {reg_4 * 32'd4}} / 32'd4};
        end
        32'd127: begin
          state <= 32'd128;
          reg_107 <= ( ~ reg_107);
          reg_106 <= 32'd1;
          reg_104 <= reg_42;
          reg_102 <= {{{reg_40 + 32'd0} + {reg_4 * 32'd4}} / 32'd4};
        end
        32'd126: begin
          state <= 32'd127;
          reg_107 <= ( ~ reg_107);
          reg_106 <= 32'd1;
          reg_104 <= reg_50;
          reg_102 <= {{{reg_48 + 32'd0} + {reg_4 * 32'd4}} / 32'd4};
        end
        32'd125: begin
          state <= 32'd126;
          reg_107 <= ( ~ reg_107);
          reg_106 <= 32'd1;
          reg_104 <= reg_58;
          reg_102 <= {{{reg_56 + 32'd0} + {reg_4 * 32'd4}} / 32'd4};
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
        32'd117: begin
          state <= 32'd118;
        end
        32'd116: begin
          state <= 32'd117;
        end
        32'd115: begin
          reg_56 <= {{reg_62 + reg_64} + 32'd0};
          reg_48 <= {{reg_52 + reg_54} + 32'd0};
          reg_40 <= {{reg_44 + reg_46} + 32'd0};
          reg_42 <= reg_50;
          reg_30 <= {{reg_36 + reg_38} + 32'd0};
          state <= 32'd116;
        end
        32'd114: begin
          state <= 32'd115;
        end
        32'd113: begin
          state <= 32'd114;
        end
        32'd112: begin
          reg_38 <= reg_46;
          state <= 32'd113;
        end
        32'd111: begin
          reg_54 <= reg_64;
          reg_46 <= reg_64;
          state <= 32'd112;
        end
        32'd110: begin
          state <= 32'd111;
        end
        32'd109: begin
          state <= 32'd110;
        end
        32'd108: begin
          state <= 32'd109;
        end
        32'd107: begin
          state <= 32'd108;
        end
        32'd106: begin
          state <= 32'd107;
        end
        32'd66: begin
          reg_6 <= 32'd0;
          state <= 32'd65;
          state <= (32'd0 ? 32'd153 : 32'd65);
        end
        32'd65: begin
          reg_4 <= 32'd0;
          state <= 32'd64;
          state <= (32'd0 ? 32'd242 : 32'd64);
        end
        32'd64: begin
          reg_62 <= 32'd0;
          reg_64 <= {reg_6 * 32'd4000};
          reg_60 <= 32'd1;
          reg_58 <= {32'd1 - reg_4};
          reg_32 <= {32'd1 - reg_4};
          reg_52 <= 32'd8000;
          reg_50 <= {reg_4 + 32'd10};
          reg_44 <= 32'd12000;
          reg_36 <= 32'd4000;
          reg_5 <= {reg_4 == 32'd0};
          state <= 32'd106;
        end
        32'd41: begin
          reg_24 <= reg_56;
          state <= 32'd243;
        end
        32'd35: begin
          reg_6 <= {reg_6 + 32'd1};
          state <= 32'd276;
        end
        32'd22: begin
          reg_70 <= 32'd0;
          reg_76 <= 32'd0;
          state <= 32'd20;
          state <= (32'd0 ? 32'd241 : 32'd20);
        end
        32'd20: begin
          state <= 32'd337;
          reg_107 <= ( ~ reg_107);
          reg_106 <= 32'd0;
          reg_102 <= {{{reg_68 + 32'd0} + {reg_76 * 32'd4}} / 32'd4};
        end
        32'd18: begin
          reg_94 <= {reg_74 + 32'd1};
          reg_76 <= {reg_76 + 32'd1};
          state <= 32'd154;
        end
        32'd7: begin
          state <= 32'd297;
          reg_107 <= ( ~ reg_107);
          reg_106 <= 32'd1;
          reg_104 <= reg_70;
          reg_102 <= {{{reg_66 + 32'd0} + {reg_72 * 32'd4}} / 32'd4};
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
