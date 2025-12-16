module main(start, reset, clk, finish, return_val);
  logic [31:0] reg_64 = 0;
  logic [31:0] reg_32 = 0;
  logic [31:0] reg_80 = 0;
  logic [31:0] reg_48 = 0;
  logic [31:0] reg_8 = 0;
  logic [31:0] reg_40 = 0;
  logic [31:0] reg_56 = 0;
  logic [31:0] reg_4 = 0;
  logic [31:0] reg_68 = 0;
  logic [31:0] reg_36 = 0;
  logic [31:0] reg_52 = 0;
  logic [31:0] reg_44 = 0;
  logic [31:0] reg_66 = 0;
  logic [31:0] reg_34 = 0;
  logic [31:0] reg_82 = 0;
  logic [31:0] reg_50 = 0;
  logic [31:0] reg_10 = 0;
  logic [31:0] reg_42 = 0;
  logic [31:0] reg_58 = 0;
  logic [31:0] reg_6 = 0;
  logic [31:0] reg_70 = 0;
  logic [31:0] reg_38 = 0;
  logic [31:0] reg_54 = 0;
  logic [31:0] reg_78 = 0;
  logic [31:0] reg_46 = 0;
  logic [31:0] reg_62 = 0;
  logic [31:0] reg_81 = 0;
  logic [31:0] reg_9 = 0;
  logic [31:0] reg_5 = 0;
  logic [31:0] reg_13 = 0;
  logic [31:0] reg_83 = 0;
  logic [31:0] reg_11 = 0;
  logic [31:0] reg_7 = 0;
  logic [31:0] reg_79 = 0;
  (* ram_style = "block" *)
  logic [31:0] stack [959:0];
  logic [31:0] state = 0;
  output logic [31:0] return_val = 0;
  output logic [0:0] finish = 0;
  input [0:0] clk;
  input [0:0] reset;
  input [0:0] start;

  always @(negedge clk) begin
    if ({reg_83 != reg_79}) begin
      if (reg_82) begin
        stack[reg_78] <= reg_80;
      end else begin
        reg_81 <= stack[reg_78];
      end
      reg_79 <= reg_83;
    end else begin
    end
  end

  always @(posedge clk) begin
    if ({reset == 32'd1}) begin
      state <= 32'd51;
    end else begin
      case (state)
        32'd355: begin
          state <= 32'd212;
          reg_66 <= reg_81;
        end
        32'd240: begin
          reg_11 <= ({reg_13 == 32'd0} ? {$signed(reg_58) < $signed(32'd30)} : reg_11);
          state <= ({{reg_13 == 32'd0} & ({reg_13 == 32'd0} ? {$signed(reg_58) < $signed(32'd30)} : reg_11)} ? 32'd17 : state);
          state <= ({{reg_13 | {({reg_13 == 32'd0} ? {$signed(reg_58) < $signed(32'd30)} : reg_11) == 32'd0}} & {{reg_13 == 32'd0} & {({reg_13 == 32'd0} ? {$signed(reg_58) < $signed(32'd30)} : reg_11) == 32'd0}}} ? 32'd4 : ({{reg_13 == 32'd0} & ({reg_13 == 32'd0} ? {$signed(reg_58) < $signed(32'd30)} : reg_11)} ? 32'd17 : state));
          state <= ({{reg_13 | {({reg_13 == 32'd0} ? {$signed(reg_58) < $signed(32'd30)} : reg_11) == 32'd0}} & {reg_13 | ({reg_13 == 32'd0} ? {$signed(reg_58) < $signed(32'd30)} : reg_11)}} ? 32'd241 : ({{reg_13 | {({reg_13 == 32'd0} ? {$signed(reg_58) < $signed(32'd30)} : reg_11) == 32'd0}} & {{reg_13 == 32'd0} & {({reg_13 == 32'd0} ? {$signed(reg_58) < $signed(32'd30)} : reg_11) == 32'd0}}} ? 32'd4 : ({{reg_13 == 32'd0} & ({reg_13 == 32'd0} ? {$signed(reg_58) < $signed(32'd30)} : reg_11)} ? 32'd17 : state)));
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
          reg_58 <= ({reg_13 == 32'd0} ? {reg_58 + 32'd1} : reg_58);
          state <= 32'd231;
        end
        32'd229: begin
          reg_83 <= {( - {{32'd1 & {reg_13 == 32'd0}} != 32'd0}) ^ reg_83};
          reg_82 <= 32'd1;
          reg_80 <= ({32'd1 & {reg_13 == 32'd0}} ? reg_54 : reg_80);
          reg_78 <= ({32'd1 & {reg_13 == 32'd0}} ? {{{reg_48 + 32'd0} + {reg_58 * 32'd4}} / 32'd4} : reg_78);
          state <= 32'd230;
        end
        32'd228: begin
          state <= (reg_13 ? 32'd15 : state);
          state <= ({reg_13 == 32'd0} ? 32'd229 : (reg_13 ? 32'd15 : state));
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
        32'd224: begin
          state <= 32'd225;
        end
        32'd223: begin
          state <= 32'd224;
        end
        32'd222: begin
          reg_13 <= {$signed(reg_56) < $signed(32'd30)};
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
          reg_54 <= {{reg_54 + reg_62} + 32'd0};
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
          state <= 32'd214;
        end
        32'd212: begin
          reg_62 <= {reg_64 * reg_66};
          reg_56 <= {reg_56 + 32'd1};
          state <= 32'd213;
        end
        32'd211: begin
          state <= 32'd355;
          reg_83 <= ( ~ reg_83);
          reg_82 <= 32'd0;
          reg_78 <= {{{reg_68 + 32'd0} + {reg_56 * 32'd4}} / 32'd4};
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
          reg_68 <= {{reg_52 + reg_70} + 32'd0};
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
        32'd193: begin
          state <= 32'd44;
          state <= (32'd0 ? 32'd194 : 32'd44);
        end
        32'd192: begin
          state <= 32'd193;
          reg_83 <= ( ~ reg_83);
          reg_82 <= 32'd1;
          reg_80 <= reg_6;
          reg_78 <= {{{reg_42 + 32'd0} + {reg_6 * 32'd4}} / 32'd4};
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
          reg_42 <= {{reg_44 + reg_46} + 32'd0};
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
        32'd169: begin
          state <= ({reg_9 == 32'd0} ? 32'd17 : state);
          state <= (reg_9 ? 32'd170 : ({reg_9 == 32'd0} ? 32'd17 : state));
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
          state <= 32'd162;
        end
        32'd160: begin
          state <= 32'd161;
        end
        32'd159: begin
          reg_9 <= {$signed(reg_8) < $signed(32'd1)};
          state <= ({$signed(reg_8) < $signed(32'd1)} ? 32'd50 : state);
          reg_58 <= ({{$signed(reg_8) < $signed(32'd1)} == 32'd0} ? 32'd0 : reg_58);
          reg_52 <= ({{$signed(reg_8) < $signed(32'd1)} == 32'd0} ? 32'd240 : reg_52);
          reg_50 <= ({{$signed(reg_8) < $signed(32'd1)} == 32'd0} ? 32'd120 : reg_50);
          reg_48 <= ({{$signed(reg_8) < $signed(32'd1)} == 32'd0} ? 32'd0 : reg_48);
          state <= ({{$signed(reg_8) < $signed(32'd1)} == 32'd0} ? 32'd160 : ({$signed(reg_8) < $signed(32'd1)} ? 32'd50 : state));
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
        32'd148: begin
          reg_5 <= ({reg_7 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_5);
          state <= ({{reg_7 == 32'd0} & ({reg_7 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_5)} ? 32'd49 : state);
          state <= ({{reg_7 | {({reg_7 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_5) == 32'd0}} & {{reg_7 == 32'd0} & {({reg_7 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_5) == 32'd0}}} ? 32'd34 : ({{reg_7 == 32'd0} & ({reg_7 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_5)} ? 32'd49 : state));
          state <= ({{reg_7 | {({reg_7 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_5) == 32'd0}} & {reg_7 | ({reg_7 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_5)}} ? 32'd149 : ({{reg_7 | {({reg_7 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_5) == 32'd0}} & {{reg_7 == 32'd0} & {({reg_7 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_5) == 32'd0}}} ? 32'd34 : ({{reg_7 == 32'd0} & ({reg_7 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_5)} ? 32'd49 : state)));
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
          reg_7 <= {$signed(reg_4) < $signed(32'd30)};
          state <= ({$signed(reg_4) < $signed(32'd30)} ? 32'd44 : state);
          reg_6 <= ({{$signed(reg_4) < $signed(32'd30)} == 32'd0} ? {reg_6 + 32'd1} : reg_6);
          state <= ({{$signed(reg_4) < $signed(32'd30)} == 32'd0} ? 32'd139 : ({$signed(reg_4) < $signed(32'd30)} ? 32'd44 : state));
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
          state <= 32'd130;
        end
        32'd128: begin
          reg_4 <= {reg_4 + 32'd1};
          state <= 32'd129;
        end
        32'd127: begin
          state <= 32'd128;
          reg_83 <= ( ~ reg_83);
          reg_82 <= 32'd1;
          reg_80 <= reg_4;
          reg_78 <= {{{reg_32 + 32'd0} + {reg_4 * 32'd4}} / 32'd4};
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
        32'd117: begin
          reg_32 <= {{reg_34 + reg_36} + 32'd0};
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
          state <= 32'd109;
        end
        32'd107: begin
          reg_34 <= {{reg_38 + reg_40} + 32'd0};
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
          state <= 32'd103;
        end
        32'd101: begin
          state <= 32'd102;
        end
        32'd100: begin
          state <= 32'd101;
        end
        32'd99: begin
          state <= 32'd100;
        end
        32'd98: begin
          state <= 32'd99;
        end
        32'd51: begin
          reg_8 <= 32'd0;
          state <= 32'd50;
          state <= (32'd0 ? 32'd195 : 32'd50);
        end
        32'd50: begin
          reg_6 <= 32'd0;
          state <= 32'd49;
          state <= (32'd0 ? 32'd171 : 32'd49);
        end
        32'd49: begin
          reg_44 <= 32'd120;
          reg_46 <= {reg_8 * 32'd120};
          reg_4 <= 32'd0;
          state <= 32'd173;
        end
        32'd44: begin
          reg_38 <= 32'd240;
          reg_40 <= {reg_8 * 32'd3600};
          reg_36 <= {reg_6 * 32'd120};
          state <= 32'd98;
        end
        32'd34: begin
          reg_8 <= {reg_8 + 32'd1};
          state <= 32'd150;
        end
        32'd17: begin
          reg_54 <= 32'd0;
          reg_56 <= 32'd0;
          state <= 32'd15;
          state <= (32'd0 ? 32'd172 : 32'd15);
        end
        32'd15: begin
          reg_64 <= stack[{{{reg_50 + 32'd0} + {reg_56 * 32'd4}} / 32'd4}];
          reg_70 <= {reg_58 * 32'd120};
          state <= 32'd196;
        end
        32'd4: begin
          reg_10 <= 32'd0;
          finish <= 32'd1;
          return_val <= 32'd0;
          state <= 32'd4;
          state <= (32'd0 ? 32'd97 : 32'd4);
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
