module main(start, reset, clk, finish, return_val);
  logic [31:0] reg_64 = 0;
  logic [31:0] reg_80 = 0;
  logic [31:0] reg_48 = 0;
  logic [31:0] reg_8 = 0;
  logic [31:0] reg_72 = 0;
  logic [31:0] reg_56 = 0;
  logic [31:0] reg_4 = 0;
  logic [31:0] reg_68 = 0;
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
  logic [31:0] reg_90 = 0;
  logic [31:0] reg_58 = 0;
  logic [31:0] reg_6 = 0;
  logic [31:0] reg_70 = 0;
  logic [31:0] reg_54 = 0;
  logic [31:0] reg_46 = 0;
  logic [31:0] reg_94 = 0;
  logic [31:0] reg_62 = 0;
  logic [31:0] reg_9 = 0;
  logic [31:0] reg_5 = 0;
  logic [31:0] reg_13 = 0;
  logic [31:0] reg_93 = 0;
  logic [31:0] reg_11 = 0;
  logic [31:0] reg_91 = 0;
  logic [31:0] reg_7 = 0;
  logic [31:0] reg_95 = 0;
  (* ram_style = "block" *)
  logic [31:0] stack [149:0];
  logic [31:0] state = 0;
  output logic [31:0] return_val = 0;
  output logic [0:0] finish = 0;
  input [0:0] clk;
  input [0:0] reset;
  input [0:0] start;

  always @(negedge clk) begin
    if ({reg_95 != reg_91}) begin
      if (reg_94) begin
        stack[reg_90] <= reg_92;
      end else begin
        reg_93 <= stack[reg_90];
      end
      reg_91 <= reg_95;
    end else begin
    end
  end

  always @(posedge clk) begin
    if ({reset == 32'd1}) begin
      state <= 32'd53;
    end else begin
      case (state)
        32'd292: begin
          state <= 32'd135;
          reg_82 <= reg_93;
        end
        32'd266: begin
          state <= 32'd111;
          reg_72 <= ({reg_9 == 32'd0} ? reg_93 : reg_72);
        end
        32'd210: begin
          reg_7 <= ({reg_13 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_7);
          state <= ({{reg_13 == 32'd0} & ({reg_13 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_7)} ? 32'd52 : state);
          state <= ({{reg_13 | {({reg_13 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_7) == 32'd0}} & {{reg_13 == 32'd0} & {({reg_13 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_7) == 32'd0}}} ? 32'd32 : ({{reg_13 == 32'd0} & ({reg_13 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_7)} ? 32'd52 : state));
          state <= ({{reg_13 | {({reg_13 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_7) == 32'd0}} & {reg_13 | ({reg_13 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_7)}} ? 32'd211 : ({{reg_13 | {({reg_13 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_7) == 32'd0}} & {{reg_13 == 32'd0} & {({reg_13 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_7) == 32'd0}}} ? 32'd32 : ({{reg_13 == 32'd0} & ({reg_13 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_7)} ? 32'd52 : state)));
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
          state <= 32'd202;
        end
        32'd200: begin
          reg_13 <= {$signed(reg_4) < $signed(32'd50)};
          state <= ({$signed(reg_4) < $signed(32'd50)} ? 32'd51 : state);
          reg_6 <= ({{$signed(reg_4) < $signed(32'd50)} == 32'd0} ? {reg_6 + 32'd1} : reg_6);
          state <= ({{$signed(reg_4) < $signed(32'd50)} == 32'd0} ? 32'd201 : ({$signed(reg_4) < $signed(32'd50)} ? 32'd51 : state));
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
          reg_4 <= {reg_4 + 32'd1};
          state <= 32'd191;
        end
        32'd189: begin
          state <= 32'd190;
          reg_95 <= ( ~ reg_95);
          reg_94 <= 32'd1;
          reg_92 <= reg_4;
          reg_90 <= {{{reg_42 + 32'd0} + {reg_4 * 32'd4}} / 32'd4};
        end
        32'd188: begin
          state <= 32'd189;
          reg_95 <= ( ~ reg_95);
          reg_94 <= 32'd1;
          reg_92 <= reg_50;
          reg_90 <= {{{reg_48 + 32'd0} + {reg_4 * 32'd4}} / 32'd4};
        end
        32'd187: begin
          state <= 32'd188;
          reg_95 <= ( ~ reg_95);
          reg_94 <= 32'd1;
          reg_92 <= reg_58;
          reg_90 <= {{{reg_56 + 32'd0} + {reg_4 * 32'd4}} / 32'd4};
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
          reg_56 <= {{reg_60 + reg_62} + 32'd0};
          reg_48 <= {{reg_52 + reg_54} + 32'd0};
          reg_50 <= reg_58;
          reg_42 <= {{reg_44 + reg_46} + 32'd0};
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
          reg_54 <= reg_62;
          reg_46 <= reg_62;
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
        32'd166: begin
          reg_5 <= ({reg_11 == 32'd0} ? {$signed(reg_76) < $signed(32'd50)} : reg_5);
          state <= ({{reg_11 == 32'd0} & ({reg_11 == 32'd0} ? {$signed(reg_76) < $signed(32'd50)} : reg_5)} ? 32'd18 : state);
          state <= ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(reg_76) < $signed(32'd50)} : reg_5) == 32'd0}} & {{reg_11 == 32'd0} & {({reg_11 == 32'd0} ? {$signed(reg_76) < $signed(32'd50)} : reg_5) == 32'd0}}} ? 32'd4 : ({{reg_11 == 32'd0} & ({reg_11 == 32'd0} ? {$signed(reg_76) < $signed(32'd50)} : reg_5)} ? 32'd18 : state));
          state <= ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(reg_76) < $signed(32'd50)} : reg_5) == 32'd0}} & {reg_11 | ({reg_11 == 32'd0} ? {$signed(reg_76) < $signed(32'd50)} : reg_5)}} ? 32'd167 : ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(reg_76) < $signed(32'd50)} : reg_5) == 32'd0}} & {{reg_11 == 32'd0} & {({reg_11 == 32'd0} ? {$signed(reg_76) < $signed(32'd50)} : reg_5) == 32'd0}}} ? 32'd4 : ({{reg_11 == 32'd0} & ({reg_11 == 32'd0} ? {$signed(reg_76) < $signed(32'd50)} : reg_5)} ? 32'd18 : state)));
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
          state <= 32'd160;
        end
        32'd158: begin
          state <= 32'd159;
        end
        32'd157: begin
          state <= 32'd158;
        end
        32'd156: begin
          reg_76 <= ({reg_11 == 32'd0} ? {reg_76 + 32'd1} : reg_76);
          state <= 32'd157;
        end
        32'd155: begin
          reg_95 <= {( - {{32'd1 & {reg_11 == 32'd0}} != 32'd0}) ^ reg_95};
          reg_94 <= 32'd1;
          reg_92 <= ({32'd1 & {reg_11 == 32'd0}} ? reg_80 : reg_92);
          reg_90 <= ({32'd1 & {reg_11 == 32'd0}} ? {{{reg_64 + 32'd0} + {reg_76 * 32'd4}} / 32'd4} : reg_90);
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
          reg_11 <= {$signed(reg_70) < $signed(32'd5)};
          state <= ({$signed(reg_70) < $signed(32'd5)} ? 32'd13 : state);
          reg_80 <= ({{$signed(reg_70) < $signed(32'd5)} == 32'd0} ? {{reg_72 * 32'd2} + 32'd0} : reg_80);
          state <= ({{$signed(reg_70) < $signed(32'd5)} == 32'd0} ? 32'd146 : ({$signed(reg_70) < $signed(32'd5)} ? 32'd13 : state));
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
          state <= 32'd139;
        end
        32'd137: begin
          state <= 32'd138;
        end
        32'd136: begin
          state <= 32'd137;
        end
        32'd135: begin
          reg_72 <= {{reg_72 + reg_82} + 32'd0};
          reg_70 <= {reg_70 + 32'd1};
          state <= 32'd136;
        end
        32'd132: begin
          reg_5 <= ({reg_9 == 32'd0} ? {$signed(reg_76) < $signed(32'd50)} : reg_5);
          state <= ({{reg_9 == 32'd0} & ({reg_9 == 32'd0} ? {$signed(reg_76) < $signed(32'd50)} : reg_5)} ? 32'd18 : state);
          state <= ({{reg_9 | {({reg_9 == 32'd0} ? {$signed(reg_76) < $signed(32'd50)} : reg_5) == 32'd0}} & {{reg_9 == 32'd0} & {({reg_9 == 32'd0} ? {$signed(reg_76) < $signed(32'd50)} : reg_5) == 32'd0}}} ? 32'd4 : ({{reg_9 == 32'd0} & ({reg_9 == 32'd0} ? {$signed(reg_76) < $signed(32'd50)} : reg_5)} ? 32'd18 : state));
          state <= ({{reg_9 | {({reg_9 == 32'd0} ? {$signed(reg_76) < $signed(32'd50)} : reg_5) == 32'd0}} & {reg_9 | ({reg_9 == 32'd0} ? {$signed(reg_76) < $signed(32'd50)} : reg_5)}} ? 32'd133 : ({{reg_9 | {({reg_9 == 32'd0} ? {$signed(reg_76) < $signed(32'd50)} : reg_5) == 32'd0}} & {{reg_9 == 32'd0} & {({reg_9 == 32'd0} ? {$signed(reg_76) < $signed(32'd50)} : reg_5) == 32'd0}}} ? 32'd4 : ({{reg_9 == 32'd0} & ({reg_9 == 32'd0} ? {$signed(reg_76) < $signed(32'd50)} : reg_5)} ? 32'd18 : state)));
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
          state <= 32'd125;
        end
        32'd123: begin
          state <= 32'd124;
        end
        32'd122: begin
          reg_76 <= ({reg_9 == 32'd0} ? {reg_76 + 32'd1} : reg_76);
          state <= 32'd123;
        end
        32'd121: begin
          reg_95 <= {( - {{32'd1 & {reg_9 == 32'd0}} != 32'd0}) ^ reg_95};
          reg_94 <= 32'd1;
          reg_92 <= ({32'd1 & {reg_9 == 32'd0}} ? reg_80 : reg_92);
          reg_90 <= ({32'd1 & {reg_9 == 32'd0}} ? {{{reg_64 + 32'd0} + {reg_76 * 32'd4}} / 32'd4} : reg_90);
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
          reg_80 <= ({reg_9 == 32'd0} ? {{reg_72 * 32'd2} + 32'd0} : reg_80);
          state <= 32'd112;
        end
        32'd110: begin
          state <= 32'd266;
          reg_95 <= {( - {{reg_9 == 32'd0} != 32'd0}) ^ reg_95};
          reg_94 <= 32'd0;
          reg_90 <= ({reg_9 == 32'd0} ? 32'd100 : reg_90);
        end
        32'd109: begin
          reg_9 <= {$signed(reg_74) > $signed(32'd0)};
          reg_70 <= ({$signed(reg_74) > $signed(32'd0)} ? 32'd0 : reg_70);
          state <= ({$signed(reg_74) > $signed(32'd0)} ? 32'd13 : state);
          state <= ({{$signed(reg_74) > $signed(32'd0)} == 32'd0} ? 32'd110 : ({$signed(reg_74) > $signed(32'd0)} ? 32'd13 : state));
        end
        32'd105: begin
          state <= 32'd18;
          state <= (32'd0 ? 32'd106 : 32'd18);
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
        32'd97: begin
          state <= 32'd98;
        end
        32'd96: begin
          state <= 32'd97;
        end
        32'd53: begin
          reg_6 <= 32'd0;
          state <= 32'd52;
          state <= (32'd0 ? 32'd134 : 32'd52);
        end
        32'd52: begin
          reg_4 <= 32'd0;
          state <= 32'd51;
          state <= (32'd0 ? 32'd108 : 32'd51);
        end
        32'd51: begin
          reg_60 <= 32'd400;
          reg_62 <= {reg_6 * 32'd200};
          reg_58 <= {reg_4 + 32'd10};
          reg_52 <= 32'd0;
          reg_44 <= 32'd200;
          state <= 32'd168;
        end
        32'd32: begin
          reg_64 <= 32'd0;
          reg_66 <= 32'd400;
          reg_68 <= 32'd200;
          reg_76 <= 32'd0;
          state <= 32'd96;
        end
        32'd18: begin
          reg_74 <= stack[{{{reg_68 + 32'd0} + {reg_76 * 32'd4}} / 32'd4}];
          reg_72 <= 32'd0;
          state <= 32'd109;
        end
        32'd13: begin
          state <= 32'd292;
          reg_95 <= ( ~ reg_95);
          reg_94 <= 32'd0;
          reg_90 <= {{{reg_66 + 32'd0} + {reg_70 * 32'd4}} / 32'd4};
        end
        32'd4: begin
          reg_8 <= 32'd0;
          finish <= 32'd1;
          return_val <= 32'd0;
          state <= 32'd4;
          state <= (32'd0 ? 32'd107 : 32'd4);
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
