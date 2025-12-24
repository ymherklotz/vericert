`timescale 1ns / 1ps

module main(start, reset, clk, finish, return_val);
  logic [31:0] reg_64 = 0;
  logic [31:0] reg_96 = 0;
  logic [31:0] reg_16 = 0;
  logic [31:0] reg_80 = 0;
  logic [31:0] reg_112 = 0;
  logic [31:0] reg_8 = 0;
  logic [31:0] reg_72 = 0;
  logic [31:0] reg_40 = 0;
  logic [31:0] reg_104 = 0;
  logic [31:0] reg_88 = 0;
  logic [31:0] reg_56 = 0;
  logic [31:0] reg_120 = 0;
  logic [31:0] reg_4 = 0;
  logic [31:0] reg_68 = 0;
  logic [31:0] reg_100 = 0;
  logic [31:0] reg_20 = 0;
  logic [31:0] reg_84 = 0;
  logic [31:0] reg_52 = 0;
  logic [31:0] reg_12 = 0;
  logic [31:0] reg_76 = 0;
  logic [31:0] reg_44 = 0;
  logic [31:0] reg_108 = 0;
  logic [31:0] reg_92 = 0;
  logic [31:0] reg_60 = 0;
  logic [31:0] reg_124 = 0;
  logic [31:0] reg_2 = 0;
  logic [31:0] reg_66 = 0;
  logic [31:0] reg_98 = 0;
  logic [31:0] reg_18 = 0;
  logic [31:0] reg_82 = 0;
  logic [31:0] reg_50 = 0;
  logic [31:0] reg_10 = 0;
  logic [31:0] reg_74 = 0;
  logic [31:0] reg_42 = 0;
  logic [31:0] reg_106 = 0;
  logic [31:0] reg_90 = 0;
  logic [31:0] reg_58 = 0;
  logic [31:0] reg_122 = 0;
  logic [31:0] reg_6 = 0;
  logic [31:0] reg_70 = 0;
  logic [31:0] reg_102 = 0;
  logic [31:0] reg_86 = 0;
  logic [31:0] reg_54 = 0;
  logic [31:0] reg_78 = 0;
  logic [31:0] reg_94 = 0;
  logic [31:0] reg_62 = 0;
  logic [31:0] reg_9 = 0;
  logic [31:0] reg_121 = 0;
  logic [31:0] reg_5 = 0;
  logic [31:0] reg_13 = 0;
  logic [31:0] reg_125 = 0;
  logic [31:0] reg_11 = 0;
  logic [31:0] reg_123 = 0;
  logic [31:0] reg_7 = 0;
  logic [31:0] reg_15 = 0;
  (* ram_style = "block" *)
  logic [31:0] stack [149:0];
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
    if ({reg_125 != reg_121}) begin
      if (reg_124) begin
        stack[reg_120] <= reg_122;
      end else begin
        reg_123 <= stack[reg_120];
      end
      reg_121 <= reg_125;
    end else begin
    end
  end

  always @(posedge clk) begin
    if ({reset == 32'd1}) begin
      state <= 32'd75;
    end else begin
      case (state)
        32'd191: begin
          state <= 32'd120;
          reg_100 <= ({reg_15 == 32'd0} ? reg_123 : reg_100);
        end
        32'd181: begin
          state <= 32'd117;
          reg_102 <= reg_123;
        end
        32'd160: begin
          state <= 32'd84;
          reg_112 <= reg_123;
        end
        32'd137: begin
          reg_13 <= ({reg_11 == 32'd0} ? {$signed(reg_18) < $signed(32'd1)} : reg_13);
          state <= ({{reg_11 == 32'd0} & ({reg_11 == 32'd0} ? {$signed(reg_18) < $signed(32'd1)} : reg_13)} ? 32'd74 : state);
          reg_104 <= ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(reg_18) < $signed(32'd1)} : reg_13) == 32'd0}} & {{reg_11 == 32'd0} & {({reg_11 == 32'd0} ? {$signed(reg_18) < $signed(32'd1)} : reg_13) == 32'd0}}} ? 32'd0 : reg_104);
          reg_96 <= ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(reg_18) < $signed(32'd1)} : reg_13) == 32'd0}} & {{reg_11 == 32'd0} & {({reg_11 == 32'd0} ? {$signed(reg_18) < $signed(32'd1)} : reg_13) == 32'd0}}} ? 32'd200 : reg_96);
          reg_94 <= ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(reg_18) < $signed(32'd1)} : reg_13) == 32'd0}} & {{reg_11 == 32'd0} & {({reg_11 == 32'd0} ? {$signed(reg_18) < $signed(32'd1)} : reg_13) == 32'd0}}} ? 32'd400 : reg_94);
          reg_92 <= ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(reg_18) < $signed(32'd1)} : reg_13) == 32'd0}} & {{reg_11 == 32'd0} & {({reg_11 == 32'd0} ? {$signed(reg_18) < $signed(32'd1)} : reg_13) == 32'd0}}} ? 32'd0 : reg_92);
          state <= ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(reg_18) < $signed(32'd1)} : reg_13) == 32'd0}} & {{reg_11 == 32'd0} & {({reg_11 == 32'd0} ? {$signed(reg_18) < $signed(32'd1)} : reg_13) == 32'd0}}} ? 32'd19 : ({{reg_11 == 32'd0} & ({reg_11 == 32'd0} ? {$signed(reg_18) < $signed(32'd1)} : reg_13)} ? 32'd74 : state));
          state <= ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(reg_18) < $signed(32'd1)} : reg_13) == 32'd0}} & {reg_11 | ({reg_11 == 32'd0} ? {$signed(reg_18) < $signed(32'd1)} : reg_13)}} ? 32'd138 : ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(reg_18) < $signed(32'd1)} : reg_13) == 32'd0}} & {{reg_11 == 32'd0} & {({reg_11 == 32'd0} ? {$signed(reg_18) < $signed(32'd1)} : reg_13) == 32'd0}}} ? 32'd19 : ({{reg_11 == 32'd0} & ({reg_11 == 32'd0} ? {$signed(reg_18) < $signed(32'd1)} : reg_13)} ? 32'd74 : state)));
        end
        32'd136: begin
          reg_16 <= {reg_16 + 32'd1};
          reg_11 <= {$signed({reg_16 + 32'd1}) < $signed(32'd50)};
          state <= ({$signed({reg_16 + 32'd1}) < $signed(32'd50)} ? 32'd73 : state);
          reg_18 <= ({{$signed({reg_16 + 32'd1}) < $signed(32'd50)} == 32'd0} ? {reg_18 + 32'd1} : reg_18);
          state <= ({{$signed({reg_16 + 32'd1}) < $signed(32'd50)} == 32'd0} ? 32'd137 : ({$signed({reg_16 + 32'd1}) < $signed(32'd50)} ? 32'd73 : state));
        end
        32'd135: begin
          state <= 32'd136;
          reg_125 <= ( ~ reg_125);
          reg_124 <= 32'd1;
          reg_122 <= reg_42;
          reg_120 <= {{{reg_40 + 32'd0} + {reg_16 * 32'd4}} / 32'd4};
        end
        32'd132: begin
          reg_12 <= ({{reg_15 == 32'd0} & {reg_7 == 32'd0}} ? reg_106 : reg_12);
          reg_20 <= ({{reg_15 == 32'd0} & {reg_7 == 32'd0}} ? ({{reg_15 == 32'd0} & {reg_7 == 32'd0}} ? reg_106 : reg_12) : reg_20);
          finish <= ({{reg_15 == 32'd0} & {reg_7 == 32'd0}} ? 32'd1 : finish);
          return_val <= ({{reg_15 == 32'd0} & {reg_7 == 32'd0}} ? ({{reg_15 == 32'd0} & {reg_7 == 32'd0}} ? ({{reg_15 == 32'd0} & {reg_7 == 32'd0}} ? reg_106 : reg_12) : reg_20) : return_val);
          state <= ({{reg_15 == 32'd0} & {reg_7 == 32'd0}} ? 32'd132 : state);
          state <= ({reg_15 | reg_7} ? 32'd133 : ({{reg_15 == 32'd0} & {reg_7 == 32'd0}} ? 32'd132 : state));
        end
        32'd131: begin
          reg_104 <= ({reg_15 == 32'd0} ? {reg_104 + 32'd1} : reg_104);
          reg_7 <= ({reg_15 == 32'd0} ? {$signed(({reg_15 == 32'd0} ? {reg_104 + 32'd1} : reg_104)) < $signed(32'd50)} : reg_7);
          state <= ({{reg_15 == 32'd0} & ({reg_15 == 32'd0} ? {$signed(({reg_15 == 32'd0} ? {reg_104 + 32'd1} : reg_104)) < $signed(32'd50)} : reg_7)} ? 32'd19 : state);
          reg_106 <= ({{reg_15 | {({reg_15 == 32'd0} ? {$signed(({reg_15 == 32'd0} ? {reg_104 + 32'd1} : reg_104)) < $signed(32'd50)} : reg_7) == 32'd0}} & {{reg_15 == 32'd0} & {({reg_15 == 32'd0} ? {$signed(({reg_15 == 32'd0} ? {reg_104 + 32'd1} : reg_104)) < $signed(32'd50)} : reg_7) == 32'd0}}} ? ({reg_15 == 32'd0} ? {reg_104 + 32'd1} : reg_104) : reg_106);
          state <= ({reg_15 | {({reg_15 == 32'd0} ? {$signed(({reg_15 == 32'd0} ? {reg_104 + 32'd1} : reg_104)) < $signed(32'd50)} : reg_7) == 32'd0}} ? 32'd132 : ({{reg_15 == 32'd0} & ({reg_15 == 32'd0} ? {$signed(({reg_15 == 32'd0} ? {reg_104 + 32'd1} : reg_104)) < $signed(32'd50)} : reg_7)} ? 32'd19 : state));
        end
        32'd130: begin
          reg_125 <= {( - {{32'd1 & {reg_15 == 32'd0}} != 32'd0}) ^ reg_125};
          reg_124 <= 32'd1;
          reg_122 <= ({32'd1 & {reg_15 == 32'd0}} ? reg_108 : reg_122);
          reg_120 <= ({32'd1 & {reg_15 == 32'd0}} ? {{{reg_92 + 32'd0} + {reg_104 * 32'd4}} / 32'd4} : reg_120);
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
        32'd120: begin
          reg_108 <= ({reg_15 == 32'd0} ? {reg_100 + reg_100} : reg_108);
          state <= 32'd121;
        end
        32'd119: begin
          state <= 32'd191;
          reg_125 <= {( - {{reg_15 == 32'd0} != 32'd0}) ^ reg_125};
          reg_124 <= 32'd0;
          reg_120 <= ({reg_15 == 32'd0} ? 32'd100 : reg_120);
        end
        32'd118: begin
          reg_15 <= {$signed(reg_102) > $signed(32'd0)};
          reg_98 <= ({$signed(reg_102) > $signed(32'd0)} ? 32'd0 : reg_98);
          state <= ({$signed(reg_102) > $signed(32'd0)} ? 32'd14 : state);
          state <= ({{$signed(reg_102) > $signed(32'd0)} == 32'd0} ? 32'd119 : ({$signed(reg_102) > $signed(32'd0)} ? 32'd14 : state));
        end
        32'd117: begin
          reg_100 <= 32'd0;
          state <= 32'd118;
        end
        32'd115: begin
          state <= ({reg_13 == 32'd0} ? 32'd19 : state);
          state <= (reg_13 ? 32'd116 : ({reg_13 == 32'd0} ? 32'd19 : state));
        end
        32'd113: begin
          state <= ({{reg_9 == 32'd0} & {reg_11 == 32'd0}} ? 32'd35 : state);
          state <= ({reg_9 | reg_11} ? 32'd114 : ({{reg_9 == 32'd0} & {reg_11 == 32'd0}} ? 32'd35 : state));
        end
        32'd112: begin
          state <= (reg_9 ? 32'd43 : state);
          reg_16 <= ({reg_9 == 32'd0} ? {reg_16 + 32'd1} : reg_16);
          reg_11 <= ({reg_9 == 32'd0} ? {$signed(({reg_9 == 32'd0} ? {reg_16 + 32'd1} : reg_16)) < $signed(32'd50)} : reg_11);
          state <= ({{reg_9 == 32'd0} & {{reg_9 == 32'd0} & ({reg_9 == 32'd0} ? {$signed(({reg_9 == 32'd0} ? {reg_16 + 32'd1} : reg_16)) < $signed(32'd50)} : reg_11)}} ? 32'd73 : (reg_9 ? 32'd43 : state));
          state <= ({{reg_9 == 32'd0} & {reg_9 | {({reg_9 == 32'd0} ? {$signed(({reg_9 == 32'd0} ? {reg_16 + 32'd1} : reg_16)) < $signed(32'd50)} : reg_11) == 32'd0}}} ? 32'd113 : ({{reg_9 == 32'd0} & {{reg_9 == 32'd0} & ({reg_9 == 32'd0} ? {$signed(({reg_9 == 32'd0} ? {reg_16 + 32'd1} : reg_16)) < $signed(32'd50)} : reg_11)}} ? 32'd73 : (reg_9 ? 32'd43 : state)));
        end
        32'd111: begin
          state <= 32'd112;
          reg_125 <= ( ~ reg_125);
          reg_124 <= 32'd1;
          reg_122 <= reg_16;
          reg_120 <= {{{reg_70 + 32'd0} + {reg_16 * 32'd4}} / 32'd4};
        end
        32'd110: begin
          state <= 32'd111;
          reg_125 <= ( ~ reg_125);
          reg_124 <= 32'd1;
          reg_122 <= reg_78;
          reg_120 <= {{{reg_76 + 32'd0} + {reg_16 * 32'd4}} / 32'd4};
        end
        32'd109: begin
          reg_70 <= {{reg_72 + reg_74} + 32'd0};
          state <= 32'd110;
        end
        32'd108: begin
          state <= 32'd109;
          reg_125 <= ( ~ reg_125);
          reg_124 <= 32'd1;
          reg_122 <= reg_86;
          reg_120 <= {{{reg_84 + 32'd0} + {reg_16 * 32'd4}} / 32'd4};
        end
        32'd107: begin
          reg_84 <= {{reg_88 + reg_90} + 32'd0};
          reg_82 <= reg_90;
          reg_74 <= reg_90;
          reg_76 <= {{reg_80 + reg_90} + 32'd0};
          reg_8 <= ({reg_6 != 32'd0} ? reg_54 : reg_56);
          reg_10 <= ({({reg_6 != 32'd0} ? reg_54 : reg_56) != 32'd0} ? reg_50 : reg_52);
          reg_9 <= {({({reg_6 != 32'd0} ? reg_54 : reg_56) != 32'd0} ? reg_50 : reg_52) != 32'd0};
          state <= 32'd108;
        end
        32'd105: begin
          reg_104 <= ({reg_5 == 32'd0} ? {reg_104 + 32'd1} : reg_104);
          reg_7 <= ({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_104 + 32'd1} : reg_104)) < $signed(32'd50)} : reg_7);
          state <= ({{reg_5 == 32'd0} & ({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_104 + 32'd1} : reg_104)) < $signed(32'd50)} : reg_7)} ? 32'd19 : state);
          state <= ({{reg_5 | {({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_104 + 32'd1} : reg_104)) < $signed(32'd50)} : reg_7) == 32'd0}} & {{reg_5 == 32'd0} & {({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_104 + 32'd1} : reg_104)) < $signed(32'd50)} : reg_7) == 32'd0}}} ? 32'd4 : ({{reg_5 == 32'd0} & ({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_104 + 32'd1} : reg_104)) < $signed(32'd50)} : reg_7)} ? 32'd19 : state));
          state <= ({{reg_5 | {({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_104 + 32'd1} : reg_104)) < $signed(32'd50)} : reg_7) == 32'd0}} & {reg_5 | ({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_104 + 32'd1} : reg_104)) < $signed(32'd50)} : reg_7)}} ? 32'd106 : ({{reg_5 | {({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_104 + 32'd1} : reg_104)) < $signed(32'd50)} : reg_7) == 32'd0}} & {{reg_5 == 32'd0} & {({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_104 + 32'd1} : reg_104)) < $signed(32'd50)} : reg_7) == 32'd0}}} ? 32'd4 : ({{reg_5 == 32'd0} & ({reg_5 == 32'd0} ? {$signed(({reg_5 == 32'd0} ? {reg_104 + 32'd1} : reg_104)) < $signed(32'd50)} : reg_7)} ? 32'd19 : state)));
        end
        32'd104: begin
          reg_125 <= {( - {{32'd1 & {reg_5 == 32'd0}} != 32'd0}) ^ reg_125};
          reg_124 <= 32'd1;
          reg_122 <= ({32'd1 & {reg_5 == 32'd0}} ? reg_108 : reg_122);
          reg_120 <= ({32'd1 & {reg_5 == 32'd0}} ? {{{reg_92 + 32'd0} + {reg_104 * 32'd4}} / 32'd4} : reg_120);
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
        32'd95: begin
          state <= 32'd96;
        end
        32'd94: begin
          state <= (reg_5 ? 32'd14 : state);
          reg_108 <= ({reg_5 == 32'd0} ? {reg_100 + reg_100} : reg_108);
          state <= ({reg_5 == 32'd0} ? 32'd95 : (reg_5 ? 32'd14 : state));
        end
        32'd93: begin
          state <= 32'd94;
        end
        32'd92: begin
          state <= 32'd93;
        end
        32'd91: begin
          state <= 32'd92;
        end
        32'd90: begin
          state <= 32'd91;
        end
        32'd89: begin
          state <= 32'd90;
        end
        32'd88: begin
          state <= 32'd89;
        end
        32'd87: begin
          state <= 32'd88;
        end
        32'd86: begin
          state <= 32'd87;
        end
        32'd85: begin
          state <= 32'd86;
        end
        32'd84: begin
          f_add_a <= reg_100;
          f_add_b <= reg_112;
          reg_100 <= f_add_res;
          reg_98 <= {reg_98 + 32'd1};
          reg_5 <= {$signed({reg_98 + 32'd1}) < $signed(32'd5)};
          state <= 32'd85;
        end
        32'd75: begin
          reg_18 <= 32'd0;
          state <= 32'd74;
          state <= (32'd0 ? 32'd134 : 32'd74);
        end
        32'd74: begin
          reg_16 <= 32'd0;
          state <= 32'd73;
          state <= (32'd0 ? 32'd83 : 32'd73);
        end
        32'd73: begin
          reg_88 <= 32'd400;
          reg_90 <= {reg_18 * 32'd200};
          reg_86 <= 32'd1092616192;
          reg_78 <= 32'd1092616192;
          reg_80 <= 32'd0;
          reg_72 <= 32'd200;
          reg_66 <= 32'd1;
          reg_68 <= {reg_16 == 32'd10};
          reg_62 <= 32'd1;
          reg_64 <= {reg_16 == 32'd20};
          reg_58 <= 32'd1;
          reg_60 <= {reg_16 == 32'd30};
          reg_2 <= ({reg_16 == 32'd0} ? 32'd1 : {reg_16 == 32'd10});
          reg_4 <= ({({reg_16 == 32'd0} ? 32'd1 : {reg_16 == 32'd10}) != 32'd0} ? 32'd1 : {reg_16 == 32'd20});
          reg_6 <= ({({({reg_16 == 32'd0} ? 32'd1 : {reg_16 == 32'd10}) != 32'd0} ? 32'd1 : {reg_16 == 32'd20}) != 32'd0} ? 32'd1 : {reg_16 == 32'd30});
          reg_54 <= 32'd1;
          reg_56 <= {reg_16 == 32'd40};
          reg_52 <= {reg_16 == 32'd40};
          reg_50 <= 32'd1;
          state <= 32'd107;
        end
        32'd43: begin
          reg_40 <= reg_70;
          reg_44 <= 32'd1;
          reg_42 <= {32'd1 - reg_16};
          state <= 32'd135;
        end
        32'd35: begin
          reg_18 <= {reg_18 + 32'd1};
          reg_13 <= {$signed({reg_18 + 32'd1}) < $signed(32'd1)};
          state <= ({$signed({reg_18 + 32'd1}) < $signed(32'd1)} ? 32'd74 : state);
          reg_104 <= ({{$signed({reg_18 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd0 : reg_104);
          reg_96 <= ({{$signed({reg_18 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd200 : reg_96);
          reg_94 <= ({{$signed({reg_18 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd400 : reg_94);
          reg_92 <= ({{$signed({reg_18 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd0 : reg_92);
          state <= ({{$signed({reg_18 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd115 : ({$signed({reg_18 + 32'd1}) < $signed(32'd1)} ? 32'd74 : state));
        end
        32'd19: begin
          state <= 32'd181;
          reg_125 <= ( ~ reg_125);
          reg_124 <= 32'd0;
          reg_120 <= {{{reg_96 + 32'd0} + {reg_104 * 32'd4}} / 32'd4};
        end
        32'd14: begin
          state <= 32'd160;
          reg_125 <= ( ~ reg_125);
          reg_124 <= 32'd0;
          reg_120 <= {{{reg_94 + 32'd0} + {reg_98 * 32'd4}} / 32'd4};
        end
        32'd4: begin
          reg_106 <= reg_104;
          reg_12 <= reg_104;
          reg_20 <= reg_104;
          finish <= 32'd1;
          return_val <= reg_104;
          state <= 32'd4;
          state <= (32'd0 ? 32'd82 : 32'd4);
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
