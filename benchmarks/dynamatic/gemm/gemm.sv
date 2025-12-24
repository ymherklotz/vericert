`timescale 1ns / 1ps

module main(start, reset, clk, finish, return_val);
  logic [31:0] reg_128 = 0;
  logic [31:0] reg_64 = 0;
  logic [31:0] reg_96 = 0;
  logic [31:0] reg_16 = 0;
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
  logic [31:0] reg_140 = 0;
  logic [31:0] reg_76 = 0;
  logic [31:0] reg_44 = 0;
  logic [31:0] reg_108 = 0;
  logic [31:0] reg_92 = 0;
  logic [31:0] reg_60 = 0;
  logic [31:0] reg_124 = 0;
  logic [31:0] reg_130 = 0;
  logic [31:0] reg_66 = 0;
  logic [31:0] reg_98 = 0;
  logic [31:0] reg_18 = 0;
  logic [31:0] reg_82 = 0;
  logic [31:0] reg_50 = 0;
  logic [31:0] reg_114 = 0;
  logic [31:0] reg_10 = 0;
  logic [31:0] reg_74 = 0;
  logic [31:0] reg_90 = 0;
  logic [31:0] reg_58 = 0;
  logic [31:0] reg_122 = 0;
  logic [31:0] reg_6 = 0;
  logic [31:0] reg_70 = 0;
  logic [31:0] reg_102 = 0;
  logic [31:0] reg_86 = 0;
  logic [31:0] reg_54 = 0;
  logic [31:0] reg_118 = 0;
  logic [31:0] reg_142 = 0;
  logic [31:0] reg_78 = 0;
  logic [31:0] reg_46 = 0;
  logic [31:0] reg_110 = 0;
  logic [31:0] reg_94 = 0;
  logic [31:0] reg_62 = 0;
  logic [31:0] reg_126 = 0;
  logic [31:0] reg_145 = 0;
  logic [31:0] reg_9 = 0;
  logic [31:0] reg_5 = 0;
  logic [31:0] reg_13 = 0;
  logic [31:0] reg_141 = 0;
  logic [31:0] reg_11 = 0;
  logic [31:0] reg_7 = 0;
  logic [31:0] reg_15 = 0;
  logic [31:0] reg_143 = 0;
  (* ram_style = "block" *)
  logic [31:0] stack [2701:0];
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
    if ({reg_145 != reg_141}) begin
      if (reg_144) begin
        stack[reg_140] <= reg_142;
      end else begin
        reg_143 <= stack[reg_140];
      end
      reg_141 <= reg_145;
    end else begin
    end
  end

  always @(posedge clk) begin
    if ({reset == 32'd1}) begin
      state <= 32'd86;
    end else begin
      case (state)
        32'd214: begin
          state <= 32'd96;
          reg_116 <= reg_143;
        end
        32'd207: begin
          state <= 32'd124;
          reg_18 <= ({reg_9 == 32'd0} ? reg_143 : reg_18);
        end
        32'd199: begin
          state <= 32'd94;
          reg_122 <= reg_143;
        end
        32'd168: begin
          state <= 32'd125;
          reg_16 <= ({reg_9 == 32'd0} ? reg_143 : reg_16);
        end
        32'd153: begin
          state <= 32'd145;
          reg_128 <= reg_143;
        end
        32'd151: begin
          state <= 32'd24;
          state <= (32'd0 ? 32'd152 : 32'd24);
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
          f_mul_a <= reg_128;
          f_mul_b <= reg_94;
          reg_98 <= f_mul_res;
          state <= 32'd146;
        end
        32'd144: begin
          state <= 32'd153;
          reg_145 <= ( ~ reg_145);
          reg_144 <= 32'd0;
          reg_140 <= {{{reg_130 + 32'd0} + {reg_102 * 32'd4}} / 32'd4};
        end
        32'd143: begin
          reg_130 <= {{reg_88 + reg_132} + 32'd0};
          state <= 32'd144;
        end
        32'd141: begin
          reg_11 <= ({reg_15 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_11);
          state <= ({{reg_15 == 32'd0} & ({reg_15 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_11)} ? 32'd78 : state);
          state <= ({{reg_15 | {({reg_15 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_11) == 32'd0}} & {{reg_15 == 32'd0} & {({reg_15 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_11) == 32'd0}}} ? 32'd52 : ({{reg_15 == 32'd0} & ({reg_15 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_11)} ? 32'd78 : state));
          state <= ({{reg_15 | {({reg_15 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_11) == 32'd0}} & {reg_15 | ({reg_15 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_11)}} ? 32'd142 : ({{reg_15 | {({reg_15 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_11) == 32'd0}} & {{reg_15 == 32'd0} & {({reg_15 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_11) == 32'd0}}} ? 32'd52 : ({{reg_15 == 32'd0} & ({reg_15 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_11)} ? 32'd78 : state)));
        end
        32'd140: begin
          reg_4 <= {reg_4 + 32'd1};
          reg_15 <= {$signed({reg_4 + 32'd1}) < $signed(32'd30)};
          state <= ({$signed({reg_4 + 32'd1}) < $signed(32'd30)} ? 32'd77 : state);
          reg_6 <= ({{$signed({reg_4 + 32'd1}) < $signed(32'd30)} == 32'd0} ? {reg_6 + 32'd1} : reg_6);
          state <= ({{$signed({reg_4 + 32'd1}) < $signed(32'd30)} == 32'd0} ? 32'd141 : ({$signed({reg_4 + 32'd1}) < $signed(32'd30)} ? 32'd77 : state));
        end
        32'd139: begin
          state <= 32'd140;
          reg_145 <= ( ~ reg_145);
          reg_144 <= 32'd1;
          reg_142 <= reg_46;
          reg_140 <= {{{reg_44 + 32'd0} + {reg_4 * 32'd4}} / 32'd4};
        end
        32'd138: begin
          state <= 32'd139;
          reg_145 <= ( ~ reg_145);
          reg_144 <= 32'd1;
          reg_142 <= reg_58;
          reg_140 <= {{{reg_56 + 32'd0} + {reg_4 * 32'd4}} / 32'd4};
        end
        32'd137: begin
          state <= 32'd138;
          reg_145 <= ( ~ reg_145);
          reg_144 <= 32'd1;
          reg_142 <= reg_70;
          reg_140 <= {{{reg_68 + 32'd0} + {reg_4 * 32'd4}} / 32'd4};
        end
        32'd136: begin
          reg_68 <= {{reg_72 + reg_74} + 32'd0};
          reg_56 <= {{reg_60 + reg_62} + 32'd0};
          reg_48 <= {{reg_52 + reg_54} + 32'd0};
          reg_44 <= {{{{reg_52 + reg_54} + 32'd0} + reg_50} + 32'd0};
          state <= 32'd137;
        end
        32'd135: begin
          reg_72 <= {{reg_76 + reg_78} + 32'd0};
          reg_66 <= reg_78;
          reg_54 <= reg_78;
          reg_60 <= {{reg_64 + reg_78} + 32'd0};
          reg_62 <= reg_74;
          reg_50 <= reg_74;
          state <= 32'd136;
        end
        32'd133: begin
          state <= 32'd78;
          state <= (32'd0 ? 32'd134 : 32'd78);
        end
        32'd132: begin
          state <= 32'd133;
          reg_145 <= ( ~ reg_145);
          reg_144 <= 32'd1;
          reg_142 <= reg_82;
          reg_140 <= {{{reg_80 + 32'd0} + {reg_8 * 32'd4}} / 32'd4};
        end
        32'd131: begin
          state <= 32'd132;
          reg_145 <= ( ~ reg_145);
          reg_144 <= 32'd1;
          reg_142 <= reg_86;
          reg_140 <= {{{reg_84 + 32'd0} + {reg_8 * 32'd4}} / 32'd4};
        end
        32'd126: begin
          reg_96 <= ({reg_9 == 32'd0} ? reg_16 : reg_96);
          state <= ({reg_9 == 32'd0} ? 32'd30 : state);
          state <= (reg_9 ? 32'd127 : ({reg_9 == 32'd0} ? 32'd30 : state));
        end
        32'd125: begin
          reg_94 <= ({reg_9 == 32'd0} ? reg_18 : reg_94);
          state <= 32'd126;
        end
        32'd124: begin
          state <= 32'd168;
          reg_145 <= {( - {{reg_9 == 32'd0} != 32'd0}) ^ reg_145};
          reg_144 <= 32'd0;
          reg_140 <= ({reg_9 == 32'd0} ? 32'd0 : reg_140);
        end
        32'd123: begin
          state <= 32'd207;
          reg_145 <= {( - {{reg_9 == 32'd0} != 32'd0}) ^ reg_145};
          reg_144 <= 32'd0;
          reg_140 <= ({reg_9 == 32'd0} ? 32'd1 : reg_140);
        end
        32'd121: begin
          reg_102 <= ({reg_7 == 32'd0} ? {reg_102 + 32'd1} : reg_102);
          reg_13 <= ({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_102 + 32'd1} : reg_102)) < $signed(32'd20)} : reg_13);
          state <= ({{reg_7 == 32'd0} & ({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_102 + 32'd1} : reg_102)) < $signed(32'd20)} : reg_13)} ? 32'd29 : state);
          state <= ({{reg_7 | {({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_102 + 32'd1} : reg_102)) < $signed(32'd20)} : reg_13) == 32'd0}} & {{reg_7 == 32'd0} & {({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_102 + 32'd1} : reg_102)) < $signed(32'd20)} : reg_13) == 32'd0}}} ? 32'd8 : ({{reg_7 == 32'd0} & ({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_102 + 32'd1} : reg_102)) < $signed(32'd20)} : reg_13)} ? 32'd29 : state));
          state <= ({{reg_7 | {({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_102 + 32'd1} : reg_102)) < $signed(32'd20)} : reg_13) == 32'd0}} & {reg_7 | ({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_102 + 32'd1} : reg_102)) < $signed(32'd20)} : reg_13)}} ? 32'd122 : ({{reg_7 | {({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_102 + 32'd1} : reg_102)) < $signed(32'd20)} : reg_13) == 32'd0}} & {{reg_7 == 32'd0} & {({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_102 + 32'd1} : reg_102)) < $signed(32'd20)} : reg_13) == 32'd0}}} ? 32'd8 : ({{reg_7 == 32'd0} & ({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_102 + 32'd1} : reg_102)) < $signed(32'd20)} : reg_13)} ? 32'd29 : state)));
        end
        32'd120: begin
          reg_145 <= {( - {{32'd1 & {reg_7 == 32'd0}} != 32'd0}) ^ reg_145};
          reg_144 <= 32'd1;
          reg_142 <= ({32'd1 & {reg_7 == 32'd0}} ? reg_98 : reg_142);
          reg_140 <= ({32'd1 & {reg_7 == 32'd0}} ? {{{reg_108 + 32'd0} + {reg_102 * 32'd4}} / 32'd4} : reg_140);
          state <= 32'd121;
        end
        32'd119: begin
          reg_108 <= ({reg_7 == 32'd0} ? {{reg_88 + reg_110} + 32'd0} : reg_108);
          state <= 32'd120;
        end
        32'd118: begin
          state <= (reg_7 ? 32'd24 : state);
          reg_110 <= ({reg_7 == 32'd0} ? reg_126 : reg_110);
          state <= ({reg_7 == 32'd0} ? 32'd119 : (reg_7 ? 32'd24 : state));
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
          f_add_a <= reg_98;
          f_add_b <= reg_112;
          reg_98 <= f_add_res;
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
          f_mul_a <= reg_114;
          f_mul_b <= reg_116;
          reg_112 <= f_mul_res;
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
          reg_7 <= {$signed(reg_100) < $signed(32'd20)};
          state <= 32'd98;
        end
        32'd96: begin
          reg_100 <= {reg_100 + 32'd1};
          state <= 32'd97;
        end
        32'd95: begin
          state <= 32'd214;
          reg_145 <= ( ~ reg_145);
          reg_144 <= 32'd0;
          reg_140 <= {{{reg_118 + 32'd0} + {reg_102 * 32'd4}} / 32'd4};
        end
        32'd94: begin
          f_mul_a <= reg_96;
          f_mul_b <= reg_122;
          reg_114 <= f_mul_res;
          state <= 32'd95;
        end
        32'd93: begin
          state <= 32'd199;
          reg_145 <= ( ~ reg_145);
          reg_144 <= 32'd0;
          reg_140 <= {{{reg_124 + 32'd0} + {reg_100 * 32'd4}} / 32'd4};
        end
        32'd92: begin
          reg_124 <= {{reg_92 + reg_126} + 32'd0};
          reg_118 <= {{reg_90 + reg_120} + 32'd0};
          state <= 32'd93;
        end
        32'd90: begin
          finish <= ({reg_5 == 32'd0} ? 32'd1 : finish);
          return_val <= ({reg_5 == 32'd0} ? reg_10 : return_val);
          state <= ({reg_5 == 32'd0} ? 32'd90 : state);
          state <= (reg_5 ? 32'd91 : ({reg_5 == 32'd0} ? 32'd90 : state));
        end
        32'd86: begin
          reg_8 <= 32'd0;
          state <= 32'd85;
          state <= (32'd0 ? 32'd128 : 32'd85);
        end
        32'd85: begin
          reg_84 <= 32'd0;
          reg_86 <= 32'd1065353216;
          reg_82 <= 32'd1065353216;
          reg_80 <= 32'd4;
          reg_6 <= 32'd0;
          state <= 32'd131;
        end
        32'd78: begin
          reg_4 <= 32'd0;
          state <= 32'd77;
          state <= (32'd0 ? 32'd129 : 32'd77);
        end
        32'd77: begin
          reg_76 <= 32'd3608;
          reg_78 <= {reg_8 * 32'd3600};
          reg_74 <= {reg_6 * 32'd120};
          reg_70 <= 32'd1073741824;
          reg_64 <= 32'd7208;
          reg_58 <= 32'd1077936128;
          reg_52 <= 32'd8;
          reg_46 <= 32'd1065353216;
          state <= 32'd135;
        end
        32'd52: begin
          reg_8 <= {reg_8 + 32'd1};
          reg_9 <= {$signed({reg_8 + 32'd1}) < $signed(32'd1)};
          state <= ({$signed({reg_8 + 32'd1}) < $signed(32'd1)} ? 32'd85 : state);
          reg_104 <= ({{$signed({reg_8 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd0 : reg_104);
          reg_92 <= ({{$signed({reg_8 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd3608 : reg_92);
          reg_90 <= ({{$signed({reg_8 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd7208 : reg_90);
          reg_88 <= ({{$signed({reg_8 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd8 : reg_88);
          state <= ({{$signed({reg_8 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd123 : ({$signed({reg_8 + 32'd1}) < $signed(32'd1)} ? 32'd85 : state));
        end
        32'd30: begin
          reg_102 <= 32'd0;
          state <= 32'd29;
          state <= (32'd0 ? 32'd130 : 32'd29);
        end
        32'd29: begin
          reg_132 <= {reg_104 * 32'd120};
          reg_100 <= 32'd0;
          state <= 32'd143;
        end
        32'd24: begin
          reg_126 <= {reg_104 * 32'd120};
          reg_120 <= {reg_100 * 32'd120};
          state <= 32'd92;
        end
        32'd8: begin
          reg_104 <= {reg_104 + 32'd1};
          reg_5 <= {$signed({reg_104 + 32'd1}) < $signed(32'd20)};
          state <= ({$signed({reg_104 + 32'd1}) < $signed(32'd20)} ? 32'd30 : state);
          reg_10 <= ({{$signed({reg_104 + 32'd1}) < $signed(32'd20)} == 32'd0} ? 32'd1208 : reg_10);
          state <= ({{$signed({reg_104 + 32'd1}) < $signed(32'd20)} == 32'd0} ? 32'd90 : ({$signed({reg_104 + 32'd1}) < $signed(32'd20)} ? 32'd30 : state));
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
