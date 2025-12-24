`timescale 1ns / 1ps

module main(start, reset, clk, finish, return_val);
  logic [31:0] reg_64 = 0;
  logic [31:0] reg_80 = 0;
  logic [31:0] reg_48 = 0;
  logic [31:0] reg_8 = 0;
  logic [31:0] reg_72 = 0;
  logic [31:0] reg_40 = 0;
  logic [31:0] reg_88 = 0;
  logic [31:0] reg_56 = 0;
  logic [31:0] reg_4 = 0;
  logic [31:0] reg_68 = 0;
  logic [31:0] reg_52 = 0;
  logic [31:0] reg_12 = 0;
  logic [31:0] reg_76 = 0;
  logic [31:0] reg_44 = 0;
  logic [31:0] reg_92 = 0;
  logic [31:0] reg_60 = 0;
  logic [31:0] reg_66 = 0;
  logic [31:0] reg_50 = 0;
  logic [31:0] reg_10 = 0;
  logic [31:0] reg_74 = 0;
  logic [31:0] reg_42 = 0;
  logic [31:0] reg_90 = 0;
  logic [31:0] reg_58 = 0;
  logic [31:0] reg_6 = 0;
  logic [31:0] reg_38 = 0;
  logic [31:0] reg_54 = 0;
  logic [31:0] reg_78 = 0;
  logic [31:0] reg_46 = 0;
  logic [31:0] reg_62 = 0;
  logic [31:0] reg_9 = 0;
  logic [31:0] reg_89 = 0;
  logic [31:0] reg_5 = 0;
  logic [31:0] reg_13 = 0;
  logic [31:0] reg_93 = 0;
  logic [31:0] reg_11 = 0;
  logic [31:0] reg_91 = 0;
  logic [31:0] reg_7 = 0;
  (* ram_style = "block" *)
  logic [31:0] stack [959:0];
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
    if ({reg_93 != reg_89}) begin
      if (reg_92) begin
        stack[reg_88] <= reg_90;
      end else begin
        reg_91 <= stack[reg_88];
      end
      reg_89 <= reg_93;
    end else begin
    end
  end

  always @(posedge clk) begin
    if ({reset == 32'd1}) begin
      state <= 32'd56;
    end else begin
      case (state)
        32'd131: begin
          state <= 32'd96;
          reg_12 <= reg_91;
        end
        32'd121: begin
          state <= 32'd70;
          reg_76 <= reg_91;
        end
        32'd109: begin
          state <= 32'd67;
          reg_74 <= reg_91;
        end
        32'd96: begin
          reg_10 <= reg_12;
          finish <= 32'd1;
          return_val <= reg_12;
          state <= 32'd96;
          state <= (32'd0 ? 32'd97 : 32'd96);
        end
        32'd94: begin
          state <= ({reg_11 == 32'd0} ? 32'd20 : state);
          state <= (reg_11 ? 32'd95 : ({reg_11 == 32'd0} ? 32'd20 : state));
        end
        32'd92: begin
          state <= 32'd48;
          state <= (32'd0 ? 32'd93 : 32'd48);
        end
        32'd91: begin
          state <= 32'd92;
          reg_93 <= ( ~ reg_93);
          reg_92 <= 32'd1;
          reg_90 <= reg_52;
          reg_88 <= {{{reg_50 + 32'd0} + {reg_6 * 32'd4}} / 32'd4};
        end
        32'd90: begin
          reg_50 <= {{reg_54 + reg_56} + 32'd0};
          state <= 32'd91;
        end
        32'd88: begin
          reg_68 <= ({reg_7 == 32'd0} ? {reg_68 + 32'd1} : reg_68);
          reg_9 <= ({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_68 + 32'd1} : reg_68)) < $signed(32'd30)} : reg_9);
          state <= ({{reg_7 == 32'd0} & ({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_68 + 32'd1} : reg_68)) < $signed(32'd30)} : reg_9)} ? 32'd20 : state);
          state <= ({{reg_7 | {({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_68 + 32'd1} : reg_68)) < $signed(32'd30)} : reg_9) == 32'd0}} & {{reg_7 == 32'd0} & {({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_68 + 32'd1} : reg_68)) < $signed(32'd30)} : reg_9) == 32'd0}}} ? 32'd7 : ({{reg_7 == 32'd0} & ({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_68 + 32'd1} : reg_68)) < $signed(32'd30)} : reg_9)} ? 32'd20 : state));
          state <= ({{reg_7 | {({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_68 + 32'd1} : reg_68)) < $signed(32'd30)} : reg_9) == 32'd0}} & {reg_7 | ({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_68 + 32'd1} : reg_68)) < $signed(32'd30)} : reg_9)}} ? 32'd89 : ({{reg_7 | {({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_68 + 32'd1} : reg_68)) < $signed(32'd30)} : reg_9) == 32'd0}} & {{reg_7 == 32'd0} & {({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_68 + 32'd1} : reg_68)) < $signed(32'd30)} : reg_9) == 32'd0}}} ? 32'd7 : ({{reg_7 == 32'd0} & ({reg_7 == 32'd0} ? {$signed(({reg_7 == 32'd0} ? {reg_68 + 32'd1} : reg_68)) < $signed(32'd30)} : reg_9)} ? 32'd20 : state)));
        end
        32'd87: begin
          reg_93 <= {( - {{32'd1 & {reg_7 == 32'd0}} != 32'd0}) ^ reg_93};
          reg_92 <= 32'd1;
          reg_90 <= ({32'd1 & {reg_7 == 32'd0}} ? reg_64 : reg_90);
          reg_88 <= ({32'd1 & {reg_7 == 32'd0}} ? {{{reg_58 + 32'd0} + {reg_68 * 32'd4}} / 32'd4} : reg_88);
          state <= 32'd88;
        end
        32'd86: begin
          state <= (reg_7 ? 32'd18 : state);
          state <= ({reg_7 == 32'd0} ? 32'd87 : (reg_7 ? 32'd18 : state));
        end
        32'd85: begin
          state <= 32'd86;
        end
        32'd84: begin
          state <= 32'd85;
        end
        32'd83: begin
          state <= 32'd84;
        end
        32'd82: begin
          state <= 32'd83;
        end
        32'd81: begin
          state <= 32'd82;
        end
        32'd80: begin
          state <= 32'd81;
        end
        32'd79: begin
          state <= 32'd80;
        end
        32'd78: begin
          state <= 32'd79;
        end
        32'd77: begin
          state <= 32'd78;
        end
        32'd76: begin
          f_add_a <= reg_64;
          f_add_b <= reg_72;
          reg_64 <= f_add_res;
          state <= 32'd77;
        end
        32'd75: begin
          state <= 32'd76;
        end
        32'd74: begin
          state <= 32'd75;
        end
        32'd73: begin
          state <= 32'd74;
        end
        32'd72: begin
          state <= 32'd73;
        end
        32'd71: begin
          state <= 32'd72;
        end
        32'd70: begin
          f_mul_a <= reg_74;
          f_mul_b <= reg_76;
          reg_72 <= f_mul_res;
          reg_66 <= {reg_66 + 32'd1};
          reg_7 <= {$signed({reg_66 + 32'd1}) < $signed(32'd30)};
          state <= 32'd71;
        end
        32'd69: begin
          state <= 32'd121;
          reg_93 <= ( ~ reg_93);
          reg_92 <= 32'd0;
          reg_88 <= {{{reg_78 + 32'd0} + {reg_66 * 32'd4}} / 32'd4};
        end
        32'd68: begin
          reg_78 <= {{reg_62 + reg_80} + 32'd0};
          state <= 32'd69;
        end
        32'd67: begin
          reg_80 <= {reg_68 * 32'd120};
          state <= 32'd68;
        end
        32'd63: begin
          reg_13 <= ({reg_5 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_13);
          state <= ({{reg_5 == 32'd0} & ({reg_5 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_13)} ? 32'd54 : state);
          state <= ({{reg_5 | {({reg_5 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_13) == 32'd0}} & {{reg_5 == 32'd0} & {({reg_5 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_13) == 32'd0}}} ? 32'd37 : ({{reg_5 == 32'd0} & ({reg_5 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_13)} ? 32'd54 : state));
          state <= ({{reg_5 | {({reg_5 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_13) == 32'd0}} & {reg_5 | ({reg_5 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_13)}} ? 32'd64 : ({{reg_5 | {({reg_5 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_13) == 32'd0}} & {{reg_5 == 32'd0} & {({reg_5 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_13) == 32'd0}}} ? 32'd37 : ({{reg_5 == 32'd0} & ({reg_5 == 32'd0} ? {$signed(reg_6) < $signed(32'd30)} : reg_13)} ? 32'd54 : state)));
        end
        32'd62: begin
          reg_4 <= {reg_4 + 32'd1};
          reg_5 <= {$signed({reg_4 + 32'd1}) < $signed(32'd30)};
          state <= ({$signed({reg_4 + 32'd1}) < $signed(32'd30)} ? 32'd48 : state);
          reg_6 <= ({{$signed({reg_4 + 32'd1}) < $signed(32'd30)} == 32'd0} ? {reg_6 + 32'd1} : reg_6);
          state <= ({{$signed({reg_4 + 32'd1}) < $signed(32'd30)} == 32'd0} ? 32'd63 : ({$signed({reg_4 + 32'd1}) < $signed(32'd30)} ? 32'd48 : state));
        end
        32'd61: begin
          state <= 32'd62;
          reg_93 <= ( ~ reg_93);
          reg_92 <= 32'd1;
          reg_90 <= reg_40;
          reg_88 <= {{{reg_38 + 32'd0} + {reg_4 * 32'd4}} / 32'd4};
        end
        32'd60: begin
          reg_38 <= {{reg_42 + reg_44} + 32'd0};
          state <= 32'd61;
        end
        32'd59: begin
          reg_42 <= {{reg_46 + reg_48} + 32'd0};
          state <= 32'd60;
        end
        32'd56: begin
          reg_8 <= 32'd0;
          state <= 32'd55;
          state <= (32'd0 ? 32'd65 : 32'd55);
        end
        32'd55: begin
          reg_6 <= 32'd0;
          state <= 32'd54;
          state <= (32'd0 ? 32'd98 : 32'd54);
        end
        32'd54: begin
          reg_54 <= 32'd120;
          reg_56 <= {reg_8 * 32'd120};
          reg_52 <= 32'd1086324736;
          reg_4 <= 32'd0;
          state <= 32'd90;
        end
        32'd48: begin
          reg_46 <= 32'd240;
          reg_48 <= {reg_8 * 32'd3600};
          reg_44 <= {reg_6 * 32'd120};
          reg_40 <= 32'd1088421888;
          state <= 32'd59;
        end
        32'd37: begin
          reg_8 <= {reg_8 + 32'd1};
          reg_11 <= {$signed({reg_8 + 32'd1}) < $signed(32'd1)};
          state <= ({$signed({reg_8 + 32'd1}) < $signed(32'd1)} ? 32'd55 : state);
          reg_68 <= ({{$signed({reg_8 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd0 : reg_68);
          reg_62 <= ({{$signed({reg_8 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd240 : reg_62);
          reg_60 <= ({{$signed({reg_8 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd120 : reg_60);
          reg_58 <= ({{$signed({reg_8 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd0 : reg_58);
          state <= ({{$signed({reg_8 + 32'd1}) < $signed(32'd1)} == 32'd0} ? 32'd94 : ({$signed({reg_8 + 32'd1}) < $signed(32'd1)} ? 32'd55 : state));
        end
        32'd20: begin
          reg_64 <= 32'd0;
          reg_66 <= 32'd0;
          state <= 32'd18;
          state <= (32'd0 ? 32'd66 : 32'd18);
        end
        32'd18: begin
          state <= 32'd109;
          reg_93 <= ( ~ reg_93);
          reg_92 <= 32'd0;
          reg_88 <= {{{reg_60 + 32'd0} + {reg_66 * 32'd4}} / 32'd4};
        end
        32'd7: begin
          state <= 32'd131;
          reg_93 <= ( ~ reg_93);
          reg_92 <= 32'd0;
          reg_88 <= 32'd10;
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
