module main(start, reset, clk, finish, return_val);
  logic [31:0] reg_32 = 0;
  logic [31:0] reg_48 = 0;
  logic [31:0] reg_8 = 0;
  logic [31:0] reg_72 = 0;
  logic [31:0] reg_40 = 0;
  logic [31:0] reg_4 = 0;
  logic [31:0] reg_68 = 0;
  logic [31:0] reg_36 = 0;
  logic [31:0] reg_52 = 0;
  logic [31:0] reg_44 = 0;
  logic [31:0] reg_28 = 0;
  logic [31:0] reg_60 = 0;
  logic [31:0] reg_34 = 0;
  logic [31:0] reg_50 = 0;
  logic [31:0] reg_42 = 0;
  logic [31:0] reg_26 = 0;
  logic [31:0] reg_58 = 0;
  logic [31:0] reg_6 = 0;
  logic [31:0] reg_70 = 0;
  logic [31:0] reg_38 = 0;
  logic [31:0] reg_46 = 0;
  logic [31:0] reg_30 = 0;
  logic [31:0] reg_9 = 0;
  logic [31:0] reg_73 = 0;
  logic [31:0] reg_5 = 0;
  logic [31:0] reg_69 = 0;
  logic [31:0] reg_11 = 0;
  logic [31:0] reg_7 = 0;
  logic [31:0] reg_71 = 0;
  (* ram_style = "block" *)
  logic [31:0] stack [3999:0];
  logic [31:0] state = 0;
  output logic [31:0] return_val = 0;
  output logic [0:0] finish = 0;
  input [0:0] clk;
  input [0:0] reset;
  input [0:0] start;

  always @(negedge clk) begin
    if ({reg_73 != reg_69}) begin
      if (reg_72) begin
        stack[reg_68] <= reg_70;
      end else begin
        reg_71 <= stack[reg_68];
      end
      reg_69 <= reg_73;
    end else begin
    end
  end

  always @(posedge clk) begin
    if ({reset == 32'd1}) begin
      state <= 32'd57;
    end else begin
      case (state)
        32'd227: begin
          state <= 32'd113;
          reg_58 <= reg_71;
        end
        32'd179: begin
          reg_5 <= ({reg_11 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_5);
          state <= ({{reg_11 == 32'd0} & ({reg_11 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_5)} ? 32'd56 : state);
          state <= ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_5) == 32'd0}} & {{reg_11 == 32'd0} & {({reg_11 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_5) == 32'd0}}} ? 32'd34 : ({{reg_11 == 32'd0} & ({reg_11 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_5)} ? 32'd56 : state));
          state <= ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_5) == 32'd0}} & {reg_11 | ({reg_11 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_5)}} ? 32'd180 : ({{reg_11 | {({reg_11 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_5) == 32'd0}} & {{reg_11 == 32'd0} & {({reg_11 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_5) == 32'd0}}} ? 32'd34 : ({{reg_11 == 32'd0} & ({reg_11 == 32'd0} ? {$signed(reg_6) < $signed(32'd1)} : reg_5)} ? 32'd56 : state)));
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
          reg_11 <= {$signed(reg_4) < $signed(32'd1000)};
          state <= ({$signed(reg_4) < $signed(32'd1000)} ? 32'd55 : state);
          reg_6 <= ({{$signed(reg_4) < $signed(32'd1000)} == 32'd0} ? {reg_6 + 32'd1} : reg_6);
          state <= ({{$signed(reg_4) < $signed(32'd1000)} == 32'd0} ? 32'd170 : ({$signed(reg_4) < $signed(32'd1000)} ? 32'd55 : state));
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
          reg_4 <= {reg_4 + 32'd1};
          state <= 32'd160;
        end
        32'd158: begin
          state <= 32'd159;
          reg_73 <= ( ~ reg_73);
          reg_72 <= 32'd1;
          reg_70 <= reg_28;
          reg_68 <= {{{reg_26 + 32'd0} + {reg_4 * 32'd4}} / 32'd4};
        end
        32'd157: begin
          state <= 32'd158;
          reg_73 <= ( ~ reg_73);
          reg_72 <= 32'd1;
          reg_70 <= reg_36;
          reg_68 <= {{{reg_34 + 32'd0} + {reg_4 * 32'd4}} / 32'd4};
        end
        32'd156: begin
          state <= 32'd157;
          reg_73 <= ( ~ reg_73);
          reg_72 <= 32'd1;
          reg_70 <= reg_44;
          reg_68 <= {{{reg_42 + 32'd0} + {reg_4 * 32'd4}} / 32'd4};
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
          state <= 32'd150;
        end
        32'd148: begin
          state <= 32'd149;
        end
        32'd147: begin
          state <= 32'd148;
        end
        32'd146: begin
          reg_42 <= {{reg_48 + reg_50} + 32'd0};
          reg_34 <= {{reg_38 + reg_40} + 32'd0};
          reg_26 <= {{reg_30 + reg_32} + 32'd0};
          reg_28 <= reg_36;
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
          reg_40 <= reg_50;
          reg_32 <= reg_50;
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
        32'd135: begin
          reg_7 <= {$signed(reg_60) < $signed(32'd1000)};
          state <= ({$signed(reg_60) < $signed(32'd1000)} ? 32'd25 : state);
          reg_8 <= ({{$signed(reg_60) < $signed(32'd1000)} == 32'd0} ? 32'd0 : reg_8);
          finish <= ({{$signed(reg_60) < $signed(32'd1000)} == 32'd0} ? 32'd1 : finish);
          return_val <= ({{$signed(reg_60) < $signed(32'd1000)} == 32'd0} ? ({{$signed(reg_60) < $signed(32'd1000)} == 32'd0} ? 32'd0 : reg_8) : return_val);
          state <= ({{$signed(reg_60) < $signed(32'd1000)} == 32'd0} ? 32'd135 : ({$signed(reg_60) < $signed(32'd1000)} ? 32'd25 : state));
          state <= ({{{$signed(reg_60) < $signed(32'd1000)} == 32'd0} & {$signed(reg_60) < $signed(32'd1000)}} ? 32'd136 : ({{$signed(reg_60) < $signed(32'd1000)} == 32'd0} ? 32'd135 : ({$signed(reg_60) < $signed(32'd1000)} ? 32'd25 : state)));
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
          state <= 32'd129;
        end
        32'd127: begin
          state <= 32'd128;
        end
        32'd126: begin
          state <= 32'd127;
        end
        32'd123: begin
          reg_7 <= ({reg_9 == 32'd0} ? {$signed(reg_60) < $signed(32'd1000)} : reg_7);
          state <= ({{reg_9 == 32'd0} & ({reg_9 == 32'd0} ? {$signed(reg_60) < $signed(32'd1000)} : reg_7)} ? 32'd25 : state);
          state <= ({{reg_9 | {({reg_9 == 32'd0} ? {$signed(reg_60) < $signed(32'd1000)} : reg_7) == 32'd0}} & {{reg_9 == 32'd0} & {({reg_9 == 32'd0} ? {$signed(reg_60) < $signed(32'd1000)} : reg_7) == 32'd0}}} ? 32'd4 : ({{reg_9 == 32'd0} & ({reg_9 == 32'd0} ? {$signed(reg_60) < $signed(32'd1000)} : reg_7)} ? 32'd25 : state));
          state <= ({{reg_9 | {({reg_9 == 32'd0} ? {$signed(reg_60) < $signed(32'd1000)} : reg_7) == 32'd0}} & {reg_9 | ({reg_9 == 32'd0} ? {$signed(reg_60) < $signed(32'd1000)} : reg_7)}} ? 32'd124 : ({{reg_9 | {({reg_9 == 32'd0} ? {$signed(reg_60) < $signed(32'd1000)} : reg_7) == 32'd0}} & {{reg_9 == 32'd0} & {({reg_9 == 32'd0} ? {$signed(reg_60) < $signed(32'd1000)} : reg_7) == 32'd0}}} ? 32'd4 : ({{reg_9 == 32'd0} & ({reg_9 == 32'd0} ? {$signed(reg_60) < $signed(32'd1000)} : reg_7)} ? 32'd25 : state)));
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
          state <= 32'd116;
        end
        32'd114: begin
          state <= 32'd115;
        end
        32'd113: begin
          reg_9 <= {$signed(reg_58) >= $signed(32'd0)};
          state <= ({$signed(reg_58) >= $signed(32'd0)} ? 32'd23 : state);
          reg_60 <= ({{$signed(reg_58) >= $signed(32'd0)} == 32'd0} ? {reg_60 + 32'd1} : reg_60);
          state <= ({{$signed(reg_58) >= $signed(32'd0)} == 32'd0} ? 32'd114 : ({$signed(reg_58) >= $signed(32'd0)} ? 32'd23 : state));
        end
        32'd111: begin
          state <= 32'd25;
          state <= (32'd0 ? 32'd112 : 32'd25);
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
        32'd57: begin
          reg_6 <= 32'd0;
          state <= 32'd56;
          state <= (32'd0 ? 32'd125 : 32'd56);
        end
        32'd56: begin
          reg_4 <= 32'd0;
          state <= 32'd55;
          state <= (32'd0 ? 32'd100 : 32'd55);
        end
        32'd55: begin
          reg_48 <= 32'd0;
          reg_50 <= {reg_6 * 32'd4000};
          reg_46 <= 32'd1;
          reg_44 <= {32'd1 - reg_4};
          reg_38 <= 32'd8000;
          reg_36 <= {reg_4 + 32'd10};
          reg_30 <= 32'd12000;
          state <= 32'd137;
        end
        32'd34: begin
          reg_52 <= 32'd0;
          reg_60 <= 32'd0;
          state <= 32'd102;
        end
        32'd25: begin
          state <= 32'd227;
          reg_73 <= ( ~ reg_73);
          reg_72 <= 32'd0;
          reg_68 <= {{{reg_52 + 32'd0} + {reg_60 * 32'd4}} / 32'd4};
        end
        32'd23: begin
          reg_60 <= {reg_60 + 32'd1};
          state <= 32'd126;
        end
        32'd4: begin
          reg_8 <= 32'd0;
          finish <= 32'd1;
          return_val <= 32'd0;
          state <= 32'd4;
          state <= (32'd0 ? 32'd101 : 32'd4);
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
