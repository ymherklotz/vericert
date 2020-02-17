Require CoqUp.Verilog.VerilogAST.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Cd "src/Extraction".
Separate Extraction
         VerilogAST.nat_to_value VerilogAST.value_to_nat VerilogAST.verilog VerilogAST.verilog_example.
