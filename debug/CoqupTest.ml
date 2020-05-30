open Coqup

open Test
open Camlcoq
open FMapPositive

let test_function_transf () =
  print_endline "Testing transformation";
  print_endline "TL PROGRAM: ";
  PrintRTL.print_program stdout testinputprogram;
  print_endline "VERILOG PROGRAM: ";

  let v = match Veriloggen.transf_program testinputprogram with
  | Errors.OK v -> v
  | Errors.Error _ ->
     raise (Failure "Error") in
  PrintVerilog.print_program stdout v

let cvalue n = Value.natToValue (Nat.of_int 32) (Nat.of_int n)

let test_values () =
  print_endline "Testing values";
  let v1 = cvalue 138 in
  let v2 = cvalue 12 in
  let v3 = Value.natToValue (Nat.of_int 16) (Nat.of_int 21) in
  PrintVerilog.print_value stdout v1;
  print_newline();
  PrintVerilog.print_value stdout v2;
  print_newline();
  PrintVerilog.print_value stdout v3;
  print_newline();
  print_string "Addition: ";
  PrintVerilog.print_value stdout (Value.vplus v1 v2);
  print_newline();
  print_string "Wrong addition: ";
  PrintVerilog.print_value stdout (Value.vplus v1 v3);
  print_newline();
  print_string "Opt addition: ";
  match Value.vplus_opt v1 v2 with
  | Some x -> begin
      PrintVerilog.print_value stdout x;
      print_endline "";
      match Value.vplus_opt v1 v3 with
      | Some x -> PrintVerilog.print_value stdout x; print_newline()
      | None -> print_endline "Correctly failed in addition"
    end
  | None -> raise (Failure "Error")

let simulate_test () =
  print_endline "Simulation test";
  let v =
    match Veriloggen.transf_program testinputprogram with
    | Errors.OK v -> v
    | _ -> raise (Failure "HLS Error") in
  match Verilog.module_run (Nat.of_int 10) v with
  | Errors.OK lst -> PrintVerilog.print_result stdout (PositiveMap.elements lst)
  | _ -> raise (Failure "Simulation error")

let () = test_function_transf ()
