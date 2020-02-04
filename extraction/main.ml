open Verilog
open Datatypes

let rec nat_to_int = function
  | O -> 0
  | S n -> 1 + nat_to_int n

let () =
  print_endline ("Result: " ^  (Verilog.value_to_nat (Verilog.VBool Coq_true) |> nat_to_int))
