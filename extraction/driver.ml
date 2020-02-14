(* let parse_c_file sourcename ifile =
  (* Simplification options *)
  let simplifs =
    "b" (* blocks: mandatory *)
  ^ (if false then "s" else "")
  ^ (if false then "f" else "")
  ^ (if false then "p" else "")
  in
  (* Parsing and production of a simplified C AST *)
  let ast = Parse.preprocessed_file simplifs sourcename ifile in
  (* Conversion to Csyntax *)
  let csyntax = Timing.time "CompCert C generation" C2C.convertProgram ast in
  (* Save CompCert C AST if requested *)
  PrintCsyntax.print_if csyntax;
  csyntax
 *)
open Compcert.Allocation

let _ = print_endline "Hello world"
