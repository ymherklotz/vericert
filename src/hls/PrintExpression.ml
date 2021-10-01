(*open Printf
open Camlcoq
open Datatypes
open Maps
open PrintAST
open RTLPargen

let reg pp r =
  fprintf pp "x%d" (P.to_int r)

let pred pp r =
  fprintf pp "p%d" (P.to_int r)

let print_resource pp = function
  | Reg r -> reg pp r
  | Pred r -> pred pp r
  | Mem -> fprintf pp "M"

let rec to_expr_list = function
  | Enil -> []
  | Econs (e, elist) -> e :: to_expr_list elist

let rec print_expression pp = function
  | Ebase r -> print_resource pp r
  | Eop (op, elist, e) ->
    PrintOp.print_operation print_expression pp (op, to_expr_list elist);
    Printf.printf "; ";
    print_expression pp e
  | Eload (chunk, addr, elist, e) ->
    fprintf pp "%s[%a]; " (name_of_chunk chunk) (PrintOp.print_addressing print_expression) (addr, to_expr_list elist);
    print_expression pp e
  | Estore (e, chunk, addr, elist, e') ->
    fprintf pp "%s[%a] = %a; " (name_of_chunk chunk)
      (PrintOp.print_addressing print_expression) (addr, to_expr_list elist)
      print_expression e;
    print_expression pp e
  | Esetpred (p, cond, elist, e) ->
    fprintf pp "%a = %a; " pred p (PrintOp.print_condition print_expression) (cond, to_expr_list elist);
    print_expression pp e
*)
