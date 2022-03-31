(**open Camlcoq
open Datatypes
open Maps
open AST
open Abstr
open PrintAST
open Printf

let rec expr_to_list = function
  | Enil -> []
  | Econs (e, el) -> e :: expr_to_list el

let res pp = function
  | Reg r -> fprintf pp "r%d" (P.to_int r)
  | Pred r -> fprintf pp "p%d" (P.to_int r)
  | Mem -> fprintf pp "M"

let rec print_expression pp = function
  | Ebase r -> fprintf pp "%a'" res r
  | Eop (op, el) -> fprintf pp "(%a)" (PrintOp.print_operation print_expression) (op, expr_to_list el)
  | Eload (chunk, addr, el, e) ->
    fprintf pp "(%s[%a][%a])"
       (name_of_chunk chunk) print_expression e
       (PrintOp.print_addressing print_expression) (addr, expr_to_list el)
  | Estore (e, chunk, addr, el, m) ->
    fprintf pp "(%s[%a][%a] = %a)"
      (name_of_chunk chunk) print_expression m
      (PrintOp.print_addressing print_expression) (addr, expr_to_list el)
      print_expression e
  | Esetpred (c, el) ->
    fprintf pp "(%a)" (PrintOp.print_condition print_expression) (c, expr_to_list el)

let rec print_predicated pp = function
  | NE.Coq_singleton (p, e) ->
    fprintf pp "%a %a" PrintRTLBlockInstr.print_pred_option p print_expression e
  | NE.Coq_cons ((p, e), pr) ->
    fprintf pp "%a %a\n%a" PrintRTLBlockInstr.print_pred_option p print_expression e
      print_predicated pr
*)
