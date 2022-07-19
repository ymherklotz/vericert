open Camlcoq
open Datatypes
open Maps
open AST
open Abstr
open PrintAST
open Printf
open Abstr

let rec expr_to_list = function
  | Enil -> []
  | Econs (e, el) -> e :: expr_to_list el

let res pp = function
  | Reg r -> fprintf pp "x%d" (P.to_int r)
  | Pred r -> fprintf pp "p%d" (P.to_int r)
  | Exit -> fprintf pp "EXIT"
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
  | Eexit cf ->
    fprintf pp "[%a]" PrintGible.print_bblock_exit cf

let rec rev_index = function
  | BinNums.Coq_xH -> Mem
  | BinNums.Coq_xO BinNums.Coq_xH -> Exit
  | BinNums.Coq_xI (BinNums.Coq_xI r) -> Pred r
  | BinNums.Coq_xO (BinNums.Coq_xO r) -> Reg r

let print_pred_expr = PrintGible.print_pred_op_gen print_expression

let rec print_predicated pp = function
  | NE.Coq_singleton (p, e) ->
    fprintf pp "%a %a" print_pred_expr p print_expression e
  | NE.Coq_cons ((p, e), pr) ->
    fprintf pp "%a %a\n%a" print_pred_expr p print_expression e
      print_predicated pr

let print_forest pp f =
  fprintf pp "########################################\n";
  List.iter
    (function (i, y) -> fprintf pp "-- %a --\n%a\n"
                          res (rev_index i)
                          print_predicated y)
    (PTree.elements f);
  flush stdout
