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

let print_pred_expression pp = function
  | PEbase p -> fprintf pp "%a'" PrintGible.pred p
  | PEsetpred (c, el) ->
    fprintf pp "(%a)" (PrintOp.print_condition print_expression) (c, expr_to_list el)

let print_exit_expression pp = function
  | EEbase -> fprintf pp "EXIT'"
  | EEexit cf ->
    fprintf pp "[%a]" PrintGible.print_bblock_exit cf

let rec rev_index = function
  | BinNums.Coq_xH -> Mem
  | BinNums.Coq_xO r -> Reg r

let print_pred_expr = PrintGible.print_pred_op_gen PrintGible.pred
let print_pred_pexpr = PrintGible.print_pred_op_gen print_pred_expression

let rec print_predicated pp = function
  | NE.Coq_singleton (p, e) ->
    fprintf pp "%a %a" print_pred_expr p print_expression e
  | NE.Coq_cons ((p, e), pr) ->
    fprintf pp "%a %a\n%a" print_pred_expr p print_expression e
      print_predicated pr

let rec print_predicated_exit pp = function
  | NE.Coq_singleton (p, e) ->
    fprintf pp "%a %a" print_pred_expr p print_exit_expression e
  | NE.Coq_cons ((p, e), pr) ->
    fprintf pp "%a %a\n%a" print_pred_expr p print_exit_expression e
      print_predicated_exit pr

let print_forest_regs pp f =
  fprintf pp "-------------------- Reg --------------------\n";
  List.iter
    (function (i, y) -> fprintf pp "-- %a --\n%a\n"
                          res (rev_index i)
                          print_predicated y)
    (PTree.elements f);
  flush stdout

let print_forest_preds pp f =
  fprintf pp "------------------- Preds -------------------\n";
  List.iter
    (function (i, y) -> fprintf pp "-- %a --\n%a\n"
                          PrintGible.pred i
                          print_pred_pexpr y)
    (PTree.elements f);
  flush stdout

let print_forest_exit pp f =
  fprintf pp "------------------- Exit  -------------------\n";
  print_predicated_exit pp f

let print_forest pp f =
  fprintf pp "#############################################\n";
  fprintf pp "%a\n%a\n%a\n"
    print_forest_regs f.forest_regs
    print_forest_preds f.forest_preds
    print_forest_exit f.forest_exit
