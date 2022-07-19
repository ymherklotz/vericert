open Printf
open Camlcoq
open Datatypes
open Maps
open AST
open Gible
open Predicate
open PrintAST

let reg pp r =
  fprintf pp "x%d" (P.to_int r)

let pred pp r =
  fprintf pp "p%d" (P.to_int r)

let rec regs pp = function
  | [] -> ()
  | [r] -> reg pp r
  | r1::rl -> fprintf pp "%a, %a" reg r1 regs rl

let ros pp = function
  | Coq_inl r -> reg pp r
  | Coq_inr s -> fprintf pp "\"%s\"" (extern_atom s)

let rec print_pred_op_gen f pp = function
  | Plit p -> if fst p then f pp (snd p) else fprintf pp "~%a" f (snd p)
  | Pand (p1, p2) -> fprintf pp "(%a ∧ %a)" (print_pred_op_gen f) p1 (print_pred_op_gen f) p2
  | Por (p1, p2) -> fprintf pp "(%a ∨ %a)" (print_pred_op_gen f) p1 (print_pred_op_gen f) p2
  | Ptrue -> fprintf pp "T"
  | Pfalse -> fprintf pp "⟂"

let print_pred_option_gen f pp = function
  | Some x -> fprintf pp "(%a)" (print_pred_op_gen f) x
  | None -> ()

let print_pred_option = print_pred_option_gen pred

let print_bblock_exit pp i =
  match i with
  | RBcall(_, fn, args, res, _) ->
      fprintf pp "%a = %a(%a)"
        reg res ros fn regs args;
  | RBtailcall(_, fn, args) ->
      fprintf pp "tailcall %a(%a)"
        ros fn regs args
  | RBbuiltin(ef, args, res, _) ->
      fprintf pp "%a = %s(%a)"
        (print_builtin_res reg) res
        (name_of_external ef)
        (print_builtin_args reg) args
  | RBcond(cond, args, s1, s2) ->
      fprintf pp "if (%a) goto %d else goto %d"
        (PrintOp.print_condition reg) (cond, args)
        (P.to_int s1) (P.to_int s2)
  | RBjumptable(arg, tbl) ->
      let tbl = Array.of_list tbl in
      fprintf pp "jumptable (%a)" reg arg;
      for i = 0 to Array.length tbl - 1 do
        fprintf pp "\tcase %d: goto %d" i (P.to_int tbl.(i))
      done
  | RBreturn None ->
      fprintf pp "return"
  | RBreturn (Some arg) ->
      fprintf pp "return %a" reg arg
  | RBgoto n ->
     fprintf pp "goto %d" (P.to_int n)

let print_bblock_body pp i =
  fprintf pp "\t\t";
  match i with
  | RBnop -> fprintf pp "nop\n"
  | RBop(p, op, ls, dst) ->
     fprintf pp "%a %a = %a\n"
       print_pred_option p reg dst (PrintOp.print_operation reg) (op, ls)
  | RBload(p, chunk, addr, args, dst) ->
     fprintf pp "%a %a = %s[%a]\n"
       print_pred_option p reg dst (name_of_chunk chunk)
       (PrintOp.print_addressing reg) (addr, args)
  | RBstore(p, chunk, addr, args, src) ->
     fprintf pp "%a %s[%a] = %a\n"
       print_pred_option p
       (name_of_chunk chunk)
       (PrintOp.print_addressing reg) (addr, args)
       reg src
  | RBsetpred (p', c, args, p) ->
    fprintf pp "%a %a = %a\n"
      print_pred_option p'
      pred p
      (PrintOp.print_condition reg) (c, args)
  | RBexit (p, cf) ->
    fprintf pp "%a %a\n" print_pred_option p print_bblock_exit cf
