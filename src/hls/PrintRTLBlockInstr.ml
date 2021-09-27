open Printf
open Camlcoq
open Datatypes
open Maps
open AST
open RTLBlockInstr
open PrintAST

let reg pp r =
  fprintf pp "x%d" (P.to_int r)

let pred pp r =
  fprintf pp "p%d" (Nat.to_int r)

let rec regs pp = function
  | [] -> ()
  | [r] -> reg pp r
  | r1::rl -> fprintf pp "%a, %a" reg r1 regs rl

let ros pp = function
  | Coq_inl r -> reg pp r
  | Coq_inr s -> fprintf pp "\"%s\"" (extern_atom s)

let rec print_pred_op pp = function
  | Pvar p -> pred pp p
  | Pnot p -> fprintf pp "(~ %a)" print_pred_op p
  | Pand (p1, p2) -> fprintf pp "(%a & %a)" print_pred_op p1 print_pred_op p2
  | Por (p1, p2) -> fprintf pp "(%a | %a)" print_pred_op p1 print_pred_op p2

let print_pred_option pp = function
  | Some x -> fprintf pp "(%a)" print_pred_op x
  | None -> ()

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
  | RBsetpred (c, args, p) ->
    fprintf pp "%a = %a\n"
      pred p
      (PrintOp.print_condition reg) (c, args)

let rec print_bblock_exit pp i =
  fprintf pp "\t\t";
  match i with
  | RBcall(_, fn, args, res, _) ->
      fprintf pp "%a = %a(%a)\n"
        reg res ros fn regs args;
  | RBtailcall(_, fn, args) ->
      fprintf pp "tailcall %a(%a)\n"
        ros fn regs args
  | RBbuiltin(ef, args, res, _) ->
      fprintf pp "%a = %s(%a)\n"
        (print_builtin_res reg) res
        (name_of_external ef)
        (print_builtin_args reg) args
  | RBcond(cond, args, s1, s2) ->
      fprintf pp "if (%a) goto %d else goto %d\n"
        (PrintOp.print_condition reg) (cond, args)
        (P.to_int s1) (P.to_int s2)
  | RBjumptable(arg, tbl) ->
      let tbl = Array.of_list tbl in
      fprintf pp "jumptable (%a)\n" reg arg;
      for i = 0 to Array.length tbl - 1 do
        fprintf pp "\tcase %d: goto %d\n" i (P.to_int tbl.(i))
      done
  | RBreturn None ->
      fprintf pp "return\n"
  | RBreturn (Some arg) ->
      fprintf pp "return %a\n" reg arg
  | RBgoto n ->
     fprintf pp "goto %d\n" (P.to_int n)
  | RBpred_cf (p, c1, c2) ->
    fprintf pp "if %a then (%a) else (%a)\n" print_pred_op p print_bblock_exit c1 print_bblock_exit c2
