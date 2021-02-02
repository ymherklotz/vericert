open Printf
open Camlcoq
open Datatypes
open Maps
open AST
open RTLBlockInstr
open PrintAST

let reg pp r =
  fprintf pp "x%d" (P.to_int r)

let rec regs pp = function
  | [] -> ()
  | [r] -> reg pp r
  | r1::rl -> fprintf pp "%a, %a" reg r1 regs rl

let ros pp = function
  | Coq_inl r -> reg pp r
  | Coq_inr s -> fprintf pp "\"%s\"" (extern_atom s)

let print_bblock_body pp i =
  fprintf pp "\t\t";
  match i with
  | RBnop -> fprintf pp "nop\n"
  | RBop(_, op, ls, dst) ->
     fprintf pp "%a = %a\n"
       reg dst (PrintOp.print_operation reg) (op, ls)
  | RBload(_, chunk, addr, args, dst) ->
     fprintf pp "%a = %s[%a]\n"
       reg dst (name_of_chunk chunk)
       (PrintOp.print_addressing reg) (addr, args)
  | RBstore(_, chunk, addr, args, src) ->
     fprintf pp "%s[%a] = %a\n"
       (name_of_chunk chunk)
       (PrintOp.print_addressing reg) (addr, args)
       reg src

let print_bblock_exit pp i =
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
