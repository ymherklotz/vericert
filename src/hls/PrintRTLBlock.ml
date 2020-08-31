(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Pretty-printers for RTL code *)

open Printf
open Camlcoq
open Datatypes
open Maps
open AST
open RTLBlock
open PrintAST

(* Printing of RTL code *)

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
  | RBop(op, ls, dst) ->
     fprintf pp "%a = %a\n"
       reg dst (PrintOp.print_operation reg) (op, ls)
  | RBload(chunk, addr, args, dst) ->
     fprintf pp "%a = %s[%a]\n"
       reg dst (name_of_chunk chunk)
       (PrintOp.print_addressing reg) (addr, args)
  | RBstore(chunk, addr, args, src) ->
     fprintf pp "%s[%a] = %a\n"
       (name_of_chunk chunk)
       (PrintOp.print_addressing reg) (addr, args)
       reg src

let print_bblock_exit pp i =
  fprintf pp "\t\t";
  match i with
  | Some(RBcall(_, fn, args, res, _)) ->
      fprintf pp "%a = %a(%a)\n"
        reg res ros fn regs args;
  | Some(RBtailcall(_, fn, args)) ->
      fprintf pp "tailcall %a(%a)\n"
        ros fn regs args
  | Some(RBbuiltin(ef, args, res, _)) ->
      fprintf pp "%a = %s(%a)\n"
        (print_builtin_res reg) res
        (name_of_external ef)
        (print_builtin_args reg) args
  | Some(RBcond(cond, args, s1, s2)) ->
      fprintf pp "if (%a) goto %d else goto %d\n"
        (PrintOp.print_condition reg) (cond, args)
        (P.to_int s1) (P.to_int s2)
  | Some(RBjumptable(arg, tbl)) ->
      let tbl = Array.of_list tbl in
      fprintf pp "jumptable (%a)\n" reg arg;
      for i = 0 to Array.length tbl - 1 do
        fprintf pp "\tcase %d: goto %d\n" i (P.to_int tbl.(i))
      done
  | Some(RBreturn None) ->
      fprintf pp "return\n"
  | Some(RBreturn (Some arg)) ->
      fprintf pp "return %a\n" reg arg
  | Some(RBgoto n) ->
     fprintf pp "goto %d\n" (P.to_int n)
  | None -> fprintf pp "\n"

let print_bblock pp (pc, i) =
  fprintf pp "%5d:{\n" pc;
  List.iter (print_bblock_body pp) i.bb_body;
  print_bblock_exit pp i.bb_exit;
  fprintf pp "\t}\n\n"

let print_function pp id f =
  fprintf pp "%s(%a) {\n" (extern_atom id) regs f.fn_params;
  let instrs =
    List.sort
      (fun (pc1, _) (pc2, _) -> compare pc2 pc1)
      (List.rev_map
        (fun (pc, i) -> (P.to_int pc, i))
        (PTree.elements f.fn_code)) in
  List.iter (print_bblock pp) instrs;
  fprintf pp "}\n\n"

let print_globdef pp (id, gd) =
  match gd with
  | Gfun(Internal f) -> print_function pp id f
  | _ -> ()

let print_program pp (prog: program) =
  List.iter (print_globdef pp) prog.prog_defs

let destination : string option ref = ref None

let print_if prog =
  match !destination with
  | None -> ()
  | Some f ->
     let oc = open_out f in
     print_program oc prog;
     close_out oc
