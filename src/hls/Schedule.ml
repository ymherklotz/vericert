(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2020 Yann Herklotz <yann@yannherklotz.com>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 *)

open Printf
open Clflags
open Camlcoq
open Datatypes
open Coqlib
open Maps
open AST
open Kildall
open Op
open RTLBlock
open HTL

let read_process command =
  let buffer_size = 2048 in
  let buffer = Buffer.create buffer_size in
  let string = Bytes.create buffer_size in
  let in_channel = Unix.open_process_in command in
  let chars_read = ref 1 in
  while !chars_read <> 0 do
    chars_read := input in_channel string 0 buffer_size;
    Buffer.add_substring buffer (Bytes.to_string string) 0 !chars_read
  done;
  ignore (Unix.close_process_in in_channel);
  Buffer.contents buffer

let add_dep i tree deps curr =
  match PTree.get curr tree with None -> deps | Some ip -> (ip, i) :: deps

let accumulate_deps dfg curr =
  let i, tree, vals = dfg in
  match curr with
  | RBnop -> (i + 1, tree, vals)
  | RBop (_, rs, dst) ->
      ( i + 1,
        PTree.set dst i tree,
        List.append (List.fold_left (add_dep i tree) [] rs) vals )
  | RBload (mem, addr, rs, dst) ->
      ( i + 1,
        PTree.set dst i tree,
        List.append (List.fold_left (add_dep i tree) [] rs) vals )
  | RBstore (mem, addr, rs, dst) -> (i + 1, tree, vals)

let assigned_vars vars = function
  | RBnop -> vars
  | RBop (_, _, dst) -> dst :: vars
  | RBload (_, _, _, dst) -> dst :: vars
  | RBstore (_, _, _, _) -> vars

(* All the nodes in the DFG have to come after the source of the basic block, and should terminate
   before the sink of the basic block.  After that, there should be constraints for data
   dependencies between nodes. *)
let gather_bb_constraints bb =
  let _, _, edges =
    List.fold_left accumulate_deps (0, PTree.empty, []) bb.bb_body
  in
  match bb.bb_exit with
  | None -> assert false
  | Some e -> (List.length bb.bb_body, edges, successors_instr e)

let gen_bb_name s i = sprintf "bb%d%s" (P.to_int i) s

let gen_bb_name_ssrc = gen_bb_name "ssrc"

let gen_bb_name_ssnk = gen_bb_name "ssnk"

let gen_var_name s c i = sprintf "v%d%s_%d" (P.to_int i) s c

let gen_var_name_b = gen_var_name "b"

let gen_var_name_e = gen_var_name "e"

let print_lt0 = sprintf "%s - %s <= 0;\n"

let print_bb_order i c = print_lt0 (gen_bb_name_ssnk i) (gen_bb_name_ssrc c)

let print_src_order i c =
  print_lt0 (gen_bb_name_ssrc i) (gen_var_name_b c i)
  ^ print_lt0 (gen_var_name_e c i) (gen_bb_name_ssnk i)
  ^ sprintf "%s - %s = 1;\n" (gen_var_name_e c i) (gen_var_name_b c i)

let print_src_type i c =
  sprintf "int %s;\n" (gen_var_name_e c i)
  ^ sprintf "int %s;\n" (gen_var_name_b c i)

let print_data_dep_order c (i, j) =
  print_lt0 (gen_var_name_e i c) (gen_var_name_b j c)

let rec gather_cfg_constraints (completed, (bvars, constraints, types)) c curr =
  if List.exists (fun x -> P.eq x curr) completed then
    (completed, (bvars, constraints, types))
  else
    match PTree.get curr c with
    | None -> assert false
    | Some (num_iters, edges, next) ->
        let constraints' =
          constraints
          ^ String.concat "" (List.map (print_bb_order curr) next)
          ^ String.concat ""
              (List.map (print_src_order curr)
                 (List.init num_iters (fun x -> x)))
          ^ String.concat "" (List.map (print_data_dep_order curr) edges)
        in
        let types' =
          types
          ^ String.concat ""
              (List.map (print_src_type curr)
                 (List.init num_iters (fun x -> x)))
          ^ sprintf "int %s;\n" (gen_bb_name_ssrc curr)
          ^ sprintf "int %s;\n" (gen_bb_name_ssnk curr)
        in
        let bvars' =
          List.append
            (List.map
               (fun x -> gen_var_name_b x curr)
               (List.init num_iters (fun x -> x)))
            bvars
        in
        let next' = List.filter (fun x -> P.lt x curr) next in
        List.fold_left
          (fun compl curr' -> gather_cfg_constraints compl c curr')
          (curr :: completed, (bvars', constraints', types'))
          next'

let rec intersperse s = function
  | [] -> []
  | [ a ] -> [ a ]
  | x :: xs -> x :: s :: intersperse s xs

let schedule entry (c : code) =
  let c' = PTree.map1 gather_bb_constraints c in
  let _, (vars, constraints, types) =
    gather_cfg_constraints ([], ([], "", "")) c' entry
  in
  let oc = open_out "lpsolve.txt" in
  fprintf oc "min: ";
  List.iter (fprintf oc "%s") (intersperse " + " vars);
  fprintf oc ";\n";
  fprintf oc "%s" constraints;
  fprintf oc "%s" types;
  close_out oc;
  let s = read_process "lp_solve lpsolve.txt" in
  printf "%s" s;
  c
