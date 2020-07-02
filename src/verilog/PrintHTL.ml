(* -*- mode: tuareg -*-
 * CoqUp: Verified high-level synthesis.
 * Copyright (C) 2019-2020 Yann Herklotz <yann@yannherklotz.com>
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

open Value
open Datatypes
open Camlcoq
open AST
open Clflags
open Printf
open Maps
open AST
open HTL
open PrintAST
open PrintVerilog
open CoqupClflags

let pstr pp = fprintf pp "%s"

let reg pp r =
  fprintf pp "x%d" (P.to_int r)

let rec regs pp = function
  | [] -> ()
  | [r] -> reg pp r
  | r1::rl -> fprintf pp "%a, %a" reg r1 regs rl

let print_instruction pp (pc, i) =
  fprintf pp "%5d:\t%s" pc (pprint_stmnt 0 i)

let print_module pp id f =
  fprintf pp "%s(%a) {\n" (extern_atom id) regs f.mod_params;
  let datapath =
    List.sort
      (fun (pc1, _) (pc2, _) -> compare pc2 pc1)
      (List.rev_map
        (fun (pc, i) -> (P.to_int pc, i))
        (PTree.elements f.mod_datapath)) in
  let controllogic =
    List.sort
      (fun (pc1, _) (pc2, _) -> compare pc2 pc1)
      (List.rev_map
        (fun (pc, i) -> (P.to_int pc, i))
        (PTree.elements f.mod_controllogic)) in
  fprintf pp "  datapath {\n";
  List.iter (print_instruction pp) datapath;
  fprintf pp "  }\n\n  controllogic {\n";
  List.iter (print_instruction pp) controllogic;
  fprintf pp "  }\n}\n\n"

let print_globdef pp (id, gd) =
  match gd with
  | Gfun(Internal f) -> print_module pp id f
  | _ -> ()

let print_program pp prog =
  List.iter (print_globdef pp) prog.prog_defs

let destination : string option ref = ref None

let print_if prog =
  match !destination with
  | None -> ()
  | Some f ->
    let oc = open_out f in
    print_program oc prog;
    close_out oc
