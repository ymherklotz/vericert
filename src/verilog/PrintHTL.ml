(* -*- mode: tuareg -*-
 * Vericert: Verified high-level synthesis.
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
open VericertClflags

let pstr pp = fprintf pp "%s"

let concat = String.concat ""

let rec intersperse c = function
  | [] -> []
  | [x] -> [x]
  | x :: xs -> x :: c :: intersperse c xs

let register a = sprintf "reg_%d" (P.to_int a)
let registers a = String.concat "" (intersperse ", " (List.map register a))

let print_instruction pp (pc, i) =
  fprintf pp "%5d:\t%s" pc (pprint_stmnt 0 i)

let pprint_datapath_stmnt i = function
  | HTLVstmnt s -> pprint_stmnt i s
  | HTLfork (name, args) -> concat [
      "fork "; extern_atom name; "("; concat (intersperse ", " (List.map register args)); ");\n"
    ]
  | HTLjoin (name, dst) -> concat [
      register dst; " <= join "; extern_atom name; ";\n"
    ]

let print_datapath_instruction pp (pc, i) =
  fprintf pp "%5d:\t%s" pc (pprint_datapath_stmnt 0 i)

let ptree_to_list ptree =
  List.sort
    (fun (pc1, _) (pc2, _) -> compare pc2 pc1)
    (List.rev_map
      (fun (pc, i) -> (P.to_int pc, i))
      (PTree.elements ptree))

let print_module pp id f =
  fprintf pp "%s(%s) {\n" (extern_atom id) (registers f.mod_params);
  let datapath = ptree_to_list f.mod_datapath in
  let controllogic = ptree_to_list f.mod_controllogic in
  fprintf pp "datapath {\n";
  List.iter (print_datapath_instruction pp) datapath;
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
