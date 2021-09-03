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

let string_controlsignal = function
  | Coq_ctrl_finish -> "finish"
  | Coq_ctrl_return -> "return"
  | Coq_ctrl_start -> "start"
  | Coq_ctrl_reset -> "rst"
  | Coq_ctrl_clk -> "clk"
  | Coq_ctrl_param idx -> sprintf "param_%d" (Nat.to_int idx)

let print_externctrl pp ((local_reg : reg), ((target_mod: ident), (target_reg: controlsignal))) =
  fprintf pp "%s -> %s.%s\n" (register local_reg) (extern_atom target_mod) (string_controlsignal target_reg)

let ptree_to_list ptree =
  List.sort
    (fun (pc1, _) (pc2, _) -> compare pc2 pc1)
    (List.rev_map
      (fun (pc, i) -> (P.to_int pc, i))
      (PTree.elements ptree))

let print_ram pp opt_ram =
  match opt_ram with
  | Some ram ->
    fprintf pp "ram {\n";
    fprintf pp "   size: %d\n" (Nat.to_int ram.ram_size);
    fprintf pp "    mem: %s\n" (register ram.ram_mem);
    fprintf pp "     en: %s\n" (register ram.ram_en);
    fprintf pp "   u_en: %s\n" (register ram.ram_u_en);
    fprintf pp "   addr: %s\n" (register ram.ram_addr);
    fprintf pp "  wr_en: %s\n" (register ram.ram_wr_en);
    fprintf pp "   d_in: %s\n" (register ram.ram_d_in);
    fprintf pp "  d_out: %s\n" (register ram.ram_d_out);
    fprintf pp "}\n\n"
  | None -> ()

let print_module pp id f =
  fprintf pp "%s(%s) {\n" (extern_atom id) (registers f.mod_params);

  let externctrl = PTree.elements f.mod_externctrl in
  let datapath = ptree_to_list f.mod_datapath in
  let controllogic = ptree_to_list f.mod_controllogic in

  print_ram pp f.mod_ram;

  fprintf pp "externctrl {\n";
  List.iter (print_externctrl pp) externctrl;
  fprintf pp "  }\n\n";

  fprintf pp "datapath {\n";
  List.iter (print_instruction pp) datapath;
  fprintf pp "  }\n\n";

  fprintf pp "controllogic {\n";
  List.iter (print_instruction pp) controllogic;
  fprintf pp "  }\n}\n\n"

let print_globdef pp (id, gd) =
  match gd with
  | Gfun(Internal f) -> print_module pp id f
  | _ -> ()

let print_program pp prog =
  List.iter (print_globdef pp) prog.prog_defs

let destination : string option ref = ref None

let print_if passno prog =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out (f ^ "." ^ Z.to_string passno) in
      print_program oc prog;
      close_out oc
