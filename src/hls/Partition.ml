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

(* Assuming that the nodes of the CFG [code] are numbered in reverse postorder (cf. pass
   [Renumber]), an edge from [n] to [s] is a normal edge if [s < n] and a back-edge otherwise. *)
let find_backedge i n =
  let succ = RTL.successors_instr i in
  List.filter (fun s -> P.lt n s) succ

let find_backedges c =

let prepend_instr i = function
  | {bb_body = bb; bb_exit = e} -> {bb_body = (i :: bb); bb_exit = e}

let rec bblock_from_RTL (c : RTL.code) i =
  let succ = List.map (fun i -> PTree.get i c) (RTL.successors_instr i) in
  match i, succ with
  | RTL.Inop _, Some i::[] -> begin
      match bblock_from_RTL c i with
      | Errors.OK bb -> Errors.OK (prepend_instr RBnop bb)
      | Errors.Error msg -> Errors.Error msg
    end
  | RTL.Iop (op, rs, dst, _), Some i::[] -> begin
      match bblock_from_RTL c i with
      | Errors.OK bb
    end

(* Partition a function and transform it into RTLBlock. *)
let function_from_RTL f =
  { fn_sig = f.RTL.fn_entrypoint;
    fn_stacksize = f.RTL.fn_stacksize;
    fn_entrypoint = f.RTL.fn_entrypoint;
    fn_code = f.RTL.fn_code
  }
