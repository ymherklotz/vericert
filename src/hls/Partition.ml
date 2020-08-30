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
  PTree.fold (fun l n i -> List.append (find_backedge i n) l) c []

let prepend_instr i = function
  | {bb_body = bb; bb_exit = e} -> {bb_body = (i :: bb); bb_exit = e}

let translate_inst = function
  | RTL.Inop _ -> Some RBnop
  | RTL.Iop (op, ls, dst, _) -> Some (RBop (op, ls, dst))
  | RTL.Iload (m, addr, ls, dst, _) -> Some (RBload (m, addr, ls, dst))
  | RTL.Istore (m, addr, ls, src, _) -> Some (RBstore (m, addr, ls, src))
  | _ -> None

let translate_cfi = function
  | RTL.Icall (s, r, ls, dst, n) -> Some (RBcall (s, r, ls, dst, n))
  | RTL.Itailcall (s, r, ls) -> Some (RBtailcall (s, r, ls))
  | RTL.Ibuiltin (e, ls, r, n) -> Some (RBbuiltin (e, ls, r, n))
  | RTL.Icond (c, ls, dst1, dst2) -> Some (RBcond (c, ls, dst1, dst2))
  | RTL.Ijumptable (r, ls) -> Some (RBjumptable (r, ls))
  | RTL.Ireturn r -> Some (RBreturn r)
  | _ -> None

let rec next_bblock_from_RTL (c : RTL.code) i =
  let succ = List.map (fun i -> PTree.get i c) (RTL.successors_instr i) in
  let trans_inst = (translate_inst i, translate_cfi i) in
  match trans_inst, succ with
  | (Some i', _), Some i::[] -> begin
      match next_bblock_from_RTL c i with
      | Errors.OK bb -> Errors.OK (prepend_instr i' bb)
      | Errors.Error msg -> Errors.Error msg
    end
  | (_, Some i'), _ ->
    Errors.OK {bb_body = []; bb_exit = Some i'}
  | _, _ -> Errors.Error (Errors.msg (coqstring_of_camlstring "next_bblock_from_RTL went wrong."))

let rec traverselist f l =
  match l with
  | [] -> Errors.OK []
  | x::xs ->
    match f x with
    | Errors.Error msg -> Errors.Error msg
    | Errors.OK x' ->
      match traverselist f xs with
      | Errors.Error msg -> Errors.Error msg
      | Errors.OK xs' ->
        Errors.OK (x'::xs')

let rec translate_all start c =
  match PTree.get start c with
  | None -> Errors.Error (Errors.msg (coqstring_of_camlstring "Could not translate all."))
  | Some i ->
    match next_bblock_from_RTL c i with
    | Errors.Error msg -> Errors.Error msg
    | Errors.OK {bb_body = bb; bb_exit = Some e} ->
      let succ = successors_instr e in
      match traverselist (fun s -> translate_all s c) succ with
      | Errors.OK l ->

(* Partition a function and transform it into RTLBlock. *)
let function_from_RTL f =
  let ba = find_backedges f.RTL.fn_code in
  { fn_sig = f.RTL.fn_entrypoint;
    fn_stacksize = f.RTL.fn_stacksize;
    fn_entrypoint = f.RTL.fn_entrypoint;
    fn_code = f.RTL.fn_code
  }
