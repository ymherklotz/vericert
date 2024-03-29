(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2020-2022 Yann Herklotz <yann@yannherklotz.com>
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
open Gible
open GibleSeq
open GibleSeq

(** Assuming that the nodes of the CFG [code] are numbered in reverse postorder (cf. pass
   [Renumber]), an edge from [n] to [s] is a normal edge if [s < n] and a back-edge otherwise. *)
let find_edge i n =
  let succ = RTL.successors_instr i in
  let filt = List.filter (fun s -> P.lt n s || P.lt s (P.pred n)) succ in
  ((match filt with [] -> [] | _ -> [n]), filt)

let find_edges c =
  PTree.fold (fun l n i ->
      let f = find_edge i n in
      (List.append (fst f) (fst l), List.append (snd f) (snd l))) c ([], [])

(* let prepend_instr i = function *)
(*   | {bb_body = bb; bb_exit = e} -> {bb_body = (i :: bb); bb_exit = e} *)

let prepend_instr i b = i :: b

let translate_inst = function
  | RTL.Inop _ -> Some RBnop
  | RTL.Iop (op, ls, dst, _) -> Some (RBop (None, op, ls, dst))
  | RTL.Iload (m, addr, ls, dst, _) -> Some (RBload (None, m, addr, ls, dst))
  | RTL.Istore (m, addr, ls, src, _) -> Some (RBstore (None, m, addr, ls, src))
  | _ -> None

let translate_cfi = function
  | RTL.Icall (s, r, ls, dst, n) -> Some (RBcall (s, r, ls, dst, n))
  | RTL.Itailcall (s, r, ls) -> Some (RBtailcall (s, r, ls))
  | RTL.Ibuiltin (e, ls, r, n) -> Some (RBbuiltin (e, ls, r, n))
  | RTL.Icond (c, ls, dst1, dst2) -> Some (RBcond (c, ls, dst1, dst2))
  | RTL.Ijumptable (r, ls) -> Some (RBjumptable (r, ls))
  | RTL.Ireturn r -> Some (RBreturn r)
  | _ -> None

let rec next_bblock_from_RTL is_start e (c : RTL.code) s i =
  let succ = List.map (fun i -> (i, PTree.get i c)) (RTL.successors_instr i) in
  let trans_inst = (translate_inst i, translate_cfi i) in
  match trans_inst, succ with
  | (None, Some i'), _ ->
    if List.exists (fun x -> x = s) (snd e) && not is_start then
      Errors.OK [RBexit (None, (RBgoto s))]
    else
      Errors.OK [RBnop; RBexit (None, i')]
  | (Some i', None), (s', Some i_n)::[] ->
    if List.exists (fun x -> x = s) (fst e) then
      Errors.OK [i'; RBexit (None, (RBgoto s'))]
    else if List.exists (fun x -> x = s) (snd e) && not is_start then
      Errors.OK [RBexit (None, (RBgoto s))]
    else begin
      match next_bblock_from_RTL false e c s' i_n with
      | Errors.OK bb ->
        Errors.OK (prepend_instr i' bb)
      | Errors.Error msg -> Errors.Error msg
    end
  | _, _ ->
    Errors.Error (Errors.msg (coqstring_of_camlstring "next_bblock_from_RTL went wrong."))

let rec traverseacc f l c =
  match l with
  | [] -> Errors.OK c
  | x::xs ->
    match f x c with
    | Errors.Error msg -> Errors.Error msg
    | Errors.OK x' ->
      match traverseacc f xs x' with
      | Errors.Error msg -> Errors.Error msg
      | Errors.OK xs' -> Errors.OK xs'

let rec translate_all edge c s res =
  let c_bb, translated = res in
  if List.exists (fun x -> P.eq x s) translated then Errors.OK (c_bb, translated) else
    (match PTree.get s c with
     | None -> Errors.Error (Errors.msg (coqstring_of_camlstring "Could not translate all."))
     | Some i ->
       match next_bblock_from_RTL true edge c s i with
       | Errors.Error msg -> Errors.Error msg
       | Errors.OK bb ->
         let succ = List.filter (fun x -> P.lt x s) (all_successors bb) in
         (match traverseacc (translate_all edge c) succ (c_bb, s :: translated) with
          | Errors.Error msg -> Errors.Error msg
          | Errors.OK (c', t') ->
            Errors.OK (PTree.set s bb c', t')))

(* Partition a function and transform it into RTLBlock. *)
let function_from_RTL f =
  let e = find_edges f.RTL.fn_code in
  match translate_all e f.RTL.fn_code f.RTL.fn_entrypoint (PTree.empty, []) with
  | Errors.Error msg -> Errors.Error msg
  | Errors.OK (c, _) ->
    Errors.OK { fn_sig = f.RTL.fn_sig;
                fn_stacksize = f.RTL.fn_stacksize;
                fn_params = f.RTL.fn_params;
                fn_entrypoint = f.RTL.fn_entrypoint;
                fn_code = c
              }

let partition = function_from_RTL
