(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2022 Yann Herklotz <yann@yannherklotz.com>
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

Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.Gible.
Require Import vericert.hls.GibleSeq.
Require Import vericert.hls.Predicate.
Require Import vericert.bourdoncle.Bourdoncle.

Definition elim_cond_s (fresh: predicate) (i: instr) :=
  match i with
  | RBexit p (RBcond c args n1 n2) =>
      (Pos.succ fresh,
       RBsetpred p c args fresh
       :: RBexit (combine_pred (Some (Plit (true, fresh))) p) (RBgoto n1)
       :: RBexit (combine_pred (Some (Plit (false, fresh))) p) (RBgoto n2)
       :: nil)
  | _ => (fresh, i :: nil)
  end.

(* Fixpoint elim_cond (fresh: predicate) (b: SeqBB.t) := *)
(*   match b with *)
(*   | RBexit p (RBcond c args n1 n2) :: b' => *)
(*       let (fresh', b'') := elim_cond fresh b' in *)
(*       (Pos.succ fresh', *)
(*           RBsetpred p c args fresh' *)
(*        :: RBexit (combine_pred (Some (Plit (true, fresh'))) p) (RBgoto n1) *)
(*        :: RBexit (combine_pred (Some (Plit (false, fresh'))) p) (RBgoto n1) *)
(*        :: b'') *)
(*   | i :: b' => *)
(*       let (fresh, b'') := elim_cond fresh b' in *)
(*       (fresh, i :: b'') *)
(*   | nil => (fresh, nil) *)
(*   end. *)

Definition elim_cond_fold (state: predicate * PTree.t SeqBB.t) (n: node) (b: SeqBB.t) :=
  let (p, ptree) := state in
  let (p', b') := replace_section elim_cond_s p b in
  (p', PTree.set n b' ptree).

Definition transf_function (f: function) : function :=
  mkfunction f.(fn_sig) f.(fn_params) f.(fn_stacksize)
             (snd (PTree.fold elim_cond_fold f.(fn_code) (1%positive, PTree.empty _)))
             f.(fn_entrypoint).

Definition transf_fundef (fd: fundef) : fundef :=
  transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.
