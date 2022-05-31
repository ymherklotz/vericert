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

Local Open Scope error_monad_scope.

Definition not_seen_sons (code:code) (pc : node) (seen: PTree.t unit) : (list positive) * PTree.t unit := 
  match code ! pc with 
    | None => (nil, seen)
    | Some i => 
      List.fold_left (fun (ns:(list node) * PTree.t unit) j =>
        let (new,seen) := ns in
          match PTree.get j seen with
            | None => (j::new, PTree.set j tt seen)
            | Some _ => ns
          end) 
        (all_successors i)
        (nil, seen)
  end.

Definition remove_dead (i:option SeqBB.t) (b:option unit) : option SeqBB.t :=
  match b with
    | Some _ => i
    | None => None
  end.

Fixpoint acc_succ (c:code) (workl: list node)
         (acc: res (PTree.t unit * (list positive) * (list positive)))
  : res ((list positive) * code) :=
  do acc <- acc;
    let '(seen_set,seen_list,stack) := acc in 
      match stack with 
        | nil => OK (seen_list, PTree.combine remove_dead c seen_set)
        | x::q => 
          match workl with
            | nil => Error (msg "workl too small")
            | pc::m => 
              let seen_set' := PTree.set x tt seen_set in
                let (new,seen_set) := not_seen_sons c x seen_set' in
                  acc_succ c m (OK (seen_set,x::seen_list,new++q))
          end
      end.

Definition dfs (tf: function) : res (list node * code) :=
  do (res, code') <-
    (acc_succ 
      (fn_code tf)
      (map (@fst node SeqBB.t) (PTree.elements (fn_code tf)))
      (OK (PTree.empty _,nil,(fn_entrypoint tf)::nil))) ;
    OK (rev_append res nil, code').

Definition transf_function (f: function) : res function :=
  do (seen,code) <- dfs f ;
  OK (mkfunction f.(fn_sig) f.(fn_params) f.(fn_stacksize)
             code
             f.(fn_entrypoint)).

Definition transf_fundef (fd: fundef) : res fundef :=
  transf_partial_fundef transf_function fd.

Definition transf_program (p: program) : res program :=
  transform_partial_program transf_fundef p.
