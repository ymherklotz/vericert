(*|
..
   Vericert: Verified high-level synthesis.
   Copyright (C) 2021-2022 Yann Herklotz <yann@yannherklotz.com>

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.

.. coq:: none
|*)


Require Import Coq.Structures.Orders.
Require Import Coq.Sorting.Mergesort.

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

Definition if_conv_t : Type := list (node * node).

Parameter build_bourdoncle : function -> (bourdoncle * PMap.t N).

#[local] Open Scope positive.

(*|
=============
If-Conversion
=============

This conversion is a verified conversion from RTLBlock back to itself, which
performs if-conversion on basic blocks to make basic blocks larger.
|*)

Definition map_if_convert (p: option pred_op) (i: instr) :=
  match i with
  | RBop p' op args dst => RBop (combine_pred p p') op args dst
  | RBload p' chunk addr args dst =>
      RBload (combine_pred p p') chunk addr args dst
  | RBstore p' chunk addr args src =>
      RBstore (combine_pred p p') chunk addr args src
  | RBsetpred p' c l pred =>
      RBsetpred (combine_pred p p') c l pred
  | RBexit p' cf => RBexit (combine_pred p p') cf
  | _ => i
  end.

Definition wf_transition (pl: list predicate) (i: instr) :=
  match i with
  | RBsetpred _ _ _ p => negb (existsb (Pos.eqb p) pl)
  | _ => true
  end.

Definition wf_transition_block (p: pred_op) (b: SeqBB.t) :=
  forallb (wf_transition (predicate_use p)) b.

Definition wf_transition_block_opt (p: option pred_op) b :=
  Option.default true (Option.map (fun p' => wf_transition_block p' b) p).

Definition if_convert_block (next: node) (b_next: SeqBB.t) (i: instr) :=
  match i with
  | RBexit p (RBgoto next') =>
      if (next =? next') && wf_transition_block_opt p b_next
      then map (map_if_convert p) b_next
      else i::nil
  | _ => i::nil
  end.

Definition wrap_unit {A B} (f: A -> B) (_: unit) (a: A) := (tt, f a).

Definition predicated_store i :=
  match i with
  | RBstore _ _ _ _ _ => true
  | _ => false
  end.

Definition no_predicated_store bb :=
  match filter predicated_store bb with
  | nil => true
  | _ => false
  end.

Definition gather_set_predicate (l: list positive) (i: instr): list positive :=
  match i with
  | RBsetpred _ _ _ p => p::l
  | _ => l
  end.

Definition gather_all_set_predicate i :=
  fold_left gather_set_predicate i nil.

Definition gather_rbgoto (l: list positive) (i: instr): list positive :=
  match i with
  | RBexit _ (RBgoto p) => p::l
  | _ => l
  end.

Definition gather_all_rbgoto i :=
  fold_left gather_rbgoto i nil.

Definition distinct_lists (l1 l2: list positive): bool :=
  forallb (fun x => negb (existsb (Pos.eqb x) l2)) l1.

Definition decide_if_convert b_main b_next :=
  (length b_next <=? 50)%nat && no_predicated_store b_next
  && distinct_lists (gather_all_set_predicate b_main) (gather_all_set_predicate b_next)
  && distinct_lists (gather_all_rbgoto b_main) (gather_all_rbgoto b_next).

Definition if_convert (orig_c c: code) (main next: node) :=
  match orig_c ! main, orig_c ! next with
  | Some b_main, Some b_next =>
      if decide_if_convert b_main b_next then
        PTree.set main (snd (replace_section (wrap_unit (if_convert_block next b_next)) tt b_main)) c
      else c
  | _, _ => c
  end.

Definition get_unconditional_exit (bb: SeqBB.t) := nth_error bb (length bb - 1).

(* Definition if_convert_block (c: code) (p: predicate) (bb: SeqBB.t) : SeqBB.t := *)
(*   match get_unconditional_exit bb with *)
(*   | Some (RBexit None (RBcond cond args n1 n2)) => *)
(*     match PTree.get n1 c, PTree.get n2 c with *)
(*     | Some bb1, Some bb2 => *)
(*       let bb1' := List.map (map_if_convert (Plit (true, p))) bb1 in *)
(*       let bb2' := List.map (map_if_convert (Plit (false, p))) bb2 in *)
(*       List.concat (bb :: ((RBsetpred None cond args p) :: bb1') :: bb2' :: nil) *)
(*     | _, _ => bb *)
(*     end *)
(*   | _ => bb *)
(*   end. *)

Definition is_cond_cfi' (cfi: cf_instr) :=
  match cfi with
  | RBcond _ _ _ _ => true
  | _ => false
  end.

Definition is_cond_cfi (b: SeqBB.t) :=
  match get_unconditional_exit b with
  | Some (RBexit None (RBcond _ _ _ _)) => true
  | _ => false
  end.

Fixpoint any {A: Type} (f: A -> bool) (a: list A) :=
  match a with
  | x :: xs => f x || any f xs
  | nil => false
  end.

Fixpoint all {A: Type} (f: A -> bool) (a: list A) :=
  match a with
  | x :: xs => f x && all f xs
  | nil => true
  end.

Definition find_backedge (nb: node * SeqBB.t) :=
  let (n, b) := nb in
  let succs := all_successors b in
  filter (fun x => Pos.ltb n x) succs.

Definition find_all_backedges (c: code) : list node :=
  concat (map find_backedge (PTree.elements c)).

Definition has_backedge (entry: node) (be: list node) :=
  any (fun x => Pos.eqb entry x) be.

Fixpoint get_loops (b: bourdoncle): list node :=
  match b with
  | L h b' => h::(fold_right (fun a b => get_loops a ++ b) nil b')
  | I h => nil
  end.

Definition is_loop (b: list node) (n: node) :=
  any (Pos.eqb n) b.

Definition is_flat_cfi' (n: cf_instr) :=
  match n with
  | RBcond _ _ _ _ => false
  | RBjumptable _ _ => false
  | _ => true
  end.

Definition is_flat_cfi (n: SeqBB.t) :=
  (length (all_successors n) =? 1)%nat.

Definition is_flat (c: code) (succ: node) :=
  match c ! succ with
  | Some bblock => is_flat_cfi bblock
  | None => false
  end.

Definition find_blocks_with_cond ep (b: list node) (c: code) : list (node * SeqBB.t) :=
  let backedges := find_all_backedges c in
  filter (fun x => is_cond_cfi (snd x) &&
                     (negb (is_loop b (fst x)) || Pos.eqb (fst x) ep) &&
                     all (fun x' => is_flat c x')
                         (all_successors (snd x))
         ) (PTree.elements c).

Module TupOrder <: TotalLeBool.
  Definition t : Type := positive * positive.
  Definition leb (x y: t) := fst x <=? fst y.
  Infix "<=?" := leb (at level 70, no associativity).
  Theorem leb_total : forall a1 a2, (a1 <=? a2) = true \/ (a2 <=? a1) = true.
  Proof. unfold leb; intros; repeat rewrite Pos.leb_le; lia. Qed.
End TupOrder.

Module Import TupSort := Sort TupOrder.

Definition ifconv_list (headers: list node) (c: code) :=
  let all_succ := PTree.fold (fun l n i => (n, all_successors i) :: l) c nil in
  let filtered := filter (fun x => match x with (_, l) => (length l <=? 2)%nat end) all_succ in
  let expanded :=
    fold_left (fun l (e: node * list node) =>
                 let (e1, e2) := e in
                 map (fun x => (e1, x)) e2 ++ l
              ) filtered nil in
  let filtered2 := filter (fun x: node * node =>
                             let (x1, x2) := x in
                             negb (is_loop headers x2)
                          ) expanded in
  sort filtered2.

(* Definition if_convert_code (p: nat * code) (nb: node * SeqBB.t) := *)
(*   let nbb := if_convert_block (snd p) (Pos.of_nat (fst p)) (snd nb) in *)
(*   (S (fst p), PTree.set (fst nb) nbb (snd p)). *)

Definition if_convert_code (c: code) iflist :=
  fold_left (fun s n => if_convert c s (fst n) (snd n)) iflist c.

Definition transf_function (f: function) : function :=
  let (b, _) := build_bourdoncle f in
  let b' := get_loops b in
  let iflist := ifconv_list b' f.(fn_code) in
  mkfunction f.(fn_sig) f.(fn_params) f.(fn_stacksize)
             (if_convert_code f.(fn_code) iflist)
             f.(fn_entrypoint).

Section TRANSF_PROGRAM.

  Context {A B V DATA: Type}.
  Variable transf: option DATA -> A -> B.

  Definition transform_program_globdef' (data: PTree.t DATA) (idg: ident * globdef A V) : ident * globdef B V :=
    match idg with
    | (id, Gfun f) => (id, Gfun (transf (data!id) f))
    | (id, Gvar v) => (id, Gvar v)
    end.

  Definition transform_program_data (data: PTree.t DATA) (p: AST.program A V) : AST.program B V :=
    mkprogram
      (List.map (transform_program_globdef' data) p.(prog_defs))
      p.(prog_public)
          p.(prog_main).

End TRANSF_PROGRAM.

Definition transf_fundef (fd: fundef) : fundef :=
  transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.
