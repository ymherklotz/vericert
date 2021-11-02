(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2020-2021 Yann Herklotz <yann@yannherklotz.com>
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

Require Import compcert.backend.Registers.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Floats.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require compcert.verilog.Op.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.RTLBlock.
Require Import vericert.hls.RTLPar.
Require Import vericert.hls.RTLBlockInstr.
Require Import vericert.hls.Predicate.
Require Import vericert.hls.Abstr.

#[local] Open Scope positive.
#[local] Open Scope forest.
#[local] Open Scope pred_op.

(*|
Update functions.
|*)

Fixpoint list_translation (l : list reg) (f : forest) {struct l} : list pred_expr :=
  match l with
  | nil => nil
  | i :: l => (f # (Reg i)) :: (list_translation l f)
  end.

Fixpoint replicate {A} (n: nat) (l: A) :=
  match n with
  | O => nil
  | S n => l :: replicate n l
  end.

Definition merge''' x y :=
  match x, y with
  | Some p1, Some p2 => Some (Pand p1 p2)
  | Some p, None | None, Some p => Some p
  | None, None => None
  end.

Definition merge'' x :=
  match x with
  | ((a, e), (b, el)) => (merge''' a b, Econs e el)
  end.

Definition predicated_prod {A B: Type} (p1: predicated A) (p2: predicated B) :=
  NE.map (fun x => match x with ((a, b), (c, d)) => (Pand a c, (b, d)) end)
         (NE.non_empty_prod p1 p2).

Definition predicated_map {A B: Type} (f: A -> B) (p: predicated A): predicated B :=
  NE.map (fun x => (fst x, f (snd x))) p.

(*map (fun x => (fst x, Econs (snd x) Enil)) pel*)
Definition merge' (pel: pred_expr) (tpel: predicated expression_list) :=
  predicated_map (uncurry Econs) (predicated_prod pel tpel).

Fixpoint merge (pel: list pred_expr): predicated expression_list :=
  match pel with
  | nil => NE.singleton (T, Enil)
  | a :: b => merge' a (merge b)
  end.

Definition map_pred_op {A B} (pf: option pred_op * (A -> B)) (pa: option pred_op * A): option pred_op * B :=
  match pa, pf with
  | (p, a), (p', f) => (merge''' p p', f a)
  end.

Definition map_predicated {A B} (pf: predicated (A -> B)) (pa: predicated A): predicated B :=
  predicated_map (fun x => (fst x) (snd x)) (predicated_prod pf pa).

Definition predicated_apply1 {A B} (pf: predicated (A -> B)) (pa: A): predicated B :=
  NE.map (fun x => (fst x, (snd x) pa)) pf.

Definition predicated_apply2 {A B C} (pf: predicated (A -> B -> C)) (pa: A) (pb: B): predicated C :=
  NE.map (fun x => (fst x, (snd x) pa pb)) pf.

Definition predicated_apply3 {A B C D} (pf: predicated (A -> B -> C -> D)) (pa: A) (pb: B) (pc: C): predicated D :=
  NE.map (fun x => (fst x, (snd x) pa pb pc)) pf.

(*Compute merge (((Some (Pvar 2), Ebase (Reg 4))::nil)::((Some (Pvar 3), Ebase (Reg 3))::(Some (Pvar 1), Ebase (Reg 3))::nil)::nil).*)

Definition predicated_from_opt {A: Type} (p: option pred_op) (a: A) :=
  match p with
  | Some p' => NE.singleton (p', a)
  | None => NE.singleton (T, a)
  end.

Definition update (f : forest) (i : instr) : forest :=
  match i with
  | RBnop => f
  | RBop p op rl r =>
    f # (Reg r) <-
    (map_predicated (predicated_from_opt p (Eop op)) (merge (list_translation rl f)))
  | RBload p chunk addr rl r =>
    f # (Reg r) <-
    (map_predicated
     (map_predicated (predicated_from_opt p (Eload chunk addr)) (merge (list_translation rl f)))
     (f # Mem))
  | RBstore p chunk addr rl r =>
    f # Mem <-
    (map_predicated
     (map_predicated
      (predicated_apply2 (map_predicated (predicated_from_opt p Estore) (f # (Reg r))) chunk addr)
      (merge (list_translation rl f))) (f # Mem))
  | RBsetpred p' c addr p => f
  end.

(*|
Implementing which are necessary to show the correctness of the translation validation by showing
that there aren't any more effects in the resultant RTLPar code than in the RTLBlock code.

Get a sequence from the basic block.
|*)

Fixpoint abstract_sequence (f : forest) (b : list instr) : forest :=
  match b with
  | nil => f
  | i :: l => abstract_sequence (update f i) l
  end.

(*|
Check equivalence of control flow instructions.  As none of the basic blocks should have been moved,
none of the labels should be different, meaning the control-flow instructions should match exactly.
|*)

Definition check_control_flow_instr (c1 c2: cf_instr) : bool :=
  if cf_instr_eq c1 c2 then true else false.

(*|
We define the top-level oracle that will check if two basic blocks are equivalent after a scheduling
transformation.
|*)

Definition empty_trees (bb: RTLBlock.bb) (bbt: RTLPar.bb) : bool :=
  match bb with
  | nil =>
    match bbt with
    | nil => true
    | _ => false
    end
  | _ => true
  end.

Definition schedule_oracle (bb: RTLBlock.bblock) (bbt: RTLPar.bblock) : bool :=
  check (abstract_sequence empty (bb_body bb))
        (abstract_sequence empty (concat (concat (bb_body bbt)))) &&
  check_control_flow_instr (bb_exit bb) (bb_exit bbt) &&
  empty_trees (bb_body bb) (bb_body bbt).

Definition check_scheduled_trees := beq2 schedule_oracle.

Ltac solve_scheduled_trees_correct :=
  intros; unfold check_scheduled_trees in *;
  match goal with
  | [ H: context[beq2 _ _ _], x: positive |- _ ] =>
    rewrite beq2_correct in H; specialize (H x)
  end; repeat destruct_match; crush.

Lemma check_scheduled_trees_correct:
  forall f1 f2 x y1,
    check_scheduled_trees f1 f2 = true ->
    PTree.get x f1 = Some y1 ->
    exists y2, PTree.get x f2 = Some y2 /\ schedule_oracle y1 y2 = true.
Proof. solve_scheduled_trees_correct; eexists; crush. Qed.

Lemma check_scheduled_trees_correct2:
  forall f1 f2 x,
    check_scheduled_trees f1 f2 = true ->
    PTree.get x f1 = None ->
    PTree.get x f2 = None.
Proof. solve_scheduled_trees_correct. Qed.

(*|
Top-level functions
===================
|*)

Parameter schedule : RTLBlock.function -> RTLPar.function.

Definition transl_function (f: RTLBlock.function) : Errors.res RTLPar.function :=
  let tfcode := fn_code (schedule f) in
  if check_scheduled_trees f.(fn_code) tfcode then
    Errors.OK (mkfunction f.(fn_sig)
                          f.(fn_params)
                          f.(fn_stacksize)
                          tfcode
                          f.(fn_entrypoint))
  else
    Errors.Error (Errors.msg "RTLPargen: Could not prove the blocks equivalent.").

Definition transl_fundef := transf_partial_fundef transl_function.

Definition transl_program (p : RTLBlock.program) : Errors.res RTLPar.program :=
  transform_partial_program transl_fundef p.
