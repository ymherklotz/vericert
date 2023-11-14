(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2023 Yann Herklotz <yann@yannherklotz.com>
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

Require Import Coq.FSets.FMapPositive.
Require Import Coq.micromega.Lia.

Require compcert.common.Events.
Require compcert.common.Globalenvs.
Require compcert.common.Smallstep.
Require compcert.common.Values.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.ValueInt.
Require Import vericert.hls.AssocMap.
Require Import vericert.hls.Array.
Require Import vericert.hls.Verilog.
Require Import vericert.hls.DHTL.

Require Import vericert.common.Errormonad.
Import Errors.
Import ErrorMonad.
Import ErrorMonadExtra.
Import MonadNotation.

#[local] Open Scope monad_scope.

Definition error {A} m := @Errors.Error A (Errors.msg m).

Definition pred := positive.

Inductive lhs : Type :=
| LhsReg : reg -> lhs
| LhsPred : pred -> lhs
.

Definition lhs_eqd (r1 r2: lhs): {r1 = r2} + {r1 <> r2}.
  pose proof peq.
  decide equality.
Defined.

Module R_indexed.
  Definition t := lhs.
  Definition index (rs: t) : positive :=
    match rs with
    | LhsReg r => xO r
    | LhsPred p => xI p
    end.

  Lemma index_inj:  forall (x y: t), index x = index y -> x = y.
  Proof. destruct x; destruct y; crush. Qed.

  Definition eq := lhs_eqd.
End R_indexed.

Module RTree := ITree(R_indexed).

Inductive flat_expr : Type :=
| FVlit : value -> flat_expr
| FVvar : reg -> flat_expr
| FVbinop : Verilog.binop -> flat_expr -> flat_expr -> flat_expr
| FVunop : Verilog.unop -> flat_expr -> flat_expr
| FVternary : flat_expr -> flat_expr -> flat_expr -> flat_expr
.

Inductive flat_stmnt : Type :=
| FVblock : reg -> flat_expr -> flat_stmnt
| FVnonblock : reg -> flat_expr -> flat_stmnt
.

Fixpoint flatten_expr (e: Verilog.expr) : Errors.res flat_expr :=
  match e with
  | Verilog.Vlit v => ret (FVlit v)
  | Verilog.Vvar r => ret (FVvar r)
  | Verilog.Vunop u e => 
    do fe <- flatten_expr e;
    ret (FVunop u fe)
  | Verilog.Vbinop u e1 e2 => 
    do fe1 <- flatten_expr e1;
    do fe2 <- flatten_expr e2;
    ret (FVbinop u fe1 fe2)
  | Verilog.Vternary e1 e2 e3 => 
    do fe1 <- flatten_expr e1;
    do fe2 <- flatten_expr e2;
    do fe3 <- flatten_expr e3;
    ret (FVternary fe1 fe2 fe3)
  | Verilog.Vrange _ _ _ => error "ClockRegisters: Could not translate Vrange"
  | Verilog.Vvari _ _ => error "ClockRegisters: Could not translate Vvari"
  | Verilog.Vinputvar _ => error "ClockRegisters: Could not translate Vinputvar"
  end.

Fixpoint flatten_seq_block (s: Verilog.stmnt) : Errors.res (list flat_stmnt) := 
  match s with
  | Verilog.Vskip => ret nil
  | Verilog.Vseq s1 s2 =>
    do s1' <- flatten_seq_block s1;
    do s2' <- flatten_seq_block s2;
    ret (s1' ++ s2')
  | Verilog.Vblock (Verilog.Vvar r) e => 
    do fe <- flatten_expr e;
    ret (FVblock r fe :: nil)
  (* | Verilog.Vblock (Verilog.Vrange r (Verilog.Vlit i1) (Verilog.Vlit i2)) e =>  *)
  (*   if Pos.eqb preg r && Int.eq i1 i2 then *)
  (*     match Int.unsigned i1, flatten_expr e with  *)
  (*     | Zpos p, Some fe => Some (FVblock p fe :: nil) *)
  (*     | _, _ => None *)
  (*     end *)
  (*   else None *)
  | Verilog.Vnonblock (Verilog.Vvar r) e => 
    do fe <- flatten_expr e;
    ret (FVnonblock r fe :: nil)
  (* | Verilog.Vnonblock (Verilog.Vrange r (Verilog.Vlit i1) (Verilog.Vlit i2)) e =>  *)
  (*   if Pos.eqb preg r && Int.eq i1 i2 then *)
  (*     match Int.unsigned i1, flatten_expr e with  *)
  (*     | Zpos p, Some fe => Some (FVnonblock p fe :: nil) *)
  (*     | _, _ => None *)
  (*     end *)
  (*   else None *)
  | _ => error "ClockRegisters: Could not translate seq_block"
  end.

Fixpoint expand_expr (f: flat_expr): Verilog.expr :=
  match f with
  | FVlit l => Verilog.Vlit l
  | FVvar r => Verilog.Vvar r
  | FVbinop b e1 e2 => Verilog.Vbinop b (expand_expr e1) (expand_expr e2)
  | FVunop b e => Verilog.Vunop b (expand_expr e)
  | FVternary e1 e2 e3 => Verilog.Vternary (expand_expr e1) (expand_expr e2) (expand_expr e3)
  end.

Definition expand_assignment (f: flat_stmnt): Verilog.stmnt := 
  match f with
  | FVblock r e => Verilog.Vblock (Verilog.Vvar r) (expand_expr e)
  | FVnonblock r e => Verilog.Vnonblock (Verilog.Vvar r) (expand_expr e)
  end.

Definition fold_seq_block (s: list flat_stmnt): Verilog.stmnt :=
  fold_left (fun a b => Verilog.Vseq a (expand_assignment b)) s Verilog.Vskip.

Fixpoint clock_flat_expr (t: PTree.t flat_expr) (f: flat_expr): flat_expr :=
  match f with
  | FVvar r => 
    match PTree.get r t with
    | Some e => e
    | None => FVvar r
    end
  | FVunop b e => FVunop b (clock_flat_expr t e)
  | FVbinop b e1 e2 => 
    FVbinop b (clock_flat_expr t e1) (clock_flat_expr t e2)
  | FVternary e1 e2 e3 => 
    FVternary (clock_flat_expr t e1) (clock_flat_expr t e2) (clock_flat_expr t e3)
  | _ => f
  end.

Fixpoint clock_expr (t: PTree.t expr) (f: expr): res expr :=
  match f with
  | Vvar r => 
    match PTree.get r t with
    | Some e => OK e
    | None => OK (Vvar r)
    end
  | Vunop b e => do e' <- (clock_expr t e); OK (Vunop b e')
  | Vbinop b e1 e2 => 
    do e1' <- (clock_expr t e1);
    do e2' <- (clock_expr t e2);
    OK (Vbinop b e1' e2')
  | Vternary e1 e2 e3 =>
    do e1' <- (clock_expr t e1);
    do e2' <- (clock_expr t e2);
    do e3' <- (clock_expr t e3);
    OK (Vternary e1' e2' e3')
  | Vvari r e => do e' <- (clock_expr t e); OK (Vvari r e')
  | Vrange r e1 e2 => Error (msg "ClockRegisters: could not translate Vrange")
  | Vinputvar r => OK (Vinputvar r)
  | Vlit v => OK (Vlit v)
  end.

Fixpoint clock_stmnt (t: PTree.t expr) (f: stmnt): 
    res (PTree.t expr * stmnt) :=
  match f with
  | Vblock (Vvar r) e => 
    do fe <- clock_expr t e;
    OK (PTree.set r fe t, (Vnonblock (Vvar r) fe))
  | Vnonblock (Vvar r) e =>
    (* let fe := clock_expr t e in  *)
    (* OK (PTree.set r fe t, Vnonblock (Vvar r) fe) *)
    Error (msg "ClockRegisters: no support for nonblocking assignment")
  | Vseq a b => 
    do (t', s') <- clock_stmnt t a;
    do (t'', s'') <- clock_stmnt t' b;
    OK (t'', Vseq s' s'')
  | Vskip => OK (t, Vskip)
  | Vblock (Vvari r e) e' => Error (msg "ClockRegisters: no support for arrays")
  | Vnonblock (Vvari r e) e' => Error (msg "ClockRegisters: no support for nonblock arrays")
  | Vblock _ e' => Error (msg "ClockRegisters: no support for other blocking assignment")
  | Vnonblock _ e' => Error (msg "ClockRegisters: no support for other nonblocking assignment")
  | Vcond _ _ _ => Error (msg "ClockRegisters: no support for cond")
  | Vcase _ _ _ => Error (msg "ClockRegisters: no support for case")
  end.

(* Definition clock_assignments (s: list stmnt): list stmnt := *)
(*   snd (fold_left clock_assignment s (RTree.empty _, nil)). *)

(* Definition clock_stmnt_assignments (s: Verilog.stmnt): Errors.res Verilog.stmnt := *)
(*   do fs <- flatten_seq_block s; *)
(*   ret (fold_seq_block (clock_assignments fs)). *)

Lemma mfold_left_error:
  forall A B f l m, @mfold_left A B f l (Error m) = Error m.
Proof. now induction l. Qed.

Lemma mfold_left_cons:
  forall A B f a l x y, 
    @mfold_left A B f (a :: l) x = OK y ->
    exists x' y', @mfold_left A B f l (OK y') = OK y /\ f x' a = OK y' /\ x = OK x'.
Proof.
  intros.
  destruct x; [|now rewrite mfold_left_error in H].
  cbn in H.
  replace (fold_left (fun (a : mon A) (b : B) => bind (fun a' : A => f a' b) a) l (f a0 a) = OK y) with
    (mfold_left f l (f a0 a) = OK y) in H by auto.
  destruct (f a0 a) eqn:?; [|now rewrite mfold_left_error in H].
  eauto.
Qed.

Lemma mfold_left_app:
  forall A B f a l x y, 
    @mfold_left A B f (a ++ l) x = OK y ->
    exists y', @mfold_left A B f a x = OK y' /\ @mfold_left A B f l (OK y') = OK y.
Proof.
  induction a.
  - intros. destruct x; [|now rewrite mfold_left_error in H]. exists a. eauto.
  - intros. destruct x; [|now rewrite mfold_left_error in H]. rewrite <- app_comm_cons in H.
    exploit mfold_left_cons; eauto.
Qed.

Lemma transf_clock_stmnt_output :
  forall l t t',
    mfold_left (fun b a =>
      do (_t, a') <- clock_stmnt (PTree.empty _) (snd a);
      OK (PTree.set (fst a) a' b)) l (OK t) = OK t' ->
    forall x,
      ~ In x (List.map fst l) ->
      t' ! x = t ! x.
Proof.
  induction l.
  - cbn; intros. now inv H.
  - intros.
    exploit mfold_left_cons; eauto; simplify. inv H4. unfold bind2, bind in *.
    repeat (destruct_match; try discriminate). inv H1.
    assert (~ In x (List.map fst l)) by tauto.
    assert (fst a <> x) by tauto.
    assert ((PTree.set (fst a) s x0) ! x = x0 ! x) by (now rewrite PTree.gso by auto).
    rewrite <- H4. eauto.
Qed.

Lemma transf_clock_stmnt_spec :
  forall l t t',
    mfold_left (fun b a =>
      do (_t, a') <- clock_stmnt (PTree.empty _) (snd a);
      OK (PTree.set (fst a) a' b)) l (OK t) = OK t' ->
    list_norepet (List.map fst l) ->
    forall x y,
      In (x, y) l ->
      exists tz z, clock_stmnt (PTree.empty _) y = OK (tz, z)
                   /\ t' ! x = Some z.
Proof.
  induction l.
  - intros. inv H1.
  - intros. inv H1. exploit mfold_left_cons; eauto; simplify. inv H4. 
    unfold bind, bind2 in *. repeat (destruct_match; try discriminate; []). inv H1.
    do 2 eexists; split. eauto. inv H0. erewrite transf_clock_stmnt_output; eauto. 
    now rewrite PTree.gss.
    exploit mfold_left_cons; eauto; simplify. inv H5.
    unfold bind, bind2 in *. repeat (destruct_match; try discriminate; []). inv H1.
    inv H0. exploit IHl; eauto.
Qed.

Lemma transf_clock_stmnt_spec_in :
  forall l t',
    mfold_left (fun b a =>
      do (_t, a') <- clock_stmnt (PTree.empty _) (snd a);
      OK (PTree.set (fst a) a' b)) l (OK (PTree.empty _)) = OK t' ->
    list_norepet (List.map fst l) ->
    forall x y,
      t' ! x = Some y ->
      exists y', In (x, y') l.
Proof.
  intros. destruct (in_dec peq x (List.map fst l)).
  - eapply in_map_iff in i; simplify. destruct x0; cbn in *. eauto.
  - exploit transf_clock_stmnt_output; eauto; intros.
    rewrite H1 in H2. rewrite PTree.gempty in H2. discriminate.
Qed.

Definition max_pc_map (m : Maps.PTree.t stmnt) :=
  PTree.fold (fun m pc i => Pos.max m pc) m 1%positive.

Lemma max_pc_map_sound:
  forall m pc i, m!pc = Some i -> Ple pc (max_pc_map m).
Proof.
  intros until i. unfold max_pc_function.
  apply PTree_Properties.fold_rec with (P := fun c m => c!pc = Some i -> Ple pc m).
  (* extensionality *)
  intros. apply H0. rewrite H; auto.
  (* base case *)
  rewrite PTree.gempty. congruence.
  (* inductive case *)
  intros. rewrite PTree.gsspec in H2. destruct (peq pc k).
  inv H2. unfold Ple; lia.
  apply Ple_trans with a. auto. unfold Ple; lia.
Qed.

Lemma max_pc_wf :
  forall m, Z.pos (max_pc_map m) <= Integers.Int.max_unsigned ->
            map_well_formed m.
Proof.
  unfold map_well_formed. intros.
  exploit list_in_map_inv. eassumption. intros [x [A B]]. destruct x.
  apply Maps.PTree.elements_complete in B. apply max_pc_map_sound in B.
  unfold Ple in B. apply Pos2Z.pos_le_pos in B. subst.
  simplify. transitivity (Z.pos (max_pc_map m)); eauto.
Qed.

Program Definition transf_module (m: DHTL.module) : Errors.res DHTL.module :=
  do dp <- mfold_left (fun b a =>
             do (_t, a') <- clock_stmnt (PTree.empty _) (snd a);
             OK (PTree.set (fst a) a' b)) (PTree.elements m.(mod_datapath)) (Errors.OK (PTree.empty _));
  match zle (Z.pos (max_pc_map dp)) Integers.Int.max_unsigned with
  | left LEDATA =>
    OK (mkmodule m.(mod_params)
      dp
      m.(mod_entrypoint)
      m.(mod_st)
      m.(mod_stk)
      m.(mod_stk_len)
      m.(mod_finish)
      m.(mod_return)
      m.(mod_start)
      m.(mod_reset)
      m.(mod_clk)
      m.(mod_scldecls)
      m.(mod_arrdecls)
      m.(mod_ram) 
      (max_pc_wf _ LEDATA)
      m.(mod_ordering_wf)
      m.(mod_ram_wf)
      m.(mod_params_wf))
  | _ => Error (msg "ClockRegisters: Failed")
  end.

Definition transf_fundef := transf_partial_fundef transf_module.

Definition transf_program (p : DHTL.program) : Errors.res DHTL.program :=
  transform_partial_program transf_fundef p.
