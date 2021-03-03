(*
 * Vericert: Verified high-level synthesis.
 * Copyright (C) 2021 Yann Herklotz <yann@yannherklotz.com>
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
Require compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Floats.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require compcert.common.Smallstep.
Require compcert.verilog.Op.

Require Import vericert.common.Vericertlib.
Require Import vericert.hls.ValueInt.
Require Import vericert.hls.Verilog.
Require Import vericert.hls.HTL.
Require Import vericert.hls.AssocMap.
Require Import vericert.hls.Array.

Local Open Scope positive.

Definition max_pc_function (m: module) :=
  List.fold_left Pos.max (List.map fst (PTree.elements m.(mod_controllogic))) 1.

Definition transf_maps (st addr d_in d_out wr: reg)
           (dc: node * PTree.t stmnt * PTree.t stmnt) i :=
  match dc with
  | (n, d, c) =>
    match PTree.get i d, PTree.get i c with
    | Some d_s, Some c_s =>
      match d_s with
      | Vnonblock (Vvari r e1) e2 =>
        let nd := Vseq (Vnonblock (Vvar wr) (Vlit (ZToValue 1)))
                       (Vseq (Vnonblock (Vvar d_in) e2)
                             (Vnonblock (Vvar addr) e1))
        in
        (n, PTree.set i nd d, c)
      | Vnonblock e1 (Vvari r e2) =>
        let nd := Vseq (Vnonblock (Vvar wr) (Vlit (ZToValue 0)))
                       (Vnonblock (Vvar addr) e2)
        in
        let aout := Vnonblock e1 (Vvar d_out) in
        let redirect := Vnonblock (Vvar st) (Vlit (posToValue n)) in
        (n+1, PTree.set i nd
                        (PTree.set n aout d),
         PTree.set i redirect (PTree.set n c_s c))
      | _ => dc
      end
    | _, _ => dc
    end
  end.

Lemma transf_maps_wf :
  forall st addr d_in d_out wr n d c n' d' c' i,
  map_well_formed c /\ map_well_formed d ->
  transf_maps st addr d_in d_out wr (n, d, c) i = (n', d', c') ->
  map_well_formed c' /\ map_well_formed d'.
Proof.
  unfold map_well_formed; simplify;
    repeat destruct_match;
    match goal with | H: (_, _, _) = (_, _, _) |- _ => inv H end; eauto;
      simplify.
  apply H2.
  exploit list_in_map_inv; eauto; intros.
  inv H0. destruct x. inv H3. simplify.
  replace p with (fst (p, s)) by auto.
  apply in_map.
  apply PTree.elements_correct.
  apply PTree.elements_complete in H4.
  Admitted.

Definition set_mod_datapath d c wf m :=
  mkmodule (mod_params m)
           d
           c
           (mod_entrypoint m)
           (mod_st m)
           (mod_stk m)
           (mod_stk_len m)
           (mod_finish m)
           (mod_return m)
           (mod_start m)
           (mod_reset m)
           (mod_clk m)
           (mod_scldecls m)
           (mod_arrdecls m)
           (mod_ram m)
           wf.

Lemma is_wf:
  forall A nc nd,
@map_well_formed A nc /\ @map_well_formed A nd.
Admitted.

Definition transf_module (m: module): module :=
  let addr := m.(mod_clk)+1 in
  let d_in := m.(mod_clk)+2 in
  let d_out := m.(mod_clk)+3 in
  let wr_en := m.(mod_clk)+4 in
  match fold_left (transf_maps m.(mod_st) addr d_in d_out wr_en)
                  (map fst (PTree.elements m.(mod_datapath)))
                  (max_pc_function m + 1, m.(mod_datapath), m.(mod_controllogic))
  with
  | (_, nd, nc) =>
    mkmodule m.(mod_params)
             nd
             nc
             m.(mod_entrypoint)
             m.(mod_st)
             m.(mod_stk)
             (2 ^ Nat.log2_up m.(mod_stk_len))%nat
             m.(mod_finish)
             m.(mod_return)
             m.(mod_start)
             m.(mod_reset)
             m.(mod_clk)
             (AssocMap.set wr_en (None, VScalar 32)
              (AssocMap.set d_out (None, VScalar 32)
               (AssocMap.set d_in (None, VScalar 32)
                (AssocMap.set addr (None, VScalar 32) m.(mod_scldecls)))))
             (AssocMap.set m.(mod_stk) (None, VArray 32 (2 ^ Nat.log2_up m.(mod_stk_len)))%nat m.(mod_arrdecls))
             (Some (mk_ram (mod_stk m) addr wr_en d_in d_out))
             (is_wf _ nc nd)
  end.

Lemma fold_has_value:
  forall st d c addr d_in d_out wr_en mst data ctrl l n dstm cstm,
    data ! st = Some dstm ->
    ctrl ! st = Some cstm ->
    fold_left (transf_maps st addr d_in d_out wr_en) l
              (mst, data, ctrl) = (n, d, c) ->
    exists dstm' cstm', d ! st = Some dstm' /\ c ! st = Some cstm'.
Admitted.

Definition transf_fundef := transf_fundef transf_module.

Definition transf_program (p : program) :=
  transform_program transf_fundef p.

Inductive match_assocmaps : assocmap -> assocmap -> Prop :=
  match_assocmap: forall rs rs',
    (forall r v, rs!r = Some v -> rs'!r = Some v) ->
    match_assocmaps rs rs'.

Inductive match_arrs : assocmap_arr -> assocmap_arr -> Prop :=
  match_assocmap_arr: forall ar ar',
    (forall s arr arr',
      ar!s = Some arr ->
      ar'!s = Some arr' ->
      forall addr,
        array_get_error addr arr = array_get_error addr arr') ->
    match_arrs ar ar'.

Inductive match_states : HTL.state -> HTL.state -> Prop :=
| match_state :
    forall res m st asr asr' asa asa'
           (ASSOC: match_assocmaps asr asr')
           (ARRS: match_arrs asa asa'),
      match_states (HTL.State res m st asr asa)
                   (HTL.State res (transf_module m) st asr' asa')
| match_returnstate :
    forall res v,
      match_states (HTL.Returnstate res v) (HTL.Returnstate res v)
| match_initial_call :
    forall m,
      match_states (HTL.Callstate nil m nil)
      (HTL.Callstate nil (transf_module m) nil).
Hint Constructors match_states : htlproof.

Definition match_prog (p: program) (tp: program) :=
  Linking.match_program (fun cu f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. unfold transf_program, match_prog.
  apply Linking.match_transform_program.
Qed.

Section CORRECTNESS.

  Context (prog: program).

  Let tprog := transf_program prog.

  Let ge : HTL.genv := Globalenvs.Genv.globalenv prog.

  Lemma transf_maps_preserves_behaviour :
    forall m m' s addr d_in d_out wr n n' t stk rs ar d' c' wf' i,
      m' = set_mod_datapath d' c' wf' m ->
      transf_maps m.(mod_st) addr d_in d_out wr (n, mod_datapath m, mod_controllogic m) i = (n', d', c') ->
      step ge (State stk m s rs ar) t (State stk m s rs ar) ->
      forall R1,
        match_states (State stk m s rs ar) R1 ->
        exists R2, step ge R1 t R2 /\ match_states (State stk m s rs ar) R2.
  Proof.
    Admitted.

  Lemma fold_transf_maps_preserves_behaviour :
    forall m m' s addr d_in d_out wr n' t stk rs ar d' c' wf' l rs' ar',
      fold_left (transf_maps m.(mod_st) addr d_in d_out wr) l
                  (max_pc_function m + 1, m.(mod_datapath), m.(mod_controllogic)) = (n', d', c') ->
      m' = set_mod_datapath d' c' wf' m ->
      step ge (State stk m s rs ar) t (State stk m s rs' ar') ->
      exists R2, step ge (State stk m' s rs ar) t R2 /\ match_states (State stk m s rs' ar') R2.
  Proof.
    Admitted.

  Theorem transf_step_correct:
    forall (S1 : state) t S2,
      step ge S1 t S2 ->
        forall R1,
          match_states S1 R1 ->
            exists R2, Smallstep.plus step ge R1 t R2 /\ match_states S2 R2.
  Proof.
    pose proof fold_transf_maps_preserves_behaviour.
    induction 1.
    - exploit fold_transf_maps_preserves_behaviour. intros. inv H13. inv ASSOC. inv ARRS.
      econstructor.
      econstructor.
      eapply Smallstep.plus_one.
      econstructor; unfold transf_module; repeat destruct_match; try solve [crush].
      + simplify.


End CORRECTNESS.
