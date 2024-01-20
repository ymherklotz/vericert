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
Require Import vericert.common.Monad.
Require Import vericert.common.Optionmonad.
Require Import vericert.hls.Verilog.
Require Import vericert.hls.DHTL.

Import OptionExtra.

#[local] Open Scope monad_scope.

Definition pred := positive.

Fixpoint check_excluded (r: reg) (e: expr) :=
  match e with
  | Vlit v => true
  | Vvar r' => negb (Pos.eqb r r')
  | Vvari r' e => (negb (Pos.eqb r r')) && (check_excluded r e)
  | Vrange r' e1 e2 => (negb (Pos.eqb r r')) && (check_excluded r e1) && (check_excluded r e2)
  | Vinputvar r' => negb (Pos.eqb r r')
  | Vbinop _ e1 e2 => (check_excluded r e1) && (check_excluded r e2)
  | Vunop _ e1 => (check_excluded r e1)
  | Vternary e1 e2 e3 => (check_excluded r e1) && (check_excluded r e2) && (check_excluded r e3)
  end.

Definition transf_maps st (d: stmnt) :=
  match d with
  | Vseq (Vseq Vskip (Vblock (Vvari r e1) e2)) ((Vblock (Vvar r2) e3) as rest) as orig =>
    if (check_excluded r e3) 
    && (check_excluded r2 e1) 
    && (check_excluded r2 e2) 
    && (negb (Pos.eqb r2 r)) 
    && (Pos.eqb r st) then
      Vseq rest (Vnonblock (Vvari r e1) e2)
    else orig
  | Vseq (Vseq Vskip (Vblock (Vvar r1) (Vvari r e2))) (Vblock (Vvar st') e3) as orig =>
    if (check_excluded r1 e3) 
    && (check_excluded st' e2) 
    && (negb (Pos.eqb r1 r)) 
    && (negb (Pos.eqb r1 st')) 
    && (negb (Pos.eqb r st')) 
    && (Pos.eqb r st) then
      Vseq (Vblock (Vvar st') e3) (Vnonblock (Vvar r1) (Vvari r e2))
    else orig
  | _ => d
  end.

Program Definition transf_module (m: DHTL.module) : DHTL.module :=
  mkmodule m.(mod_params)
      (PTree.map1 (transf_maps m.(mod_stk)) m.(mod_datapath))
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
      _
      m.(mod_ordering_wf)
      m.(mod_ram_wf)
      m.(mod_params_wf).
Next Obligation.
  unfold map_well_formed; intros. apply AssocMapExt.elements_iff in H. simplify.
  rewrite PTree.gmap1 in H0.
  pose proof (mod_wf m). unfold map_well_formed in *.
  unfold option_map in *. destruct_match; try discriminate. 
  eapply H. apply AssocMapExt.elements_iff. eauto.
Qed.

Definition transf_fundef := transf_fundef transf_module.

Definition transf_program (p : DHTL.program) : DHTL.program :=
  transform_program transf_fundef p.
