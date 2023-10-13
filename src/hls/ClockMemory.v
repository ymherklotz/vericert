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

Definition transf_maps (d: stmnt) :=
  match d with
  | Vseq ((Vblock (Vvar _) _) as rest) (Vblock (Vvari r e1) e2) =>
    Vseq rest (Vnonblock (Vvari r e1) e2)
  | Vseq (Vblock (Vvar st') e3) (Vblock (Vvar e1) (Vvari r e2)) =>
    Vseq (Vblock (Vvar st') e3) (Vnonblock (Vvar e1) (Vvari r e2))
  | _ => d
  end.

Program Definition transf_module (m: DHTL.module) : DHTL.module :=
  mkmodule m.(mod_params)
      (PTree.map1 transf_maps m.(mod_datapath))
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
Admitted.

Definition transf_fundef := transf_fundef transf_module.

Definition transf_program (p : DHTL.program) : DHTL.program :=
  transform_program transf_fundef p.
