(*
 * CoqUp: Verified high-level synthesis.
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

From coqup Require Import Verilog Veriloggen Coquplib Value.
From compcert Require Import AST Errors Maps Op Integers.
From compcert Require RTL.
From Coq Require Import FSets.FMapPositive.
From bbv Require Import Word.
Import ListNotations.
Import HexNotationValue.
Import WordScope.

Local Open Scope word_scope.

Definition test_module : module :=
  let mods := [
      Valways (Vposedge 3%positive) (Vseq (Vnonblock (Vvar 6%positive) (Vlit (ZToValue 32 5)))
                                          (Vnonblock (Vvar 7%positive)
                                                     (Vvar 6%positive)))
      ] in
  mkmodule (1%positive, 1%nat)
           (2%positive, 1%nat)
           (3%positive, 1%nat)
           (4%positive, 1%nat)
           (5%positive, 32%nat)
           (6%positive, 32%nat)
           nil
           mods.

Definition test_input : RTL.function :=
  let sig := mksignature nil Tvoid cc_default in
  let params := nil in
  let stacksize := 0 in
  let entrypoint := 3%positive in
  let code := PTree.set 1%positive (RTL.Ireturn (Some 1%positive))
               (PTree.set 3%positive (RTL.Iop (Ointconst (Int.repr 5)) nil 1%positive 1%positive)
                          (PTree.empty RTL.instruction)) in
  RTL.mkfunction sig params stacksize code entrypoint.

Definition test_input_program : RTL.program :=
  mkprogram [(1%positive, Gfun (Internal test_input))] nil 1%positive.

Compute transf_program test_input_program.

Definition test_output_module : module :=
  {| mod_start := (4%positive, 1%nat);
     mod_reset := (5%positive, 1%nat);
     mod_clk := (6%positive, 1%nat);
     mod_finish := (2%positive, 1%nat);
     mod_return := (3%positive, 32%nat);
     mod_state := (7%positive, 32%nat);
     mod_args := [];
     mod_body :=
       [Valways_ff (Vposedge 6%positive)
                   (Vcond (Vbinop Veq (Vinputvar 5%positive) (1'h"1"))
                          (Vnonblock (Vvar 7%positive) (32'h"3"))
                          (Vcase (Vvar 7%positive)
                                 [(Vlit (32'h"1"), Vnonblock (Vvar 7%positive) (32'h"1"));
                                 (Vlit (32'h"3"), Vnonblock (Vvar 7%positive) (32'h"1"))]
                                 (Some Vskip)));
       Valways_ff (Vposedge 6%positive)
                  (Vcase (Vvar 7%positive)
                         [(Vlit (32'h"1"), Vseq (Vblock (Vvar 2%positive) (Vlit (1'h"1")))
                                                (Vblock (Vvar 3%positive) (Vvar 1%positive)));
                         (Vlit (32'h"3"), Vblock (Vvar 1%positive) (Vlit (32'h"5")))]
                         (Some Vskip));
       Vdecl 1%positive 32; Vdecl 7%positive 32] |}.

Search (_ <> _ -> _ = _).

Lemma valid_test_output :
  transf_program test_input_program = OK test_output_module.
Proof. trivial. Qed.

Definition test_fextclk := initial_fextclk test_output_module.

Lemma manual_simulation :
  step (State test_output_module empty_assoclist empty_assoclist
              test_fextclk 1 (32'h"1"))
       (State test_output_module (add_assoclist 7%positive (32'h"3") empty_assoclist)
              empty_assoclist test_fextclk 2 (32'h"3")).
Proof.
  repeat (econstructor; eauto);
  try (simpl; unfold ZToValue; simpl; instantiate (1 := eq_refl (vsize (1'h"1"))); auto);
  apply nevalue; apply weqb_false; trivial.
  Unshelve. exact 0%nat.
Qed.
