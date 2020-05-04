From coqup Require Import Verilog Veriloggen Coquplib Value.
From compcert Require Import AST Errors Maps Op Integers.
From compcert Require RTL.
From Coq Require Import FSets.FMapPositive.
Import ListNotations.
Import HexNotationValue.
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
  apply step_module with (assoc1 := empty_assoclist)
                         (nbassoc := (add_assoclist 7%positive (32'h"3") empty_assoclist)); auto.
  apply mis_stepp_Cons with (s1 := State test_output_module empty_assoclist (add_assoclist 7%positive (32'h"3") empty_assoclist) test_fextclk 1%nat (32'h"1")).
  apply mi_stepp_Valways_ff.
  apply stmnt_runp_Vcond_true with (f := test_fextclk 1%nat)
                                   (assoc := empty_assoclist)
                                   (vc := 1'h"1"); auto.
  apply get_state_fext_assoc.
  apply erun_Vbinop with (lv := 1'h"1")
                         (rv := 1'h"1")
                         (oper := veq)
                         (EQ := EQ_trivial (1'h"1")); auto.
  apply erun_Vinputvar; auto.
  apply erun_Vlit.
  eapply stmnt_runp_Vnonblock. simpl. auto.
  apply erun_Vlit.
  auto.
  eapply mis_stepp_Cons.
  apply mi_stepp_Valways_ff.
  eapply stmnt_runp_Vcase_nomatch.
  apply get_state_fext_assoc.
  apply erun_Vvar_empty. auto.
  apply erun_Vlit.
  unfold ZToValue. instantiate (1 := 32%nat). simpl.
