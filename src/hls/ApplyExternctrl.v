Require Import compcert.common.Errors.
Require Import compcert.common.AST.

Require Import vericert.common.Maps.
Require Import vericert.common.Statemonad.
Require Import vericert.common.Vericertlib.
Require Import vericert.hls.AssocMap.
Require Import vericert.hls.HTL.
Require Import vericert.hls.Verilog.

Import ListNotations.

Section APPLY_EXTERNCTRL.
  Local Open Scope assocmap.
  Local Open Scope error_monad_scope.

  Variable prog : HTL.program.
  Variable m : HTL.module.

  Let modmap := prog_modmap prog.

  Definition global_clk :=
    match modmap ! (AST.prog_main prog) with
    | None => Error (msg "ApplyExternctrl: No main")
    | Some main => OK (HTL.mod_clk main)
    end.

  Definition get_mod_signal (othermod : HTL.module) (signal : HTL.controlsignal) :=
    match signal with
    | ctrl_finish => OK (HTL.mod_finish othermod)
    | ctrl_return => OK (HTL.mod_return othermod)
    | ctrl_start => OK (HTL.mod_start othermod)
    | ctrl_reset => OK (HTL.mod_reset othermod)
    | ctrl_clk => OK (HTL.mod_clk othermod)
    | ctrl_param idx =>
      match List.nth_error (HTL.mod_params othermod) idx with
      | Some r => OK r
      | None => Error (msg "Module does not have nth parameter")
      end
    end.

  Definition reg_apply_externctrl (r : Verilog.reg) : res reg :=
    match (HTL.mod_externctrl m) ! r with
    | None => OK r
    | Some (m, signal) =>
      match modmap ! m with
      | None => Error (msg "Veriloggen: Could not find definition for called module")
      | Some othermod => get_mod_signal othermod signal
      end
    end.

  Fixpoint expr_apply_externctrl (expr : Verilog.expr) {struct expr} : res Verilog.expr :=
    match expr with
    | Vlit n =>
      OK (Vlit n)
    | Vvar r =>
      do r' <- reg_apply_externctrl r;
      OK (Vvar r')
    | Vvari r e =>
      do r' <- reg_apply_externctrl r;
      do e' <- expr_apply_externctrl e;
      OK (Vvari r e)
    | Vrange r e1 e2 =>
      do r' <- reg_apply_externctrl r;
      do e1' <- expr_apply_externctrl e1;
      do e2' <- expr_apply_externctrl e2;
      OK (Vrange r' e1' e2')
    | Vinputvar r =>
      do r' <- reg_apply_externctrl r;
      OK (Vinputvar r')
    | Vbinop op e1 e2 =>
      do e1' <- expr_apply_externctrl e1;
      do e2' <- expr_apply_externctrl e2;
      OK (Vbinop op e1' e2')
    | Vunop op e =>
      do e' <- expr_apply_externctrl e;
      OK (Vunop op e')
    | Vternary e1 e2 e3 =>
      do e1' <- expr_apply_externctrl e1;
      do e2' <- expr_apply_externctrl e2;
      do e3' <- expr_apply_externctrl e3;
      OK (Vternary e1' e2' e3')
    end.

  Definition mmap_option {A B} (f : A -> res B) (opt : option A) : res (option B) :=
    match opt with
    | None => OK None
    | Some a => do a' <- f a; OK (Some a')
    end.

  Definition cases_apply_externctrl_ (stmnt_apply_externctrl_ : Verilog.stmnt -> res Verilog.stmnt) :=
    fix cases_apply_externctrl (cs : list (Verilog.expr * Verilog.stmnt)) :=
      match cs with
      | nil => OK nil
      | (c_e, c_s) :: tl =>
        do c_e' <- expr_apply_externctrl c_e;
        do c_s' <- stmnt_apply_externctrl_ c_s;
        do tl' <- cases_apply_externctrl tl;
        OK ((c_e', c_s') :: tl')
      end.

  Fixpoint stmnt_apply_externctrl (stmnt : Verilog.stmnt) {struct stmnt} : res Verilog.stmnt :=
    match stmnt with
    | Vskip => OK Vskip
    | Vseq s1 s2 =>
      do s1' <- stmnt_apply_externctrl s1;
      do s2' <- stmnt_apply_externctrl s2;
      OK (Vseq s1' s2')
    | Vcond e s1 s2 =>
      do e' <- expr_apply_externctrl e;
      do s1' <- stmnt_apply_externctrl s1;
      do s2' <- stmnt_apply_externctrl s2;
      OK (Vcond e' s1' s2')
    | Vcase e cases def =>
      do e' <- expr_apply_externctrl e;
      do cases' <- cases_apply_externctrl_ stmnt_apply_externctrl cases;
      do def' <- mmap_option (fun x => stmnt_apply_externctrl x) def;
      OK (Vcase e' cases' def')
    | Vblock e1 e2 =>
      do e1' <- expr_apply_externctrl e1;
      do e2' <- expr_apply_externctrl e2;
      OK (Vblock e1' e2')
    | Vnonblock e1 e2 =>
      do e1' <- expr_apply_externctrl e1;
      do e2' <- expr_apply_externctrl e2;
      OK (Vnonblock e1' e2')
    end.

  (* Unused. Defined for completeness *)
  Definition cases_apply_externctrl := cases_apply_externctrl_ stmnt_apply_externctrl.

  Fixpoint xassocmap_apply_externctrl {A} (regmap : list (reg * A)) : res (list (reg * A)) :=
    match regmap with
    | nil => OK nil
    | (r, v) :: l =>
      do r' <- reg_apply_externctrl r;
      do l' <- xassocmap_apply_externctrl l;
      OK ((r', v) :: l')
    end.

  Definition assocmap_apply_externctrl {A} (regmap : AssocMap.t A) : res (AssocMap.t A) :=
    do l <- xassocmap_apply_externctrl (AssocMap.elements regmap);
    OK (AssocMap_Properties.of_list l).

  Definition module_apply_externctrl : res HTL.module :=
    do mod_start' <- reg_apply_externctrl (HTL.mod_start m);
    do mod_reset' <- reg_apply_externctrl (HTL.mod_reset m);
    do mod_clk' <- global_clk;
    do mod_finish' <- reg_apply_externctrl (HTL.mod_finish m);
    do mod_return' <- reg_apply_externctrl (HTL.mod_return m);
    do mod_st' <- reg_apply_externctrl (HTL.mod_st m);
    do mod_stk' <- reg_apply_externctrl (HTL.mod_stk m);
    do mod_params' <- mmap reg_apply_externctrl (HTL.mod_params m);
    do mod_controllogic' <- PTree.traverse1 stmnt_apply_externctrl (HTL.mod_controllogic m);
    do mod_datapath' <- PTree.traverse1 stmnt_apply_externctrl (HTL.mod_datapath m);

    do mod_scldecls' <- assocmap_apply_externctrl (HTL.mod_scldecls m);
    do mod_arrdecls' <- assocmap_apply_externctrl (HTL.mod_arrdecls m);
    do mod_externctrl' <- assocmap_apply_externctrl (HTL.mod_externctrl m);

    match zle (Z.pos (max_pc_map mod_datapath')) Integers.Int.max_unsigned,
          zle (Z.pos (max_pc_map mod_controllogic')) Integers.Int.max_unsigned with
    | left LEDATA, left LECTRL =>
      OK (HTL.mkmodule
             mod_params'
             mod_datapath'
             mod_controllogic'
             (HTL.mod_entrypoint m)
             mod_st'
             mod_stk'
             (HTL.mod_stk_len m)
             mod_finish'
             mod_return'
             mod_start'
             mod_reset'
             mod_clk'
             mod_scldecls'
             mod_arrdecls'
             mod_externctrl'
             (conj (max_pc_wf _ _ LECTRL) (max_pc_wf _ _ LEDATA)))
    | _, _ => Error (Errors.msg "More than 2^32 states.")
    end.
End APPLY_EXTERNCTRL.

Definition transf_fundef (prog : HTL.program) := transf_partial_fundef (module_apply_externctrl prog).
Definition transf_program (prog : HTL.program) := transform_partial_program (transf_fundef prog) prog.

(* Semantics *)

Definition match_prog : HTL.program -> HTL.program -> Prop :=
  Linking.match_program (fun ctx f tf => ApplyExternctrl.transf_fundef ctx f = OK tf) eq.

Lemma transf_program_match : forall p tp,
  ApplyExternctrl.transf_program p = OK tp -> match_prog p tp.
Admitted.

Lemma transf_program_correct : forall p tp,
  match_prog p tp -> Smallstep.forward_simulation (HTL.semantics p) (HTL.semantics tp).
Admitted.

Instance TransfLink : Linking.TransfLink match_prog.
Admitted.
