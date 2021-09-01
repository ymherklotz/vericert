Require Import compcert.common.AST.

Require Import vericert.hls.HTL.
Require Import vericert.hls.Verilog.
Require Import vericert.hls.AssocMap.

Require Import vericert.common.Statemonad.
Require Import vericert.common.Vericertlib.
Require Import vericert.common.Maps.

Record renumber_state: Type :=
  mk_renumber_state {
    renumber_freshreg : reg;
    renumber_regmap : PTree.t reg;
  }.

Module RenumberState <: State.
  Definition st := renumber_state.

  Definition st_prop (st1 st2 : st) := True.
  Hint Unfold st_prop : htl_renumber.

  Lemma st_refl : forall (s : st), st_prop s s.
  Proof. constructor. Qed.

  Lemma st_trans : forall s1 s2 s3, st_prop s1 s2 -> st_prop s2 s3 -> st_prop s1 s3.
  Proof. constructor. Qed.
End RenumberState.

Module RenumberMonad := Statemonad(RenumberState).
Module RenumberMonadExtra := Monad.MonadExtra(RenumberMonad).

Import RenumberMonad.
Import RenumberState.
Import RenumberMonadExtra.
Import MonadNotation.

Definition map_reg (r: reg) : mon reg :=
  fun st => OK
        (renumber_freshreg st)
        (mk_renumber_state (Pos.succ (renumber_freshreg st))
                          (PTree.set r (renumber_freshreg st) (renumber_regmap st)))
        ltac:(auto with htl_renumber).

Definition clear_regmap : mon unit :=
  fun st => OK
        tt
        (mk_renumber_state (renumber_freshreg st)
                          (PTree.empty reg))
        ltac:(auto with htl_renumber).

Definition renumber_reg (r : reg) : mon reg :=
  do st <- get;
  match PTree.get r (renumber_regmap st) with
  | Some reg' => ret reg'
  | None => map_reg r
  end.

Fixpoint renumber_expr (expr : Verilog.expr) :=
  match expr with
  | Vlit val => ret (Vlit val)
  | Vvar reg =>
    do reg' <- renumber_reg reg;
    ret (Vvar reg')
  | Vvari reg e =>
    do reg' <- renumber_reg reg;
    do e' <- renumber_expr e;
    ret (Vvari reg' e')
  | Vinputvar reg =>
    do reg' <- renumber_reg reg;
    ret (Vvar reg')
  | Vbinop op e1 e2 =>
    do e1' <- renumber_expr e1;
    do e2' <- renumber_expr e2;
    ret (Vbinop op e1' e2')
  | Vunop op e =>
    do e' <- renumber_expr e;
    ret (Vunop op e')
  | Vternary e1 e2 e3 =>
    do e1' <- renumber_expr e1;
    do e2' <- renumber_expr e2;
    do e3' <- renumber_expr e3;
    ret (Vternary e1' e2' e3')
  | Vrange r e1 e2 =>
    do e1' <- renumber_expr e1;
    do e2' <- renumber_expr e2;
    do r' <- renumber_reg r;
    ret (Vrange r e1' e2')
  end.

  Definition renumber_cases_ (renumber_stmnt_ : Verilog.stmnt -> mon Verilog.stmnt) :=
    fix renumber_cases (cs : stmnt_expr_list) :=
      match cs with
      | Stmntnil  => ret Stmntnil
      | Stmntcons c_e c_s tl =>
        do c_e' <- renumber_expr c_e;
        do c_s' <- renumber_stmnt_ c_s;
        do tl' <- renumber_cases tl;
        ret (Stmntcons c_e' c_s' tl')
      end.

Fixpoint renumber_stmnt (stmnt : Verilog.stmnt) :=
  match stmnt with
  | Vskip => ret Vskip
  | Vseq s1 s2 =>
    do s1' <- renumber_stmnt s1;
    do s2' <- renumber_stmnt s2;
    ret (Vseq s1' s2')
  | Vcond e s1 s2 =>
    do e' <- renumber_expr e;
    do s1' <- renumber_stmnt s1;
    do s2' <- renumber_stmnt s2;
    ret (Vcond e' s1' s2')
  | Vcase e cs def =>
    do e' <- renumber_expr e;
    do cs' <- renumber_cases_ renumber_stmnt cs;
    do def' <- match def with
              | None => ret None
              | Some d => do def' <- renumber_stmnt d; ret (Some def')
              end;
    ret (Vcase e' cs' def')
  | Vblock e1 e2 =>
    do e1' <- renumber_expr e1;
    do e2' <- renumber_expr e2;
    ret (Vblock e1' e2')
  | Vnonblock e1 e2 =>
    do e1' <- renumber_expr e1;
    do e2' <- renumber_expr e2;
    ret (Vnonblock e1' e2')
  end.

Fixpoint xrenumber_reg_assocmap {A} (regmap : list (reg * A)) : mon (list (reg * A)) :=
  match regmap with
  | nil => ret nil
  | (r, v) :: l =>
    do r' <- renumber_reg r;
    do l' <- xrenumber_reg_assocmap l;
    ret ((r', v) :: l')
  end.

Definition renumber_reg_assocmap {A} (regmap : AssocMap.t A) : mon (AssocMap.t A) :=
  do l <- xrenumber_reg_assocmap (AssocMap.elements regmap);
  ret (AssocMap_Properties.of_list l).

Definition renumber_module (m : HTL.module) : mon HTL.module :=
    do mod_params' <- traverselist renumber_reg (HTL.mod_params m);

    do mod_st' <- renumber_reg (HTL.mod_st m);
    do mod_finish' <- renumber_reg (HTL.mod_finish m);
    do mod_return' <- renumber_reg (HTL.mod_return m);
    do mod_stk' <- renumber_reg (HTL.mod_stk m);
    do mod_start' <- renumber_reg (HTL.mod_start m);
    do mod_reset' <- renumber_reg (HTL.mod_reset m);
    do mod_clk' <- renumber_reg (HTL.mod_clk m);

    do mod_controllogic' <- traverse_ptree1 renumber_stmnt (HTL.mod_controllogic m);
    do mod_datapath' <- traverse_ptree1 renumber_stmnt (HTL.mod_datapath m);

    do mod_scldecls' <- renumber_reg_assocmap (HTL.mod_scldecls m);
    do mod_arrdecls' <- renumber_reg_assocmap (HTL.mod_arrdecls m);
    do mod_externctrl' <- renumber_reg_assocmap (HTL.mod_externctrl m);

    do _ <- clear_regmap;

    match zle (Z.pos (max_pc_map mod_datapath')) Integers.Int.max_unsigned,
          zle (Z.pos (max_pc_map mod_controllogic')) Integers.Int.max_unsigned,
          decide_order mod_st' mod_finish' mod_return' mod_stk' mod_start' mod_reset' mod_clk',
          max_list_dec mod_params' mod_st',
          option_ram_wf mod_clk' (HTL.mod_ram m) with
    | left LEDATA, left LECTRL, left MORD, left WFPARAMS, Some WFRAM =>
      ret (HTL.mkmodule
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
          (HTL.mod_ram m)
          (conj (max_pc_wf _ _ LECTRL) (max_pc_wf _ _ LEDATA))
          MORD
          WFRAM
          WFPARAMS)
    | right _, _, _, _, _ => error (Errors.msg "Renaming: More than 2^32 datapath states")
    | _, right _, _, _, _ => error (Errors.msg "Renaming: More than 2^32 controlpath states")
    | _, _, right _, _, _ => error (Errors.msg "Renaming: Incorrect ordering of control registers")
    | _, _, _, right _, _ => error (Errors.msg "Renaming: Parameter registers conflict with control registers")
    | _, _, _, _, None    => error (Errors.msg "Renaming: Ram address register conflicts with control registers")
    end.

Definition renumber_fundef (fundef : HTL.fundef) : mon HTL.fundef :=
  match fundef with
  | Internal m => do renumbered <- renumber_module m; ret (Internal renumbered)
  | _ => ret fundef
  end.

Section TRANSF_PROGRAM_STATEFUL.
  Import RenumberMonad.
  Import RenumberState.
  Import RenumberMonadExtra.
  Import MonadNotation.

  Variables A B V : Type.
  Variable transf_fun: ident -> A -> RenumberMonad.mon B.

  Fixpoint transf_globdefs (l: list (ident * globdef A V)) : RenumberMonad.mon (list (ident * globdef B V)) :=
    match l with
    | nil => RenumberMonad.ret nil
    | (id, Gfun f) :: l' =>
      do tf <- transf_fun id f;
      do tl' <- transf_globdefs l';
      RenumberMonad.ret ((id, Gfun tf) :: tl')
    | (id, Gvar v) :: l' =>
      do tl' <- transf_globdefs l';
      RenumberMonad.ret ((id, Gvar v) :: tl')
    end.

  Definition transform_stateful_program (init_state : RenumberState.st) (p: AST.program A V) : Errors.res (AST.program B V) :=
    RenumberMonad.run_mon init_state (
                        do gl' <- transf_globdefs p.(prog_defs);
                        RenumberMonad.ret (mkprogram gl' p.(prog_public) p.(prog_main))).

End TRANSF_PROGRAM_STATEFUL.

Definition transf_program (p : HTL.program) : Errors.res HTL.program :=
  transform_stateful_program _ _ _
                              (fun _ f => renumber_fundef f)
                              (mk_renumber_state 1%positive (PTree.empty reg))
                              p.

Definition match_prog : HTL.program -> HTL.program -> Prop := fun _ _ => True.

Instance TransfRenamingLink : Linking.TransfLink match_prog.
Admitted.

Lemma transf_program_match : forall p tp,
  Renaming.transf_program p = Errors.OK tp -> match_prog p tp.
Admitted.

Lemma transf_program_correct : forall p tp,
  match_prog p tp -> Smallstep.forward_simulation (HTL.semantics p) (HTL.semantics tp).
Admitted.
