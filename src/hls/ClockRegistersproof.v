Lemma expr_runp_same :
  forall f rs1 ar1 c v,
    expr_runp f rs1 ar1 c v ->
    forall trs1,
      match_assocmaps rs1 trs1 ->
      expr_runp f trs1 ar1 c v.
Proof.
  induction 1; intros.
  - econstructor.
  - econstructor. erewrite match_assocmaps_inv_map; eauto.
  - exploit IHexpr_runp; eauto; intros. econstructor; eauto.
  - exploit IHexpr_runp1; eauto; exploit IHexpr_runp2; eauto; intros.
    econstructor; eauto.
  - exploit IHexpr_runp; eauto; intros. econstructor; eauto.
  - exploit IHexpr_runp1; eauto; exploit IHexpr_runp2; eauto; intros.
    econstructor; eauto.
  - exploit IHexpr_runp1; eauto; exploit IHexpr_runp2; eauto; intros.
    eapply erun_Vternary_false; eauto.
  - exploit IHexpr_runp; eauto; intros. econstructor; eauto.
    erewrite match_assocmaps_inv_map; eauto. rewrite H0. now rewrite H1.
Qed.

Lemma match_states_same :
  forall f rs1 ar1 c rs2 ar2,
    stmnt_runp f rs1 ar1 c rs2 ar2 ->
    forall trs1,
      match_reg_assocs rs1 trs1 ->
      exists trs2,
        stmnt_runp f trs1 ar1 c trs2 ar2
        /\ match_reg_assocs rs2 trs2.
Proof.
  induction 1.
  - econstructor; split; eauto; constructor.
  - intros. exploit IHstmnt_runp1; eauto; simplify. 
    exploit IHstmnt_runp2; eauto; simplify.
    econstructor; split.
    + econstructor; eauto.
    + auto.
  - intros. exploit IHstmnt_runp; eauto; simplify.
    inversion H2; subst; exploit expr_runp_same; eauto; intros.
    eexists; split; eauto; econstructor; eauto.
  - intros. exploit IHstmnt_runp; eauto; simplify.
    inversion H2; subst; exploit expr_runp_same; eauto; intros.
    eexists; split; eauto; eapply stmnt_runp_Vcond_false; eauto.
  - intros. exploit IHstmnt_runp; eauto; simplify.
    inversion H3. subst. exploit expr_runp_same; [eapply H| |]; eauto; intros.
    exploit expr_runp_same; [eapply H0| |]; eauto; intros.
    eexists; split; eauto. econstructor; eauto.
  - intros. exploit IHstmnt_runp; eauto; simplify.
    inversion H3. subst. exploit expr_runp_same; [eapply H| |]; eauto; intros.
    exploit expr_runp_same; [eapply H0| |]; eauto; intros.
    eexists; split; eauto. eapply stmnt_runp_Vcase_match; eauto.
  - intros. exploit IHstmnt_runp; eauto; simplify.
    inversion H1. subst. exploit expr_runp_same; [eapply H| |]; eauto; intros.
    eexists; split; eauto. eapply stmnt_runp_Vcase_default; eauto.
  - inv H; intros.
    inversion H. subst. exploit expr_runp_same; eauto; intros.
    econstructor; split; intros. econstructor; eauto. econstructor.
    econstructor; cbn; eauto.
    econstructor; intros.
    destruct (peq r r0); subst.
    + now rewrite !AssocMap.gss.
    + rewrite !AssocMap.gso by auto. inv H1; eauto.
  - inv H; intros.
    inversion H. subst. exploit expr_runp_same; eauto; intros.
    econstructor; split; intros. econstructor; eauto. econstructor.
    econstructor; cbn; eauto.
    econstructor; intros.
    destruct (peq r r0); subst.
    + now rewrite !AssocMap.gss.
    + rewrite !AssocMap.gso by auto. inv H2; eauto.
  - inv H; intros. inversion H; subst.
    exploit expr_runp_same; [eapply H0| |]; eauto; intros.
    exploit expr_runp_same; [eapply H6| |]; eauto; intros.
    eexists; split; eauto. econstructor; eauto. econstructor; eauto.
  - inv H; intros. inversion H; subst.
    exploit expr_runp_same; [eapply H0| |]; eauto; intros.
    exploit expr_runp_same; [eapply H6| |]; eauto; intros.
    eexists; split; eauto. econstructor; eauto. econstructor; eauto.
Qed.

Lemma exec_ram_same :
  forall rs1 ar1 c rs2 ar2,
    exec_ram rs1 ar1 c rs2 ar2 ->
    forall trs1,
      match_reg_assocs rs1 trs1 ->
      exists trs2,
        exec_ram trs1 ar1 c trs2 ar2
        /\ match_reg_assocs rs2 trs2.
Proof.
  induction 1; intros.
  - eexists; split; eauto.
    apply exec_ram_Some_idle. inv H0. cbn in *; setoid_rewrite match_assocmaps_inv_map; eauto.
  - inv H6; eexists; split; cbn in *.
    + eapply exec_ram_Some_write. eapply H. eauto. all: cbn in *.
      now erewrite match_assocmaps_inv_map by eauto.
      all: now erewrite match_assocmaps_inv by eauto.
    + unfold nonblock_reg; cbn. constructor; auto.
      now apply match_assocmaps_set.
  - inv H5; eexists; split; cbn in *.
    + eapply exec_ram_Some_read; eauto; cbn in *.
      now erewrite match_assocmaps_inv_map by eauto.
      all: now erewrite match_assocmaps_inv by eauto.
    + unfold nonblock_reg; cbn. constructor; auto.
      now repeat apply match_assocmaps_set.
  - eexists; split; cbn in *; eauto. econstructor.
Qed.
