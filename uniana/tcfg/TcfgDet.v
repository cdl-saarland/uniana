Require Export TcfgqMonotone.
Require Import Lia.

Section cfg.
  Context `{C : redCFG}.

  (* TODO: adjust to new monotonicity *)
  Lemma eff_tag_fresh : forall p q i j l,
      TPath (root,start_tag) (q,j) l -> tcfg_edge (q,j) (p,i) -> forall i', In (p, i') l -> i' <> i.
  Proof.
    intros ? ? ? ? ? Hpath Heff ? Hel Heq.
    subst i'.
    eapply path_from_elem in Hel as Hpi;eauto. destructH.
    eapply PathCons in Heff;eauto.
    eapply tcfg_fresh in Heff;eauto.
    - eapply Taglt_irrefl;eauto.
    - eapply path_to_elem in Hpath;eauto. destructH. eapply tag_depth';eauto.
    - destruct ϕ;[inv Hpi0|]. cbn. lia.
  Qed.

  Lemma eff_tag_det : forall  q j p i i',
      eff_tag q p j = i ->
      eff_tag q p j = i' ->
      i = i'.
  Proof.
    intros. rewrite <-H, <-H0. reflexivity.
  Qed.

  Lemma eff_tag_det'
    : forall (q : Lab) (j : Tag) (p : Lab) (i i' : Tag),
      eff_tag q p j = Some i -> eff_tag q p j = Some i' -> i = i'.
  Proof.
    intros.
    eapply eff_tag_det in H;eauto. inversion H;eauto.
  Qed.

  Lemma tcfg_edge_det p q j i1 i2
        (Hedge1 : tcfg_edge (q,j) (p,i1))
        (Hedge2 : tcfg_edge (q,j) (p,i2))
    : i1 = i2.
  Proof.
    unfold tcfg_edge in *.
    do 2 destructH. rewrite Hedge4 in Hedge3. inv Hedge3. reflexivity.
  Qed.

  (** ** Tagged paths are duplicate-free **)

  Lemma tpath_NoDup q t
        (Hpath : TPath (root,start_tag) q t)
    : NoDup t.
  Proof.
    revert q Hpath. induction t.
    - econstructor; eauto.
    - intros. unfold TPath in Hpath. path_simpl' Hpath.
      econstructor.
      + intro. inversion Hpath; subst; cbn in H; [contradiction|].
        destruct q. destruct b. eapply eff_tag_fresh;eauto.
      + inversion Hpath; subst;[econstructor|]. destruct b, q.
        eapply IHt;eauto.
  Qed.

  Lemma tpath_NoDup_unroot p q i j t
        (Hpath : TPath (p,i) (q,j) t)
        (Hdep : | i | = depth p)
    : NoDup t.
  Proof.
    eapply tcfg_enroot in Hpath;eauto. destructH.
    eapply tpath_NoDup in Hpath. eapply NoDup_app_drop;eauto.
  Qed.

End cfg.
