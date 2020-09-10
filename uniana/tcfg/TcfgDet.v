Require Export TcfgLoop.

Section cfg.
  Context `{C : redCFG}.

  (* TODO: adjust to new monotonicity *)
  Lemma eff_tag_fresh : forall p q i j l,
      TPath (root,start_tag) (q,j) l -> eff_tag q p j = Some i -> forall i', In (p, i') l -> i' <> i.
  Proof.
    intros ? ? ? ? ? Hpath Heff ? Hel Heq.
    unfold eff_tag in Heff. decide (edge__P q p);[|congruence].
    subst i'.
    admit.
  Admitted. (*
  eapply eff_tag_unfresh;eauto.
Qed. *)

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
    (* PROVEME *)
  Admitted.

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
        destruct q. destruct b. eapply eff_tag_fresh;eauto. destruct H4. eauto.
      + inversion Hpath; subst;[econstructor|]. destruct b, q.
        eapply IHt;eauto.
  Qed.
End cfg.
