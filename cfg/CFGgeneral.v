Require Export CFGdef CFGTac.

Lemma all_sat_restrict_edge'
      (L : Type)
      (f : L -> L -> bool)
      (p q : L)
      (π : list L)
      (Hπ : Path f p q π)
      (P : decPred L)
      (Hsat :  forall x : L, x ∈ π -> P x)
  : Path (restrict_edge' f P) p q π.
Proof.
  induction Hπ.
  - econstructor.
  - econstructor.
    + eapply IHHπ. intros; eapply Hsat. cbn. firstorder.
    + unfold_edge_op; split_conj; eauto; eapply Hsat; cbn; auto.
      right. eapply path_contains_front;eauto.
Qed.

Lemma loop_contains'_basic `{redCFG} h p
  : loop_contains' edge a_edge h p = loop_contains h p.
Proof.
  reflexivity.
Qed.  
