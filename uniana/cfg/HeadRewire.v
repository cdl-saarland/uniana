Require Export CFGinnermost CFGgeneral.

Section hr_cfg.
  Context `{C : redCFG}.

  Definition head_rewired_edge q p : Prop
    := edge__P q p /\ ~ loop_head q \/ exited q p.

  Lemma subgraph_refl {L : Type} [edge1 : L -> L -> Prop]
    : sub_graph edge1 edge1.
  Proof.
    unfold sub_graph. intros. tauto.
  Qed.

  (* the head rewired DAG is not a redCFG (because of unreachability) *)

  Definition HPath := Path head_rewired_edge.

  Lemma acyclic_head_rewired_edge
    : acyclic head_rewired_edge.
  Admitted.

  Lemma acyclic_HPath p q π
        (Hpath : HPath p q π)
    : NoDup π.
  Proof.
    eapply acyclic_NoDup; eauto using acyclic_head_rewired_edge.
  Qed.

  Lemma head_rewired_head_no_entry h p t
        (Hloop : loop_contains h p)
        (Hpath : HPath h p t)
    : h = p.
  Admitted.
  Lemma head_rewired_entry_eq h p q t
        (Hpath : HPath q p t)
        (Hnin : ~ loop_contains h q)
        (Hin : loop_contains h p)
    : h = p.
  Proof.

  Admitted.
  Lemma head_rewired_final_exit e p t q h
        (Hpath : HPath e p t)
        (Hexit : exit_edge h q e)
        (Hloop : loop_contains h p)
    : False.
  Proof.
    eapply head_rewired_entry_eq in Hloop;eauto.
    2: destruct Hexit as [? [Hexit _]];eauto.
    subst p.
    specialize (path_rcons) with (r:=h) as Hpath'.
    specialize Hpath' with (edge:=head_rewired_edge).
    eapply Hpath' in Hpath as Hpath''.
    - eapply acyclic_HPath in Hpath'' as Hnd.
      eapply NoDup_nin_rcons;eauto.
      destruct t;[inv Hpath|].
      cbn in Hpath''. path_simpl' Hpath''. left. reflexivity.
    - right. eexists;eauto.
  Qed.
  Lemma head_rewired_final_exit_elem e p t q h x
        (Hpath : HPath e p t)
        (Hexit : exit_edge h q e)
        (Hin : x ∈ t)
        (Hloop : loop_contains h x)
    : False.
  Proof.
    eapply path_to_elem in Hpath;eauto. destructH.
    eapply head_rewired_final_exit;eauto.
  Qed.

End hr_cfg.
