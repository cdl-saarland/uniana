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

  Lemma head_rewired_not_contains p q
        (Hedge : head_rewired_edge p q)
    : ~ loop_contains p q.
  Proof.
    destruct Hedge.
    - destructH. contradict H1. eapply loop_contains_loop_head;eauto.
    - destruct H. destruct H. destructH. assumption.
  Qed.

  Lemma head_rewired_no_self p
        (Hedge : head_rewired_edge p p)
    : False.
  Proof.
    destruct Hedge.
    - destruct H. eapply no_self_loops;eauto.
    - destruct H. destruct H. destruct H0. eauto using loop_contains_self, loop_contains_loop_head.
  Qed.

  Lemma head_rewired_head_no_entry h p t
        (Hloop : loop_contains h p)
        (Hpath : HPath h p t)
    : h = p.
  Proof.
    revert p Hpath Hloop.
    induction t;intros;inv_path Hpath.
    - reflexivity.
    - decide (loop_contains h x).
      + exfalso.
        eapply IHt in H;subst;eauto.
        eapply head_rewired_not_contains;eauto.
      + destruct H0.
        * destruct H0. eapply entry_through_header in n;eauto.
        * destruct H0. eapply deq_loop_exited' in H0. eapply H0 in Hloop. contradiction.
  Qed.

  Lemma head_rewired_entry_eq h p q t
        (Hpath : HPath q p t)
        (Hnin : ~ loop_contains h q)
        (Hin : loop_contains h p)
    : h = p.
  Proof.
    revert p Hin Hpath.
    induction t;intros;inv_path Hpath.
    - exfalso. contradiction.
    - decide (loop_contains h x).
      + exfalso.
        eapply IHt in H;subst;eauto.
        eapply head_rewired_not_contains;eauto.
      + destruct H0.
        * destruct H0. eapply entry_through_header in n;eauto.
        * destruct H0. eapply deq_loop_exited' in H0. eapply H0 in Hin. contradiction.
  Qed.

  Lemma acyclic_head_rewired_edge
    : acyclic head_rewired_edge.
  Proof.
    eapply acyclic_path_path;eauto.
    2: { intros. intro. subst. eapply head_rewired_no_self;eauto. }
    intros p q π. revert p q. induction π;intros p q ϕ Hneq Hπ Hϕ;inv_path Hπ.
    - contradiction.
    - decide (p = x).
      + subst x.
        eapply IHπ in H.
(*
    unfold acyclic. intros.
    revert p q H H0. induction π;intros p q Hedge Hpath;inv_path Hpath.
    - destruct Hedge.
      + destruct H. eapply no_self_loops;eauto.
      + destruct H. destruct H. destruct H0. eapply H0.
        eauto using loop_contains_self,loop_contains_loop_head.
    - *)
  Admitted.

  Lemma acyclic_HPath p q π
        (Hpath : HPath p q π)
    : NoDup π.
  Proof.
    eapply acyclic_NoDup; eauto using acyclic_head_rewired_edge.
  Qed.

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
