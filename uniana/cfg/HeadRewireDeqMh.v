Require Export HeadRewire.

Section cfg.
  Context `(C : redCFG).

  Infix "-h>" := (head_rewired_edge) (at level 70).


  Definition loop_contains_strict h p
    := loop_contains h p /\ h <> p.

  Definition deq_loop_mh q p
    := forall h, h <> p -> loop_contains h p -> loop_contains h q.

  Definition eq_loop_mh q p
    := deq_loop_mh q p /\ deq_loop_mh p q.

  Lemma eq_loop_mh_sym : Symmetric eq_loop_mh.
  Proof.
    firstorder.
  Qed.

  Instance deq_loop_mh_refl : Reflexive deq_loop_mh.
  Proof.
    unfold Reflexive. intros x h Hloop Hneq.
    auto.
  Qed.

  Lemma deq_loop_deq_loop_mh p q
        (Hdeq : deq_loop p q)
    : deq_loop_mh p q.
  Proof.
    intros h Hloop Hneq.
    eauto.
  Qed.

  Lemma deq_loop_mh_deq_loop p q
        (Hnh : ~ loop_head q)
        (Hdeq : deq_loop_mh p q)
    : deq_loop p q.
  Proof.
    intros h Hloop.
    eapply Hdeq.
    - contradict Hnh. subst h. eapply loop_contains_loop_head;eauto.
    - assumption.
  Qed.

  Lemma head_rewired_deq_loop_mh p q
        (Hedge : p -h> q)
    : deq_loop_mh p q.
  Proof.
    destruct Hedge.
    - destructH. destruct (edge_Edge H0);intros h Hloop Hneq.
      + eapply basic_edge_eq_loop in b.
        rewrite b. auto.
      + eapply back_edge_eq_loop in b. rewrite b. assumption.
      + eapply deq_loop_entry_or in e;eauto.
        destruct e;[assumption|contradiction].
      + destruct e. eapply deq_loop_exited;eauto.
    - destruct H. intros h Hloop Hneq.
      eapply deq_loop_exited';eauto.
  Qed.

  Lemma hpath_deq_loop_mh p q π
        (Hpath : HPath p q π)
    : deq_loop_mh p q.
  Proof.
    induction Hpath.
    - reflexivity.
    - eapply head_rewired_deq_loop_mh in H as Hmh.
      intros h Hneq Hloop.
      eapply IHHpath;eauto.
      contradict Hloop.
      subst h. eapply head_rewired_not_contains;eauto.
  Qed.

  Lemma hpath_deq_loop_mh_elem p q π x
        (Hpath : HPath p q π)
        (Hin : x ∈ π)
    : deq_loop_mh x q.
  Proof.
    eapply path_from_elem in Hpath;eauto.
    destructH.
    eapply hpath_deq_loop_mh;eauto.
  Qed.
End cfg.
