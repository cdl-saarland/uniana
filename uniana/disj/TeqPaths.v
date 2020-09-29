Require Export DiamondIncl.

Section teq.
  Context `(T : TeqPaths).

  Lemma teq_no_back : forall x : Lab, x ∈ (q1 :: map fst r1) -> ~ loop_contains x q1.
  Admitted.

  Lemma teq_no_back2
        (Htageq : j1 = j2)
    : forall x : Lab, x ∈ (q2 :: map fst r2) -> ~ loop_contains x q1.
  Admitted.

  Lemma teq_r1_incl_head_q : forall x, x ∈ (q1 :: map fst r1) -> deq_loop x q1.
  Admitted.

  Lemma teq_r2_incl_head_q : forall x, x ∈ (q2 :: map fst r2) -> deq_loop x q1.
  Admitted.

  Lemma teq_u1_deq_q
    : deq_loop u1 q1.
  Proof.
  Admitted.

  Lemma teq_u2_deq_q
    : deq_loop u2 q1.
  Admitted.

  Lemma q1_neq_q2
        (Hjeq : j1 = j2)
    : q1 <> q2.
  Proof.
    destruct T. subst j2.
    intro HEq.
    eapply Tdisj;left;eauto.
    f_equal. symmetry;eauto.
  Qed.

  Lemma q1_no_head
        (Hjeq : j1 = j2)
    : ~ loop_head q1.
  Proof.
  Admitted.

  Lemma jj_tagle
    : j1 ⊴ j2.
  Proof.
  Admitted.

  Lemma u1_exit_eq_q h p
        (Hexit : exit_edge h p u1)
    : eq_loop u1 q1.
  Proof.
  Admitted.

  Lemma u2_exit_eq_q h p
        (Hexit : exit_edge h p u2)
    : eq_loop u2 q1.
  Proof.
  Admitted.

  Lemma teq_node_disj
        (Hjeq : j1 = j2)
    : Disjoint (q1 :: map fst r1) (q2 :: map fst r2).
  Admitted.

End teq.

Lemma TeqPaths_sym `(C : redCFG) u1 u2 q1 q2 l1 l2 j r1 r2
      (T : TeqPaths u1 u2 q1 q2 l1 l2 j j r1 r2)
  : TeqPaths u2 u1 q2 q1 l2 l1 j j r2 r1.
Proof.
  copy T T'.
  destruct T.
  econstructor;eauto.
  - eapply Disjoint_sym;eauto.
  - symmetry. eauto.
  - destruct Tlj_eq2;[firstorder|].
    destruct H;[right;auto|].
    exfalso. eapply teq_no_back2 in T';eauto.
    eapply TPath_CPath in Tpath2. cbn in Tpath2. eapply path_contains_back;eauto.
  - destruct Tlj_eq1;[left|right];firstorder.
  - rewrite <-Tloop. eauto.
Qed.

Hint Resolve teq_r1_incl_head_q teq_r2_incl_head_q teq_u1_deq_q teq_u2_deq_q Tloop : teq.
