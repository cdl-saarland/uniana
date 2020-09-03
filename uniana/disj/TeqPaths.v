Require Export DiamondPaths.

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

End teq.

Hint Resolve teq_r1_incl_head_q teq_r2_incl_head_q teq_u1_deq_q teq_u2_deq_q Tloop : teq.
