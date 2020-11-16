Require Import LastCommonTac DecTac Lia.

Section Lc.

  Variable A : Type.

  Lemma rcons_eq (a a' : A) l l' :
    a = a' /\ l = l' <-> l :r: a = l' :r: a'.
  Proof.
    split.
    - destruct (rcons_destruct l); intros; destruct H0; subst; reflexivity.
    - intros. revert dependent l'.
      induction l; induction l'; intros Heq; inversion Heq.
      + split; reflexivity.
      + congruence'.
      + congruence'.
      + specialize (IHl l' H1) as [aeq leq].
        split; subst; reflexivity.
  Qed.

  Lemma postfix_first_occ_eq `{EqDec A eq} (l1 l2 l3 : list A) (a : A) :
    ~ In a l1 -> ~ In a l2 -> Postfix (l1 :r: a) l3 -> Postfix (l2 :r: a) l3
    -> l1 = l2.
  Proof.
    intros in1 in2. intros.
    assert (Postfix l1 (l2 :r: a)) as po1.
    {
      eapply postfix_order; eauto.
      - eapply postfix_step_left; eauto.
    }
    assert (Postfix l2 (l1 :r: a)) as po2.
    {
      eapply postfix_order; eauto.
      - eapply postfix_step_left; eauto.
    }
    revert dependent l2.
    revert dependent l3.
    induction l1; intros l3 post1 l2 in2 post2 po1 po2.
    - cbn in post1.
      apply postfix_incl in po2. clear - in2 po2.
      destruct l2; eauto. specialize (po2 a0).
      assert (In a0 (a :: nil)) as po' by (apply po2; econstructor; eauto).
      inversion po'.
      + subst a. exfalso. apply in2. econstructor; eauto.
      + inversion H.
    - destruct l2.
      + cbn in post2.
        apply postfix_incl in po1. clear - in1 po1.
        specialize (po1 a0).
        assert (In a0 (a :: nil)) as po' by (apply po1; econstructor; eauto).
        inversion po'.
        * subst a. exfalso. apply in1. econstructor; eauto.
        * inversion H.
      + rewrite cons_rcons_assoc in post1, post2.
        eapply postfix_hd_eq in po1 as hd_eq1. subst a0.
        assert (exists l3', l3 = a1 :: l3') as [l3' leq3].
        {
          destruct l3.
          - cbn in post2. eapply postfix_nil_nil in post2. cbn in post2. congruence.
          - exists l3. apply postfix_hd_eq in post1. subst a1. reflexivity.
        }
        subst l3.
        erewrite IHl1 with (l2:=l2); eauto.
        (* contradict in1. right. eauto.*)
        * eapply cons_postfix; eauto.
        (* contradict in2. right. eauto.*)
        * eapply cons_postfix; eauto.
        * rewrite cons_rcons_assoc in po1. eapply cons_postfix; eauto.
        * rewrite cons_rcons_assoc in po1. eapply cons_postfix; eauto.
  Qed.


  Definition last_common `{EqDec A eq} (l1 l2 : list A) (s : A) :=
    exists l1' l2', Postfix (l1' :r: s) l1 /\ Postfix (l2' :r: s) l2
               /\ Disjoint l1' l2'
               /\ ~ In s l1' /\ ~ In s l2'.


  Definition last_common' `{EqDec A eq} (l1 l2 l1' l2' : list A) (s : A)
    := Postfix (l1' :r: s) l1 /\ Postfix (l2' :r: s) l2 /\ Disjoint l1' l2' /\ s ∉ l1' /\ s ∉ l2'.

  Lemma last_common'_iff `(EqDec A eq) l1 l2 (a : A)
    : last_common l1 l2 a <-> exists l1' l2', last_common' l1 l2 l1' l2' a.
  Proof.
    unfold last_common, last_common' in *. firstorder.
  Qed.

  Lemma last_common'_sym `{EqDec A eq} (l1 l2 l1' l2' : list A) (a : A)
        (Hlc : last_common' l1' l2' l1 l2 a)
    : last_common' l2' l1' l2 l1 a.
  Proof.
    unfold last_common' in *. destructH.
    split_conj;eauto.
    eapply Disjoint_sym. auto.
  Qed.

  Require Import ListOrder.


  Lemma ne_last_common `{EqDec A eq} (l1 l2 : list A) (a : A) :
    exists s, last_common (l1 ++ [a]) (l2 ++ [a]) s.
  Proof.
    unfold last_common.


(*    revert l2.
    induction l1; intros l2.
    - admit.
    - specialize (IHl1 l2). destructH.
      exists s, (a0 :: l1'), l2'. split_conj;eauto.
      + cbn. eapply postfix_cons. eauto.
      + admit. (* nope *)
      + *)


    revert l2.
    induction l1; intros l2; induction l2; cbn in *.
    - exists a; exists nil; exists nil; cbn.
      prove_last_common.
    - exists a. exists nil.
      destruct IHl2 as [s [l1' [l2' [post [post' [disj [in1 in2]]]]]]]. cbn.
      destruct (a == a0).
      + destruct e. exists nil. prove_last_common.
      + exists (a0 :: l2'). prove_last_common.
    - exists a. specialize (IHl1 nil).
      destruct IHl1 as [s [l1' [l2' [post [post' [disj [in1 in2]]]]]]].
      destruct (a == a0).
      + destruct e. exists nil, nil. cbn. prove_last_common.
      + exists ((a0 :: l1')), nil. cbn in post'. prove_last_common.
    - specialize (IHl1 (a1 :: l2)).
      rename a1 into a2. rename a0 into a1.

      destruct IHl1 as [s1 [l11 [l12 [post11 [post12 [disj1 [in11 in12]]]]]]].
      destruct IHl2 as [s2 [l21 [l22 [post21 [post22 [disj2 [in21 in22]]]]]]].

      destruct (s1 == a2).
      + destruct e. exists s1. destruct (a1 == s1).
        * destruct e. exists nil. exists nil. prove_last_common.
        * exists ((a1 :: l11)). exists nil. prove_last_common.
      + destruct (s2 == a1).
        * destruct e. exists s2, nil. destruct (s2 == a2).
          -- destruct e. exists nil. prove_last_common.
          -- exists ((a2 :: l22)). prove_last_common.
        * destruct (a1 == a2).
          -- destruct e. exists a1, nil, nil. prove_last_common.
          -- (*destruct l12 as [|b l12].
             { cbn in post12. eapply postfix_hd_eq in post12. subst. exfalso. apply c. reflexivity. }
             replace b with a2 in *.  2: (cbn in post12; symmetry; eapply postfix_hd_eq;eauto).
             clear b.
             destruct l21 as [|b l21].
             { cbn in post21. eapply postfix_hd_eq in post21. subst. exfalso. apply c0. reflexivity. }
             replace b with a1 in *. 2: cbn in post21;symmetry; eapply postfix_hd_eq;eauto. clear b.*)
             destruct (In_dec _ s1 l22).
             ++ exists s1, (a1 :: l11), l12. split_conj.
                ** prove_last_common.
                ** prove_last_common.
                ** apply disjoint_cons1. split; auto.

                   assert (Postfix l12 (a2 :: l22)).
                   {
                     eapply postfix_order with (a0:=s1); eauto.
                     (*- econstructor 2; eauto.*)
                     - eapply postfix_step_left; eauto.
                     - cbn. apply postfix_cons. eapply postfix_step_left; eauto.
                   }
                   apply postfix_incl in H1. apply id in disj2 as disj2'.
                   unfold Disjoint in disj2'.
                   unfold incl in H1. intro In12. apply H1 in In12. cbn in In12.
                   destruct In12 as [In12|In12]; [subst a1; apply c1; reflexivity|].
                   clear disj2.
                   assert (a1 ∉ l21) as disj2.
                   { intro N. eapply disj2'. eauto. eapply In12. }
                   apply disj2. apply postfix_elem in post21; eauto.
                   --- eapply In_rcons in post21.
                       destruct post21; [subst a1; exfalso; apply c0; reflexivity|assumption].
                   --- destruct l21; cbn. lia. rewrite app_length. lia.
                ** assert (s1 =/= a1) as sa.
                   {
                     intro N. destruct N. apply postfix_elem in post21.
                     apply In_rcons in post21.
                     - destruct post21; [subst s1; apply c0; reflexivity|].
                       clear - disj2 H0 H1. firstorder.
                     - destruct l21; cbn. lia. rewrite app_length. lia.
                   }
                   prove_last_common.
                ** assumption.
             ++ destruct (s1 == s2) as [seq|sneq].
                {
(*                  destruct l12 as [|b l12].
                  { cbn in post12. eapply postfix_hd_eq in post12. subst.
                    exfalso. apply c. reflexivity. }
                  replace b with a2 in *.  2: (cbn in post12; symmetry; eapply postfix_hd_eq;eauto).
                  clear b.
                  destruct l21 as [|b l21].
                  { cbn in post21. eapply postfix_hd_eq in post21. subst.
                    exfalso. apply c0. reflexivity. }
                  replace b with a1 in *. 2: cbn in post21;symmetry; eapply postfix_hd_eq;eauto.
                  clear b.*)
                  destruct seq.
                  assert (l21 = a1 :: l11 /\ l12 = a2 :: l22) as [lleq1 lleq2].
                  {
                    split.
                    - eapply postfix_first_occ_eq; eauto.
                      + contradict in11. inversion in11.
                        * subst a1; exfalso; apply c0; reflexivity.
                        * eauto.
                      + rewrite cons_rcons_assoc. apply postfix_cons. eauto.
                    - eapply postfix_first_occ_eq; eauto.
                      + contradict in22. inversion in22.
                        * subst a2; exfalso; apply c; reflexivity.
                        * eauto.
                      + rewrite cons_rcons_assoc. apply postfix_cons. eauto.
                  }
                  subst l12 l21.
                  exists s1, (a1 :: l11), (a2 :: l22).
                  split_conj.
                  - prove_last_common.
                  - prove_last_common.
                  - eapply disjoint_cons1. split; eauto.
                    eapply disjoint1 in disj2.
                    destruct (disj2) as [disj2' _].
                    cbn in disj2'. specialize (disj2' _ (or_introl eq_refl)).
                    contradict disj2'. cbn in disj2'.
                    destruct disj2'; [subst a2; exfalso; apply c1; reflexivity|eauto].
                  - eauto.
                  - eauto.
                }
                destruct (In_dec _ a2 (l21 :r: s2)) as [in_a0|nin_a0].
                {
                  exists a2, (postfix_nincl a2 l21), nil.
                  split_conj.
                  - apply In_rcons in in_a0. destruct in_a0.
                    + subst a2.
                      apply postfix_nincl_invariant in in21. rewrite in21. eauto.
                    + eapply postfix_nincl_spec in H1.
                      eapply postfix_trans; eauto. eapply postfix_step_left; eauto.
                  - prove_last_common.
                  - prove_last_common.
                  - apply postfix_nincl_nincl.
                  - tauto.
                }
                exists s2, l21, (a2 :: l22).
                split_conj.
                ** prove_last_common.
                ** prove_last_common.
                ** apply disjoint_cons2. split; eauto.
                ** assumption.
                ** assert (s2 =/= a2) as sa.
                   {
                     intro N. destruct N. apply nin_a0.
                     apply In_rcons. left. reflexivity.
                   }
                   prove_last_common.
  Qed.

  Lemma last_common_sym `{EqDec A eq} (l l' : list A) a
        (Hlc : last_common l l' a)
    : last_common l' l a.
  Proof.
    unfold last_common in *; firstorder.
  Qed.

  Lemma last_common_singleton1 `{EqDec A eq} (s a : A) l
        (Hlc : last_common (a :: nil) l s)
    : a = s.
  Proof.
    unfold last_common in Hlc. destructH. eapply postfix_rcons_nil_eq in Hlc0. firstorder.
  Qed.

  Lemma last_common_singleton2 `{EqDec A eq} (s a : A) l
        (Hlc : last_common l (a :: nil) s)
    : a = s.
  Proof.
    unfold last_common in Hlc. destructH. eapply postfix_rcons_nil_eq in Hlc2. firstorder.
  Qed.

End Lc.
