Require Export ListExtra DecTac.


Lemma first_diff' (A : Type) `{EqDec A eq} (l1 l2 : list A)
      (Hneq : l1 <> l2)
      (Hlen : length l1 = length l2)
      (Hnnil1 : l1 <> nil)
      (Hnnil2 : l2 <> nil)
  : exists a1 a2 l' l1' l2', a1 <> a2 /\ l1 = l' ++ a1 :: l1' /\ l2 = l' ++ a2 :: l2'.
Proof.
  assert (forall (l : list A), l <> nil -> length l > 0) as Hlengt.
  { clear. intros. destruct l;cbn;[congruence|omega]. }
  eapply Hlengt in Hnnil1; eapply Hlengt in Hnnil2. clear Hlengt.
  revert dependent l2. induction l1; intros; destruct l2; cbn in *.
  1: congruence. 1-2: omega.
  destruct l1,l2; cbn in *; only 2,3: congruence.
  - exists a, a0, nil, nil, nil. split_conj; cbn; eauto. contradict Hneq. subst; eauto.
  - decide' (a == a0).
    + exploit' IHl1;[omega|]. specialize (IHl1 (a2 :: l2)). exploit IHl1.
      * contradict Hneq. f_equal;eauto.
      * cbn; omega.
      * destructH. exists a0, a3, (a :: l'), l1', l2'. split_conj; eauto.
        1,2: cbn; f_equal; eauto.
    + exists a, a0, nil, (a1 :: l1), (a2 :: l2). split_conj; eauto.
Qed.

Lemma first_diff (* unused *) (A : Type) `{EqDec A eq} (l1 l2 : list A)
      (Hneq : l1 <> l2)
      (Hlen : length l1 = length l2)
      (Hnnil1 : l1 <> nil)
      (Hnnil2 : l2 <> nil)
  : exists a1 a2 l' l1' l2', a1 <> a2 /\ l1 = l1' ++ a1 :: l' /\ l2 = l2' ++ a2 :: l'.
Proof.
  specialize (@first_diff' _ _ _ (rev l1) (rev l2)) as Hfi.
  exploit Hfi; cycle -1.
  - destructH.
    rewrite <-rev_involutive in Hfi2. eapply rev_injective in Hfi2.
    rewrite rev_app_distr in Hfi2. rewrite rev_cons in Hfi2.
    rewrite <-rev_involutive in Hfi3. eapply rev_injective in Hfi3.
    rewrite rev_app_distr in Hfi3. rewrite rev_cons in Hfi3.
    exists a1, a2, (rev l'), (rev l1'), (rev l2').
    unfold rcons in Hfi2,Hfi3.
    rewrite <-app_assoc in Hfi2,Hfi3. cbn in *. firstorder.
  - contradict Hneq. eapply rev_injective; eauto.
  - rewrite !rev_length; eauto.
  - contradict Hnnil1. destruct l1;cbn in *;[auto|congruence'].
  - contradict Hnnil2. destruct l2;cbn in *;[auto|congruence'].
Qed.
