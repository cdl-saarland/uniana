Require Export TcfgLoop.
Require Import Lia.

Section cfg.

  Context `(C : redCFG).

  Lemma tag_depth_unroot p q i j t
        (Hpath : TPath (q,j) (p,i) t)
        (Hlen : |j| = depth q)
    : |i| = depth p.
  Admitted.

  Lemma take_r_leq_cons (A : Type) (a : A) l n
        (Hlen : n <= |l|)
    : take_r n (a :: l) = take_r n l.
  Admitted.
  Lemma take_r_leq_cons2 (A : Type) (a b : A) l n
        (Hlen : n <= |l|)
    : take_r n (a :: l) = take_r n (b :: l).
  Admitted.

  Lemma tagle_take_r i j n
        (Htagle : i ⊴ j)
    : take_r n i ⊴ take_r n j.
  Admitted.

  Lemma weak_tpath_tag_take_r_eq p i q j t h n
        (Hlen : |j| = depth q)
        (Hpath : TPath (q,j) (p,i) t)
        (Hincl : forall r, r ∈ map fst t -> deq_loop r h)
        (Hdep : depth h = n)
    : take_r (n-1) j = take_r (n-1) i.
  Proof.
    revert p i Hpath.
    induction t;intros; inv_path Hpath.
    - reflexivity.
    - case (depth h) eqn:E.
      { cbn. reflexivity. }
      exploit' IHt.
      { intros. eapply Hincl. right. auto. }
      destruct x.
      copy Hincl Hincl'.
      eapply deq_loop_depth in Hincl.
      2: { right. eapply path_contains_front in H. eapply in_map with (f:=fst) in H. cbn in H;eauto. }
      eapply tcfg_edge_destruct' in H0.
      eapply tag_depth_unroot in H as Htagt0;eauto.
      destruct H0 as [[H0 Q0]|[[H0 Q0]|[[H0 Q0]|[H0 Q0]]]].
      + subst. eapply IHt;eauto.
      + subst.
        eapply depth_entry in Q0.
        rewrite take_r_leq_cons.
        * eapply IHt;eauto.
        * rewrite Htagt0. lia.
      + destruct t0.
        { cbn in Htagt0. lia. }
        cbn in H0. subst i.
        erewrite take_r_leq_cons2.
        * eapply IHt;eauto.
        * cbn in Htagt0. clear - E Hincl Htagt0. rewrite E in Hincl. rewrite <-Htagt0 in Hincl. lia.
      + destruct t0. 1:cbn in Htagt0;lia.
        cbn in H0. subst.
        setoid_rewrite <-take_r_leq_cons at 2.
        * eapply IHt;eauto.
        * cbn in Htagt0. lia.
  Qed.

  Lemma weak_monotonicity q j p i t h n
        (Hlen : |j| = depth q)
        (Hpath : TPath (q,j) (p,i) t)
        (Hincl : forall r, r ∈ map fst t -> deq_loop r h)
        (Hdep : depth h = n)
    : take_r n j ⊴ take_r n i.
  Proof.
    revert p i Hpath.
    induction t;intros; inv_path Hpath.
    - reflexivity.
    - case (depth h) eqn:E.
      { cbn. reflexivity. }
      exploit' IHt.
      { intros. eapply Hincl. right. auto. }
      destruct x.
      copy Hincl Hincl'.
      eapply deq_loop_depth in Hincl.
      2: { right. eapply path_contains_front in H. eapply in_map with (f:=fst) in H. cbn in H;eauto. }
      eapply tcfg_edge_destruct' in H0.
      eapply tag_depth_unroot in H as Htagt0;eauto.
      destruct H0 as [[H0 Q0]|[[H0 Q0]|[[H0 Q0]|[H0 Q0]]]].
      + subst. eapply IHt;eauto.
      + subst.
        eapply depth_entry in Q0.
        setoid_rewrite take_r_leq_cons.
        * eapply IHt;eauto.
        * rewrite Htagt0. lia.
      + destruct t0.
        { cbn in Htagt0. lia. }
        rewrite H0.
        transitivity (take_r (S n) (n0 :: t0)).
        * eapply IHt;eauto.
        * unfold STag.
          eapply tagle_take_r.
          econstructor.
          econstructor.
          lia.
      + specialize (Hincl' p). exploit Hincl'. 1: left;cbn;eauto.
        destruct t0. 1:cbn in Htagt0;lia.
        cbn in H0. subst.
        setoid_rewrite <-take_r_leq_cons at 2.
        * eapply IHt;eauto.
        * cbn in Htagt0.
          eapply depth_exit in Q0.
          eapply deq_loop_depth in Hincl'.
          rewrite Q0 in Htagt0. lia.
  Qed.

  Lemma non_entry_head_back_edge p h
        (Hedge : edge__P p h)
        (Hloop : loop_contains h p)
    : p ↪ h.
  Admitted.

  Lemma tcfg_fresh p i t
        (Hpath : TPath (p,i) (p,i) t)
        (Hdep : | i | = depth p)
        (Hlen : | t | >= 2)
    : False.
  Proof.
    eapply TPath_CPath in Hpath as Hpp.
    eapply p_p_ex_head in Hpp.
    2: rewrite map_length;eauto.
    destructH.
    destruct t. 1: inv Hpath.
    eapply in_fst in Hpp0. destruct Hpp0 as [k Hpp0].
    unfold TPath in *. path_simpl' Hpath.
    eapply path_to_elem in Hpp0 as Hπ;eauto.
    destruct Hπ as [π [Hπ Hπpre]].
    inv_path Hπ.
    1: {
      inv_path Hpath.
      - cbn in Hlen. lia.
      - destruct x.
        copy H0 H0'.
        destruct H0' as [H0' _].
        eapply non_entry_head_back_edge in H0'.
        2: { eapply Hpp1. eapply path_contains_front in H. cbn. right.
             eapply in_map with (f:=fst) in H. eapply H. }
        eapply tag_back_edge_iff in H0';eauto.
        admit. admit.
    }
    destruct x.
    eapply path_from_elem in Hpp0 as Hϕ;eauto.
    destruct Hϕ as [ϕ [Hϕ Hϕsuff]].
    eapply weak_monotonicity in Hϕ;eauto.
    3: {
      intros. eapply loop_contains_deq_loop. eapply Hpp1. eapply postfix_incl;eauto.
         Lemma prefix_map_fst (A B : Type) (l l' : list (A * B))
               (Hpre: Prefix l l')
           : Prefix (map fst l) (map fst l').
         Admitted.
         Lemma postfix_map_fst (A B : Type) (l l' : list (A * B))
               (Hpre: Postfix l l')
           : Postfix (map fst l) (map fst l').
         Admitted.
      eapply postfix_map_fst in Hϕsuff. assumption.
    }
    2: { eapply tag_depth_unroot in Hdep;eauto. }
    eapply weak_monotonicity in H;eauto.
    2: { intros. eapply loop_contains_deq_loop. eapply Hpp1. eapply prefix_incl;eauto.
         eapply prefix_map_fst;eauto. eapply prefix_cons;eauto.
    }
    enough (take_r (depth h) t0 ◁ take_r (depth h) k) as Q.

  Admitted.

  Lemma tpath_tag_take_r_eq p i q j t h n
        (Hpath : TPath (q,j) (p,i) t)
        (Hdeqq : deq_loop q h)
        (Hdeqp : deq_loop p h)
        (Hdep : depth h = n)
    : take_r (n-1) j = take_r (n-1) i.
  Admitted.

  Lemma monotonicity q j p i t h n
        (Hpath : TPath (q,j) (p,i) t)
        (Hdeqq : deq_loop q h)
        (Hdeqp : deq_loop p h)
        (Hdep : depth h = n)
    : take n j ⊴ take n i.
  Admitted.

End cfg.
