Require Export TcfgReach PPexhead.
Require Import Lia.

Section cfg.

  Context `(C : redCFG).

  (* the more general formulation with deq_loop is wrong *)
  Lemma tpath_tag_take_r_eq p i q j t h n
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
        rewrite take_r_cons_drop.
        * eapply IHt;eauto.
        * rewrite Htagt0. lia.
      + destruct t0.
        { cbn in Htagt0. lia. }
        cbn in H0. subst i.
        erewrite take_r_cons_replace.
        * eapply IHt;eauto.
        * cbn in Htagt0. clear - E Hincl Htagt0. rewrite E in Hincl. rewrite <-Htagt0 in Hincl. lia.
      + destruct t0. 1:cbn in Htagt0;lia.
        cbn in H0. subst.
        setoid_rewrite <-take_r_cons_drop at 2.
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
        setoid_rewrite take_r_cons_drop.
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
        setoid_rewrite <-take_r_cons_drop at 2.
        * eapply IHt;eauto.
        * cbn in Htagt0.
          eapply depth_exit in Q0.
          eapply deq_loop_depth in Hincl'.
          rewrite Q0 in Htagt0. lia.
  Qed.

  Lemma tcfg_fresh p i j t
        (Hpath : TPath (p,i) (p,j) t)
        (Hdep : | i | = depth p)
        (Hlen : | t | >= 2)
    : i ◁ j.
  Proof.
    eapply TPath_CPath in Hpath as Hpp.
    eapply p_p_ex_head in Hpp.
    2: rewrite map_length;eauto.
    destructH.
    destruct t. 1: inv Hpath.
    eapply in_fst in Hpp0. destruct Hpp0 as [k Hpp0].
    unfold TPath in *. path_simpl' Hpath.
    eapply path_from_elem' in Hpp0 as Hπ;eauto.
    destructH.
    eapply postfix_eq in Hπ1.
    destruct Hπ1 as [ϕ Hπ1].
    rewrite <-app_assoc in Hπ1.
    unfold app at 2 in Hπ1.
    assert (Prefix ((h,k) :: ϕ) ((p,j) :: t)) as Hpreϕ.
    { eapply prefix_eq. eexists;eauto. }
    eapply path_prefix_path in Hpath as Hϕ;eauto.
    inv_path Hϕ.
    {
      cbn in Hπ1.
      destruct equiv_dec in Hπ1.
      - cbn in Hπ1.
        destruct t;[|congruence]. cbn in Hlen. lia.
      - eapply tagle_neq_taglt.
        + erewrite <-take_r_geq with (n:=depth h).
          2: { erewrite tag_depth_unroot;eauto. }
          rewrite <-take_r_geq with (n:=depth h) at 1.
          2: { erewrite tag_depth_unroot;eauto. }
          eapply weak_monotonicity in Hpath. all:eauto.
          eauto using loop_contains_deq_loop.
        + contradict c0. intro. subst. apply H. reflexivity.
    }
    destruct x.
    assert (e ↪ h) as Hback.
    { eapply non_entry_head_back_edge. 1: destruct H0;eauto.
      eapply Hpp1. fold (fst (e,t0)). eapply in_map. eapply prefix_incl;eauto.
      right. eapply path_contains_front;eauto.
    }
    eapply weak_monotonicity in H;eauto.
    2: { intros. eapply loop_contains_deq_loop. eapply Hpp1. eapply prefix_incl;eauto.
         eapply prefix_map_fst;eauto. eapply prefix_cons;eauto.
    }
    eapply weak_monotonicity in Hπ0;eauto.
    3: {
      intros. eapply loop_contains_deq_loop. eapply Hpp1. eapply postfix_incl;eauto.
      eapply postfix_map_fst.
      eapply postfix_nincl_spec;eauto.
    }
    2: { eapply tag_depth_unroot in Hdep;eauto. }
    assert (| k | = depth h) as Hhdep.
    { eapply tag_depth_unroot;eauto. }
    destruct t0.
    { eapply back_edge_eq_loop in Hback. eapply tcfg_edge_depth_iff in Hhdep;eauto.
      rewrite Hback  in Hhdep. cbn in Hhdep.
      enough (0 > 0) by lia.
      rewrite Hhdep at 1. eapply depth_loop_head.
      eapply loop_contains_loop_head. eapply Hpp1. fold (fst (h,k)). eapply in_map. eauto.
    }
    eapply tag_back_edge_iff in Hback;eauto.
    specialize (taglt_stag n t0) as Hlt. subst k.
    rewrite take_r_geq in Hπ0. 2: setoid_rewrite Hhdep; lia.
    setoid_rewrite take_r_geq in H at 2. 2: setoid_rewrite Hhdep; lia.
    eapply tagle_taglt_trans in Hlt;eauto.
    eapply taglt_tagle_trans in Hlt;eauto.
    eapply taglt_take_r_taglt;eauto.
    rewrite Hdep.
    erewrite tag_depth_unroot;eauto.
  Qed.

  Lemma ex_entry (h p q : Lab) (i j j' k : Tag) t
        (Hin : loop_contains h q)
        (Hnin : ~ loop_contains h p)
        (Hpath : TPath (p,i) (q,j) t)
        (Hleni : | i | = depth p)
        (Heq : j = j' ++ k)
        (Hlen : | k | = depth h - 1)
    : (h,0 :: k) ∈ t.
  Proof.
    revert j' j q Heq Hpath Hin.
    induction t;intros;inv_path Hpath.
    - contradiction.
    - destruct x as [u l].
      decide (loop_contains h u).
      + right.
        copy H0 Htedge.
        eapply tcfg_edge_destruct' in H0.
        destruct H0 as [[H0 H1]|[[H0 H1]|[[H0 H1]|[H0 H1]]]].
        * eapply IHt. all: cycle 1; eauto.
        * destruct j'.
          -- exfalso.
             cbn in Hpath.
             eapply tag_depth_unroot in Hpath;eauto.
             eapply loop_contains_deq_loop in Hin. eapply deq_loop_depth in Hin.
             rewrite Hpath in Hlen.
             destruct k;cbn in *;[congruence|lia].
          -- eapply IHt. all: cycle 1; eauto. cbn in H0. inversion H0. eauto.
        * destruct j'.
          -- exfalso.
             cbn in Hpath.
             eapply tag_depth_unroot in Hpath;eauto.
             eapply loop_contains_deq_loop in Hin. eapply deq_loop_depth in Hin.
             rewrite Hpath in Hlen.
             destruct k;cbn in *;[|lia].
             eapply loop_contains_loop_head in l0.
             eapply depth_loop_head in l0. lia.
          -- destruct l;cbn in H0;[congruence|].
             eapply IHt. all: cycle 1; eauto.
             instantiate (1:=(n0 :: j')). cbn. inv H0. reflexivity.
        * destruct l.
          -- exfalso.
             eapply tag_depth_unroot in Hpath;eauto.
             rewrite H0 in Hpath. cbn in Hpath.
             eapply loop_contains_deq_loop in Hin as Hdeq. eapply deq_loop_depth in Hdeq.
             eapply loop_contains_loop_head in Hin.
             eapply depth_loop_head in Hin. lia.
          -- cbn in H0. eapply IHt. all: cycle 1; eauto. instantiate (1:=n :: j').
             cbn. rewrite H0. reflexivity.
      + eapply entry_through_header in Hin as Hin'. 2:eauto. 2: destruct H0;eauto.
        subst q.
        assert (entry_edge u h) as Hentry.
        { split. 1: eapply loop_contains_loop_head;eauto. split;destruct H0;eauto. }
        rewrite <-tag_entry_iff in Hentry;eauto.
        assert (| j' ++ k | = depth h).
        { eapply tag_depth_unroot in Hpath;eauto. }
        destruct j'.
        * exfalso.
          cbn in H1, Hentry. destruct k;[congruence|]. rewrite <-H1 in Hlen. cbn in Hlen. lia.
        * destruct j'.
          -- cbn in Hentry. inv Hentry. left. reflexivity.
          -- exfalso.
             rewrite <- H1 in Hlen. cbn in Hlen.
             rewrite app_length in Hlen. lia.
  Qed.

  Lemma ex_entry_rooted (h q : Lab) (j : Tag) n t
        (Hin : loop_contains h q)
        (Hpath : TPath (root,start_tag) (q,j) t)
        (Hdep : depth h = n)
    : (h,0 :: (take_r (n-1) j)) ∈ t.
  Proof.
    assert (n <= |j|) as Hnj.
    {
      eapply loop_contains_deq_loop in Hin.
      eapply deq_loop_depth in Hin.
      eapply tag_depth' in Hpath. rewrite Hpath.
      lia.
    }
    eapply ex_entry in Hpath;eauto.
    - eapply root_no_loop.
    - cbn. symmetry. eapply depth_root.
    - eapply take_take_r with (n:=|j| - (n - 1)).
      lia.
    - rewrite <- Hdep.
      eapply (take_r_length_le).
      lia.
  Qed.

  Lemma ex_entry_innermost (h p q : Lab) (i j : Tag) t
        (Hdep : | i | = depth p)
        (Hin : innermost_loop h q)
        (Hnin : ~ loop_contains h p)
        (Hpath : TPath (p,i) (q,j) t)
    : (h,0 :: tl j) ∈ t.
  Proof.
    destruct Hin as [Hloop Hinner].
    eapply loop_contains_deq_loop in Hloop as Hdeq.
    eapply deq_loop_depth in Hdeq.
    eapply loop_contains_loop_head in Hloop as Hhead.
    eapply depth_loop_head in Hhead. cbn in Hpath.
    eapply tag_depth_unroot in Hpath as Hq;eauto.
    destruct j;cbn;[exfalso;cbn in Hq;lia|].
    eapply ex_entry with (j':=[n]) in Hloop;eauto.
    cbn in Hq. eapply deq_loop_depth in Hinner. lia.
  Qed.

  Lemma tagle_monotone q j p i t h n
        (Hlen : |j| = depth q)
        (Hpath : TPath (q,j) (p,i) t)
        (Hdeqq : deq_loop q h)
        (Hdeqp : deq_loop p h)
        (Hdep : depth h = n)
    : take_r n j ⊴ take_r n i.
  Proof.
    revert n h p i Hpath Hdeqp Hdeqq Hdep.
    induction t;intros; inv_path Hpath.
    - reflexivity.
    - case (depth h) eqn:E.
      { cbn. reflexivity. }
      destruct x.
      eapply tcfg_edge_destruct' in H0.
      eapply tag_depth_unroot in H as Htagt0;eauto.
      destruct H0 as [[H0 Q0]|[[H0 Q0]|[[H0 Q0]|[H0 Q0]]]].
      + subst. eapply IHt;eauto.
        eapply basic_edge_eq_loop in Q0. symmetry in Q0. eapply eq_loop1;eauto.
      + decide (loop_contains p q).
        * subst i.
          specialize (tcfg_reachability Hlen) as Hreach.
          destructH.
          eapply ex_entry_rooted in Hreach as Hentry;eauto.
          eapply path_from_elem in Hentry;eauto.
          destructH.
          eapply path_app' in Hpath;eauto.
          eapply depth_entry in Q0 as Q1.
          eapply loop_contains_deq_loop in l as Hdeppq. eapply deq_loop_depth in Hdeppq.
          assert (depth p - 1 = depth e) as Hdeppe by lia.
          eapply deq_loop_depth in Hdeqq as Hdepq.
          eapply deq_loop_depth in Hdeqp as Hdepp.
          eapply tcfg_fresh in Hpath.
          2: {
            cbn.
            rewrite take_r_length_le.
            1: lia.
            lia.
          }
          2: { cbn. destruct t;[inv H|]. cbn. lia. }
          rewrite taglt_cons in Hpath.
          decide (depth p - 1 <= S n).
          -- left.
             eapply taglt_leq with (m:=depth p - 1).
             2-4: cbn;lia.
             rewrite take_r_cons_drop.
             2: lia.
             rewrite Hdeppe at 2. rewrite <-Htagt0.
             rewrite take_r_self. eassumption.
          -- eapply taglt_tagle in Hpath. eapply tagle_take_r with (n:=S n) in Hpath.
             rewrite take_r_cons_drop.
             2: lia.
             rewrite take_r_take_r_leq in Hpath.
             2: lia.
             eassumption.
        * subst i.
          assert (deq_loop e h) as Hdeqe.
          {
            intros h' Hh'.
             eapply deq_loop_entry_or in Q0;cycle 1.
             { eapply Hdeqp;eauto. }
             destruct Q0.
             - auto.
             - exfalso.
               subst p. eapply n0. eauto using loop_contains_deq_loop.
          }
          rewrite take_r_cons_drop.
          -- eapply IHt;eauto.
          -- rewrite Htagt0. rewrite <-E. eapply deq_loop_depth. auto.
      + destruct t0.
        { exfalso. cbn in Htagt0. eapply back_edge_eq_loop in Q0.
          rewrite Q0 in Htagt0. enough (depth p > 0) by lia.
          eapply deq_loop_depth in Hdeqp. lia.
        }
        rewrite H0.
        transitivity (take_r (S n) (n0 :: t0)).
        * eapply IHt;eauto.
          eapply back_edge_eq_loop in Q0. symmetry in Q0. eapply eq_loop1;eauto.
        * unfold STag.
          eapply tagle_take_r.
          econstructor.
          econstructor.
          lia.
      + destruct t0.
        {
          exfalso.
          cbn in Htagt0.
          eapply depth_exit in Q0.
          lia.
        }
        eapply IHt in H;eauto.
        * cbn in H0. subst t0.
          setoid_rewrite <-take_r_cons_drop at 2;eauto.
          eapply deq_loop_depth in Hdeqp.
          erewrite tag_depth_unroot;eauto. lia.
        * transitivity p;eauto.
          destruct Q0. eapply deq_loop_exited;eauto.
  Qed.

  Lemma tagle_monotone_eq_loop q1 q2 j1 j2 r
        (Hdep : | j1 | = depth q1)
        (Hpath : TPath (q1,j1) (q2,j2) r)
        (Hin : forall x, x ∈ map fst r -> deq_loop x q1)
        (Heq : eq_loop q1 q2)
    : j1 ⊴ j2.
  Proof.
    copy Hpath Hpath1.
    eapply tagle_monotone in Hpath.
    4: destruct Heq as [_ Heq];eapply Heq.
    3: reflexivity.
    2: assumption.
    2: reflexivity.
    rewrite take_r_geq in Hpath.
    2: rewrite <-Hdep;eauto.
    rewrite take_r_geq in Hpath.
    1: assumption.
    rewrite Heq.
    eapply tag_depth_unroot in Hpath1;eauto.
    rewrite Hpath1;eauto.
  Qed.

  Lemma tcfg_acyclic p i q j t
        (Hdep : | i | = depth p)
        (Hedge : tcfg_edge (q,j) (p,i))
        (Hpath : TPath (p,i) (q,j) t)
    : False.
  Proof.
    eapply PathCons in Hedge;eauto.
    eapply tcfg_fresh in Hedge;cbn;eauto.
    2: inv_path Hpath;cbn;eauto;lia.
    eapply Taglt_irrefl;eassumption.
  Qed.

End cfg.
