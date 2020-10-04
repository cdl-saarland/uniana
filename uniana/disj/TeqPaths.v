Require Export DiamondIncl CncLoop.
Require Import Lia LastCommon.

Lemma only_inner_heads_tag_prefix `(C : redCFG) p i q j l
      (Hdep : | i | = depth p)
      (Hpath : TPath (p, i) (q, j) l)
      (Hnhead : forall (h' : Lab) (k' : Tag), (h',k') ∈ tl (rev l) -> loop_contains h' q -> False)
      (Hdeqq : forall (h' : Lab) (k' : Tag), (h',k') ∈ l -> deq_loop h' q)
  : Prefix j i.
Proof.
  clear - Hpath Hnhead Hdeqq Hdep.
  remember (l) as l' in Hpath.
  assert (Postfix l' l) as Hpost by (rewrite Heql';econstructor;eauto).
  assert ((p,i) ∈ l') as Hel.
  { (rewrite Heql';eapply path_contains_back;subst;eauto). }
  remember p as p'. remember i as i'. rewrite Heqp' in Hpath. rewrite Heqi' in Hpath.
  rewrite Heqp' in Hdep. rewrite Heqi' in Hdep.
  clear Heql' Heqp' Heqi'.
  revert p' i' Hel p i Hpath Hdep.
  rinduction l'.
  - contradiction.
  - eapply In_rcons in Hel. destruct Hel.
    + subst a.
      specialize (rcons_destruct l0) as Hl0. destruct Hl0;[|destructH];subst l0.
      * cbn in *.
        inversion Hpath;subst. 2: { inversion H4. }
        destruct l;[inversion Hpost;congruence'|]; eapply postfix_hd_eq in Hpost;
                                 inversion Hpost;subst;cbn.
        econstructor;auto.
      * destruct a.
        unfold TPath in Hpath.
        assert ((p',i') ∈ l) as Helpi.
        { eapply postfix_incl;eauto. }
        replace i' with (snd (p',i')) by (cbn;auto).
        path_simpl' Hpath. cbn. copy Hpath Hpath'.
        eapply path_nlrcons_edge in Hpath.
        exploit' H.
        1: { eapply postfix_step_left;eauto. }
        specialize (H e t). exploit' H. specialize (H e t). exploit H.
        1: eapply path_rcons_rinv;eauto.
        1: eapply tcfg_edge_depth_iff in Hpath;eapply Hpath;eauto.
        eapply tcfg_edge_destruct in Hpath as Q.
        assert ((e,t) ∈ l) as Helet.
        { eapply postfix_incl;eauto. }
        destruct Q as [Q|[Q|[Q|Q]]]. all: subst.
        -- eauto. (* normal *)
        -- inversion H;subst. (* entry *)
           ++ exfalso.
              specialize (Hdeqq p i). exploit Hdeqq.
              eapply deq_loop_depth in Hdeqq.
              assert (|i| < |0 :: i|) as Q by (cbn;lia). clear Helet.
              eapply tag_depth_unroot in Hpath';eauto. lia.
           ++ auto.
        -- inversion H.  (* back_edge *)
           ++ subst.
              destruct i. 1:cbn;econstructor.
              exfalso.
              eapply Hnhead.
              ** eapply postfix_rev_prefix in Hpost.
                 rewrite rev_rcons in Hpost.
                 eapply prefix_tl in Hpost.
                 eapply prefix_incl;eauto. rewrite rev_rcons. left. reflexivity.
              ** specialize (tag_back_edge_iff Hpath) as [Q _]. exploit Q;eauto.
                 eapply deq_loop_head_loop_contains.
                 --- eapply deq_loop_depth_eq.
                     +++ eapply Hdeqq;eauto.
                     +++ eapply tag_depth_unroot in Hpath';eauto. cbn in Hpath',Hdep.
                         eapply back_edge_eq_loop in Q. rewrite <-Q. lia.
                 --- exists p;eauto.
           ++ subst. destruct i.
              ** cbn in H0. congruence.
              ** inversion H0. subst. econstructor. eauto.
        -- clear - H;destruct i;cbn in *;[auto|]. inversion H;subst;econstructor;auto.
    + destruct l0;[cbn in *;contradiction|].
      unfold TPath in Hpath. path_simpl' Hpath. cbn in Hpath. path_simpl' Hpath.
      eapply tag_depth_unroot in Hpath as Hdepq;eauto.
      eapply path_rcons_inv in Hpath. destructH. destruct p0.
      eapply H;eauto.
      * eapply postfix_step_left;eauto.
      * eapply tag_depth_unroot2 in Hpath;eauto.
Qed.

Lemma teq_l_len1 `(T : TeqPaths)
  : | l1 | = depth u1.
Proof.
  destruct T.
  eapply tag_depth_unroot2 in Tpath1;eauto.
Qed.

Lemma teq_l_len2 `(T : TeqPaths)
  : | l2 | = depth u2.
Proof.
  destruct T.
  eapply tag_depth_unroot2 in Tpath2;eauto;rewrite <-Tjj_len;rewrite <-Tloop;eassumption.
Qed.

Hint Resolve teq_l_len1 teq_l_len2 : teq.

Lemma teq_split `(T : TeqPaths)
      (Hnroot1 : u1 <> root)
      (Hnroot2 : u2 <> root)
  : exists s k r1' r2', SplitPaths s q1 q2 k j1 j2 ((q1,j1) :: r1 ++ r1') ((q2,j2) :: r2 ++ r2').
Proof.
  destruct T.
  assert (|l1| = depth u1) as Hul1.
  { eapply tag_depth_unroot2 in Tpath1;eauto. }
  assert (|l2| = depth u2) as Hul2.
  { eapply tag_depth_unroot2 in Tpath2;eauto;rewrite <-Tjj_len;rewrite <-Tloop;eassumption. }
  specialize (tcfg_reachability Hul1) as Hreach1. destructH.
  specialize (tcfg_reachability Hul2) as Hreach2. destructH.
  destr_r' t;subst;[inv Hreach1|].
  destr_r' t0;subst;[inv Hreach2|].
  unfold TPath in *. path_simpl' Hreach1. path_simpl' Hreach2.
  destruct l,l0;cbn in *.
  - exfalso.
    eapply path_single in Hreach1. eapply path_single in Hreach2. do 2 destructH.
    inv Hreach4. inv Hreach3. eapply Tdisj.
    1,2: eapply path_contains_back;eauto.
  - eapply path_single in Hreach1. inv Hreach1. inv H. contradiction.
  - eapply path_single in Hreach2. inv Hreach2. inv H. contradiction.
  - inv_path Hreach1. 1:congruence'. inv_path Hreach2. 1:congruence'.
     specialize (ne_last_common) with (l1:=(q1,j1) :: r1 ++ l) (l2:=(q2,j2) :: r2 ++ l0) (a:=(root,start_tag)) as Hlc.
     specialize (Hlc eq_equivalence Coord_dec). destructH.
     destruct s as [s k].
     rewrite last_common'_iff in Hlc. destructH.
     unfold last_common' in Hlc. destructH.
     assert (Postfix ((q1,j1) :: r1) l1') as Hpost1;[|copy Hpost1 Hr1].
     {
       eapply postfix_eq. eapply postfix_eq in Hlc0. admit.
     }
     assert (Postfix ((q2,j2) :: r2) l2') as Hpost2;[|copy Hpost2 Hr2].
     {
       admit.
     }
     eapply postfix_eq in Hr1 as [r1' Hr1].
     eapply postfix_eq in Hr2 as [r2' Hr2].
     exists s, k, r1', r2'.
     assert (TPath (s, k) (q1, j1) (((q1, j1) :: r1 ++ r1') :r: (s, k))) as Hpath1.
     {
       cbn. rewrite <-app_assoc.
       rewrite app_comm_cons. rewrite app_assoc. rewrite <-Hr1.
       eapply path_postfix_path. 2:eauto.
       cbn. rewrite <-app_assoc. rewrite app_comm_cons.
       eapply path_app;eauto.
     }
     assert (TPath (s, k) (q2, j2) (((q2, j2) :: r2 ++ r2') :r: (s, k))) as Hpath2.
     {
       cbn. rewrite <-app_assoc.
       rewrite app_comm_cons. rewrite app_assoc. rewrite <-Hr2.
       eapply path_postfix_path. 2:eauto.
       cbn. rewrite <-app_assoc. rewrite app_comm_cons.
       eapply path_app;eauto.
     }
     econstructor;eauto.
     * cbn in *. rewrite <-Hr1, <-Hr2. eassumption.
     * eapply tag_depth_unroot2. 1: eapply Hpath1. eauto.

Admitted.

Lemma teq_root_all_nil1 `(T : TeqPaths)
      (Hin : root ∈ (q1 :: map fst r1))
  : u1 = root /\ l1 = [] /\ j1 = [] /\ j2 = [] /\ depth q1 = 0 /\ forall x, deq_loop x q1.
Proof.
  assert (u1 = root) as Hroot.
  { destruct T. clear - Tpath1 Hin.
    revert q1 j1 Tpath1 Hin.
    induction r1;cbn in *;intros.
    - eapply path_single in Tpath1. destructH. inv Tpath0. destruct Hin;[|contradiction]. subst;auto.
    - inv_path Tpath1. destruct a. eapply IHr1. 1: eapply H.
      destruct Hin.
      + subst q1. eapply tcfg_edge_edge in H0. eapply root_no_pred in H0. contradiction.
      + destruct H1. cbn in H1. subst e.
        * destruct r1;[left;auto|]. inv_path H. destruct p.
          eapply tcfg_edge_edge in H2. eapply root_no_pred in H2. contradiction.
        * right;auto.
  }
  subst u1. split;auto.
  assert (l1 = []) as Hnil1.
  {
    eapply teq_l_len1 in T. rewrite depth_root in T. destruct l1;[|cbn in T;congruence]. reflexivity.
  }
  split;auto.
  assert (j1 = []) as Hnilj1.
  { destruct T. destruct Tlj_eq1;subst;auto. destruct H. congruence. }
  split;auto.
  split.
  - destruct T. subst l1 j1. cbn in Tjj_len. destruct j2;[|cbn in Tjj_len;congruence]. auto.
  - destruct T. subst j1. cbn in Tj_len. split;eauto.
    intros x y Hy.
    symmetry in Tj_len. eapply depth_zero_iff in Tj_len;eauto. contradiction.
Qed.

Lemma teq_root_all_nil2 `(T : TeqPaths)
      (Hin : root ∈ (q2 :: map fst r2))
  : u2 = root /\ l2 = [] /\ j1 = [] /\ j2 = [] /\ depth q1 = 0 /\ forall x, deq_loop x q1.
Proof.
  assert (u2 = root) as Hroot.
  { destruct T. clear - Tpath2 Hin.
    revert q2 j2 Tpath2 Hin.
    induction r2;cbn in *;intros.
    - eapply path_single in Tpath2. destructH. inv Tpath0. destruct Hin;[|contradiction]. subst;auto.
    - inv_path Tpath2. destruct a. eapply IHr2. 1: eapply H.
      destruct Hin.
      + subst q2. eapply tcfg_edge_edge in H0. eapply root_no_pred in H0. contradiction.
      + destruct H1. cbn in H1. subst e.
        * destruct r2;[left;auto|]. inv_path H. destruct p.
          eapply tcfg_edge_edge in H2. eapply root_no_pred in H2. contradiction.
        * right;auto.
  }
  subst u2. split;auto.
  assert (l2 = []) as Hnil2.
  {
    eapply teq_l_len2 in T. rewrite depth_root in T. destruct l2;[|cbn in T;congruence]. reflexivity.
  }
  split;auto.
  assert (j1 = []) as Hnilj2.
  { destruct T. destruct Tlj_eq2;subst;auto. destruct H.
    - destruct H. congruence.
    - eapply loop_contains_loop_head in H. eapply loop_contains_self in H. eapply root_no_loop in H.
      contradiction.
  }
  split;auto.
  split.
  - destruct T. subst l2 j1. cbn in Tjj_len. destruct j2;[|cbn in Tjj_len;congruence]. auto.
  - destruct T. subst j1. cbn in Tj_len. split;eauto.
    intros x y Hy.
    symmetry in Tj_len. eapply depth_zero_iff in Tj_len;eauto. contradiction.
Qed.

Lemma teq_root_teq1 `(C : redCFG) u2 q1 q2 l1 l2 j1 j2 r1 r2
      (T : TeqPaths root u2 q1 q2 l1 l2 j1 j2 (r1 ++ [(root,start_tag)]) r2)
  : exists u1 l1', u1 <> root /\ TeqPaths u1 u2 q1 q2 l1' l2 j1 j2 r1 r2.
Proof.
  eapply teq_root_all_nil1 in T as Hnil.
  2: { destruct T. eapply TPath_CPath in Tpath1. cbn in Tpath1.
       eapply path_contains_back in Tpath1. eauto. }
  copy T T'.
  destruct T'.
  replace l1 with start_tag in *.
  2: { rewrite app_comm_cons in Tpath1. eapply path_back in Tpath1. inv Tpath1. eauto. }
  destructH. subst.
  eapply path_rcons_inv' in Tpath1 as Hpath1. destructH.
  destruct p.
  exists e, t.
  split;[|econstructor];eauto.
  - eapply tcfg_edge_edge in Hpath2. intro N. subst e. eapply root_no_pred in Hpath2. contradiction.
  - eapply disjoint_subset. 3: eapply Tdisj. 2:reflexivity. eauto.
  - eapply tcfg_edge_destruct' in Hpath2.
    destruct Hpath2 as [Q|[Q|[Q|Q]]].
    all: destruct Q as [Htag Hedge];subst.
    + left. eauto.
    + right. split;eauto. destruct Hedge;eauto.
    + exfalso. eapply loop_contains_ledge in Hedge. eapply loop_contains_depth_lt in Hedge.
      rewrite depth_root in Hedge. lia.
    + exfalso. eapply depth_exit in Hedge. rewrite depth_root in Hedge. lia.
Qed.

Lemma teq_root_teq2 `(C : redCFG) u1 q1 q2 l1 l2 j1 j2 r1 r2
      (T : TeqPaths u1 root q1 q2 l1 l2 j1 j2 r1 (r2 ++ [(root,start_tag)]))
  : exists u2 l2', u2 <> root /\ TeqPaths u1 u2 q1 q2 l1 l2' j1 j2 r1 r2.
Proof.
  eapply teq_root_all_nil2 in T as Hnil.
  2: { destruct T. eapply TPath_CPath in Tpath2. cbn in Tpath2.
       eapply path_contains_back in Tpath2. eauto. }
  copy T T'.
  destruct T'.
  replace l2 with start_tag in *.
  2: { rewrite app_comm_cons in Tpath2. eapply path_back in Tpath2. inv Tpath2. eauto. }
  destructH. subst.
  eapply path_rcons_inv' in Tpath2 as Hpath1. destructH.
  destruct p.
  exists e, t.
  split;[|econstructor];eauto.
  - eapply tcfg_edge_edge in Hpath2. intro N. subst e. eapply root_no_pred in Hpath2. contradiction.
  - eapply disjoint_subset. 3: eapply Tdisj. 1:reflexivity. eauto.
  - eapply tcfg_edge_destruct' in Hpath2.
    destruct Hpath2 as [Q|[Q|[Q|Q]]].
    all: destruct Q as [Htag Hedge];subst.
    + left. eauto.
    + right. left. split;eauto. destruct Hedge;eauto.
    + exfalso. eapply loop_contains_ledge in Hedge. eapply loop_contains_depth_lt in Hedge.
      rewrite depth_root in Hedge. lia.
    + exfalso. eapply depth_exit in Hedge. rewrite depth_root in Hedge. lia.
Qed.

Lemma teq_split_root1 `(C : redCFG) u2 q1 q2 l1 l2 j1 j2 r1 r2
      (Hnroot2 : u2 <> root)
      (T : TeqPaths root u2 q1 q2 l1 l2 j1 j2 r1 r2)
  : exists s k r1' r2', SplitPaths s q1 q2 k j1 j2 (r_tl ((q1,j1) :: r1) ++ r1') ((q2,j2) :: r2 ++ r2').
Proof.
  specialize (tcfg_reachability (teq_l_len2 T)) as Hreach2. destructH.
  copy T T'. destruct T.
  assert (l1 = []) as Hlnil.
  { eapply tag_depth_unroot2 in Tpath1;eauto. rewrite depth_root in Tpath1.
    destruct l1;[|cbn in Tpath1;congruence]. reflexivity. }
  subst l1.
  destr_r' r1;subst.
  - eapply path_single in Tpath1. destructH. inversion Tpath0. subst q1 j1.
    inv_path Hreach2. 1:contradiction.
    destr_r' π;subst. 1: inv H. path_simpl' H.
    eapply path_rcons_inv' in Hreach2 as H'. destructH.
    exists root, nil, nil, l.
    unfold r_tl. cbn.
    econstructor;cbn;eauto.
    + econstructor.
    + rewrite app_comm_cons. eapply path_rcons;eauto.
      eapply path_app' in Tpath2;eauto. cbn in Tpath2. eauto.
    + eapply Disjoint_nil1.
  - rewrite app_comm_cons in Tpath1. unfold TPath in Tpath1. path_simpl' Tpath1.
    eapply teq_root_teq1 in T'. destructH.
    eapply teq_split in T'1;eauto.
    destructH. exists s, k. do 2 eexists.
    rewrite app_comm_cons. rewrite r_tl_rcons. eassumption.
Qed.

Lemma teq_split_root2 `(C : redCFG) u1 q1 q2 l1 l2 j1 j2 r1 r2
      (Hnroot2 : u1 <> root)
      (T : TeqPaths u1 root q1 q2 l1 l2 j1 j2 r1 r2)
  : exists s k r1' r2', SplitPaths s q1 q2 k j1 j2 ((q1,j1) :: r1 ++ r1') (r_tl ((q2,j2) :: r2) ++ r2').
Proof.
  specialize (tcfg_reachability (teq_l_len1 T)) as Hreach1. destructH.
  copy T T'. destruct T.
  assert (l2 = []) as Hlnil.
  { eapply teq_l_len2 in T'. rewrite depth_root in T'.
    destruct l2;[|cbn in T';congruence]. reflexivity. }
  subst l2.
  destr_r' r2;subst.
  - eapply path_single in Tpath2. destructH. inversion Tpath0. subst q2 j2.
    inv_path Hreach1. 1:contradiction.
    destr_r' π;subst. 1: inv H. path_simpl' H.
    eapply path_rcons_inv' in Hreach1 as H'. destructH.
    exists root, nil, l, nil.
    unfold r_tl. cbn.
    econstructor;cbn;eauto.
    + rewrite app_comm_cons. eapply path_rcons;eauto.
      eapply path_app' in Tpath1;eauto. cbn in Tpath1. eauto.
    + econstructor.
    + eapply Disjoint_nil2.
    + rewrite depth_root. reflexivity.
  - rewrite app_comm_cons in Tpath2. unfold TPath in Tpath2. path_simpl' Tpath2.
    eapply teq_root_teq2 in T'. destructH.
    eapply teq_split in T'1;eauto.
    destructH. exists s, k, r1', r2'.
    assert (((q2, j2) :: l ++ r2') = (r_tl ((q2, j2) :: l :r: (root, [])) ++ r2')) as QQ.
    { setoid_rewrite app_comm_cons at 2. rewrite r_tl_rcons. reflexivity. }
    rewrite QQ in T'1. eassumption.
Qed.

Lemma teq_split_sub `(T : TeqPaths)
  : exists s k r1' r2', SplitPaths s q1 q2 k j1 j2 r1' r2'
                   /\ ((q1,j1) :: r1) ⊆ ((root,start_tag) :: r1')
                   /\ ((q2,j2) :: r2) ⊆ ((root,start_tag) :: r2').
Proof.
  decide (u1 = root) as [Hroot1|Hnroot1].
  - copy T T'.
    destruct T.
    subst u1.
    eapply tag_depth_unroot2 in Tpath1 as Hdep1;eauto. rewrite depth_root in Hdep1.
    destruct l1;[|cbn in Hdep1;congruence].
    decide (u2 = root) as [Hroot2|Hnroot2].
    + exfalso. subst u2.
      eapply tag_depth_unroot2 in Tpath2 as Hdep2;eauto. 2: rewrite <-Tjj_len;rewrite <-Tloop;auto.
      rewrite depth_root in Hdep2.
      destruct l2;[|cbn in Hdep2;congruence].
      eapply Tdisj.
      1,2:eapply path_contains_back;eauto.
    + eapply teq_split_root1 in T';eauto.
      destructH. exists s, k. do 2 eexists.
      split_conj;eauto.
      destr_r' r1;subst.
      * eapply path_single in Tpath1. destructH. rewrite <-Tpath0.
        left. destruct H;[auto|contradiction].
      * rewrite app_comm_cons in Tpath1. unfold TPath in Tpath1. path_simpl' Tpath1.
        intros y Hin. setoid_rewrite app_comm_cons at 2. rewrite r_tl_rcons.
        rewrite app_comm_cons in Hin. eapply In_rcons in Hin.
        destruct Hin;[left;auto|].
        right. eapply in_or_app. left. auto.
  - decide (u2 = root) as [Hroot2|Hnroot2].
    + subst u2. copy T T'. destruct T.
      eapply tag_depth_unroot2 in Tpath2 as Hdep2;eauto. 2: rewrite <-Tjj_len;rewrite <-Tloop;auto.
      rewrite depth_root in Hdep2.
      destruct l2;[|cbn in Hdep2;congruence].
      eapply teq_split_root2 in T';eauto.
      destructH. exists s, k. do 2 eexists.
      split_conj;eauto.
      destr_r' r2;subst.
      * eapply path_single in Tpath2. destructH. rewrite <-Tpath0.
        left. destruct H;[auto|contradiction].
      * rewrite app_comm_cons in Tpath2. unfold TPath in Tpath2. path_simpl' Tpath2.
        intros y Hin. setoid_rewrite app_comm_cons at 2. rewrite r_tl_rcons.
        rewrite app_comm_cons in Hin. eapply In_rcons in Hin.
        destruct Hin;[left;auto|].
        right. auto.
    + eapply teq_split in T;eauto.
      destructH.
      exists s, k. do 2 eexists.
      split_conj;eauto.
Qed.

Section teq.
  Context `(T : TeqPaths).

  Lemma teq_r1_incl_head_q : forall x, x ∈ (q1 :: map fst r1) -> deq_loop x q1.
  Proof.
    decide (root ∈ (q1 :: map fst r1)).
    - eapply teq_root_all_nil1 in i;eauto. destructH. intros. eauto.
    - eapply teq_split_sub in T as T'. destructH.
      intros.
      eapply spath_r1_incl_head_q in T'0;eauto.
      eapply incl_map with (f:=fst) in T'2;eauto. cbn in T'2.
      eapply incl_rcons in T'2;eauto.
  Qed.

  Lemma teq_r2_incl_head_q : forall x, x ∈ (q2 :: map fst r2) -> deq_loop x q1.
  Proof.
    decide (root ∈ (q2 :: map fst r2)).
    - eapply teq_root_all_nil2 in i;eauto. destructH. intros. eauto.
    - eapply teq_split_sub in T as T'. destructH.
      intros.
      eapply spath_r2_incl_head_q in T'0;eauto.
      eapply incl_map with (f:=fst) in T'3;eauto. cbn in T'3.
      eapply incl_rcons in T'3;eauto.
  Qed.

  Lemma teq_u1_deq_q
    : deq_loop u1 q1.
  Proof.
    eapply teq_r1_incl_head_q;eauto.
    destruct T.
    inv_path Tpath1. 1:left;eauto.
    eapply path_contains_back in H.
    fold (fst (u1,l1)). right.
    eapply in_map;eauto.
  Qed.

  Lemma teq_u2_deq_q
    : deq_loop u2 q1.
  Proof.
     eapply teq_r2_incl_head_q;eauto.
    destruct T.
    inv_path Tpath2. 1:left;eauto.
    eapply path_contains_back in H.
    fold (fst (u2,l2)). right.
    eapply in_map;eauto.
  Qed.

End teq.

Lemma jj_tagle `(T : TeqPaths)
  : j1 ⊴ j2.
Proof.
  decide (u1 = root) as [?|Hnroot].
  { eapply teq_l_len1 in T as Hdep;eauto. subst u1. rewrite depth_root in Hdep.
    destruct l1;[|cbn in Hdep;congruence].
    eapply teq_root_all_nil1 in T;eauto.
    - destructH. subst. reflexivity.
    - destruct T. eapply TPath_CPath in Tpath1. cbn in Tpath1. eapply path_contains_back;eauto.
  }
  decide (u2 = root) as [?|Hnroot2].
  { eapply teq_l_len2 in T as Hdep;eauto. subst u2. rewrite depth_root in Hdep.
    destruct l2;[|cbn in Hdep;congruence].
    eapply teq_root_all_nil2 in T;eauto.
    - destructH. subst. reflexivity.
    - destruct T. eapply TPath_CPath in Tpath2. cbn in Tpath2. eapply path_contains_back;eauto.
  }
  copy T T'.
  destruct T.
  assert (loop_contains u2 q1 -> j1 ⊴ j2) as Hncont.
  {
    intro Q.
    eapply tagle_or in Tjj_len;destruct Tjj_len;[auto|exfalso].
    eapply teq_split in T';eauto. destructH.
    eapply SplitPaths_sym in T'.
    eapply spath_no_back in T';eauto.
    + eapply T'. rewrite <-Tloop. eapply Q.
    + rewrite app_comm_cons. rewrite map_app. eapply in_or_app. left.
      eapply path_contains_back in Tpath2. eapply in_map with (f:=fst) in Tpath2.
      cbn in *;eauto.
  }
  decide (loop_contains u2 q1) as [Hcont|HNcont];[eauto|].
  destruct Tlj_eq2 as [Q|[Q|Q]].
  - subst l2. eapply tagle_monotone with (n:=depth q1) in Tpath2.
    + rewrite take_r_geq in Tpath2;[|lia].
      rewrite take_r_geq in Tpath2;[|lia].
      eassumption.
    + eapply tag_depth_unroot2;eauto. rewrite <-Tloop. rewrite <-Tjj_len. assumption.
    + eapply teq_u2_deq_q;eauto.
    + rewrite Tloop. reflexivity.
    + reflexivity.
  - destructH. subst l2.
    eapply tcfg_enroot in Tpath2 as Hroot.
    2: { eapply tag_depth_unroot2;eauto. rewrite <-Tloop. rewrite <-Tjj_len. assumption. }
    destructH.
    destruct t';cbn in Hroot.
    { exfalso. rewrite <-app_nil_end in Hroot.
      destr_r' r2;subst.
      - eapply path_single in Tpath2. inv Tpath2. eapply path_single in Hroot. inv Hroot. inv H.
        cbn in Tjj_len. lia.
      - rewrite app_comm_cons in Hroot. eapply path_back in Hroot. subst x.
        rewrite app_comm_cons in Tpath2. eapply path_back in Tpath2. inv Tpath2.
    }
    destruct c.
    assert (TPath (e, t) (q2, j2) ((q2, j2) :: r2 ++ [(e, t)])) as Hpath.
    { rewrite app_comm_cons. eapply path_postfix_path;eauto.
      setoid_rewrite app_cons_rcons at 2. eapply postfix_eq. exists t'. reflexivity.
    }
    copy Hpath Hpath'.
    eapply path_rcons_inv' in Hpath. destructH.
    replace p with (u2, 0 :: j1) in *.
    2: { destr_r' r2;subst.
         - eapply path_single in Tpath2. inv Tpath2. inv H. inv Hpath0;eauto. inv H1.
         - rewrite app_comm_cons in Hpath0. eapply path_back in Hpath0.
           rewrite app_comm_cons in Tpath2. eapply path_back in Tpath2. subst x p. reflexivity.
    }
    eapply tcfg_edge_destruct' in Hpath1.
    destruct Hpath1 as [M|[M|[M|M]]].
    all: destruct M as [Htag Hedge].
    + exfalso. eapply basic_edge_no_loop2 in Hedge. contradiction.
    + symmetry in Htag. inv Htag.
      eapply tagle_monotone with (n:=depth q1) in Hpath'.
      * rewrite take_r_geq in Hpath';[|lia].
        rewrite take_r_geq in Hpath';[|lia].
        eassumption.
      * eapply tag_depth_unroot2;eauto. rewrite <-Tloop. rewrite <-Tjj_len. assumption.
      * intros h Hh. eapply teq_u2_deq_q in Hh as Hh'. 2: eauto.
        eapply deq_loop_entry_or in Hh'. 2:eauto. destruct Hh';[auto|]. subst h.
        contradiction.
      * rewrite Tloop. reflexivity.
      * reflexivity.
    + destruct t;cbn in Htag;congruence.
    + destruct Hedge. exfalso. eapply no_exit_head;eauto.
  - contradiction.
Qed.

Section teq.

  Context `(T : TeqPaths).

  Lemma teq_no_back : forall x : Lab, x ∈ (q1 :: map fst r1) -> ~ loop_contains x q1.
  Proof.
    decide (root ∈ (q1 :: map fst r1)).
    { intros. intro N. eapply teq_root_all_nil1 in i;eauto. destructH. subst.
      eapply loop_contains_depth_lt in N. lia. }
    eapply teq_split_sub in T as T'. destructH.
    intros.
    eapply spath_no_back in T'0;eauto.
    { eapply jj_tagle;eauto. }
    eapply incl_map with (f:=fst) in T'2;eauto. cbn in T'2.
    eapply incl_rcons in T'2;eauto.
  Qed.

  Lemma teq_no_back2
        (Htageq : j1 = j2)
    : forall x : Lab, x ∈ (q2 :: map fst r2) -> ~ loop_contains x q1.
  Proof.
    decide (root ∈ (q2 :: map fst r2)).
    { intros. intro N. eapply teq_root_all_nil2 in i;eauto. destructH. subst.
      eapply loop_contains_depth_lt in N. lia. }
    intros.
    eapply teq_split_sub in T as T'. destructH.
    intros. eapply SplitPaths_sym in T'0.
    subst j2.
    eapply spath_no_back in T'0;eauto.
    - rewrite Tloop. eauto.
    - reflexivity.
    - eapply incl_map with (f:=fst) in T'3;eauto. cbn in T'3.
      eapply incl_rcons in T'3;eauto.
  Qed.

  Lemma teq_tag_eq1
    : forall j, j ∈ map snd ((q1,j1) :: r1) -> take_r (depth q1) j = j1.
  Proof.
    decide ((root,start_tag) ∈ ((q1,j1) :: r1)).
    { intros. eapply in_map with (f:=fst) in i. eapply teq_root_all_nil1 in i;eauto. destructH. subst.
      cbn in i4. rewrite i4. cbn. reflexivity. }
    eapply teq_split_sub in T as T'. destructH.
    intros. eapply spath_tag_eq1;eauto.
    - eapply jj_tagle;eauto.
    - eapply incl_rcons in T'2;eauto.
      eapply incl_map with (f:=snd) in T'2;eauto.
  Qed.

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
    : ~ loop_head q1.
  Proof.
    intro N. eapply teq_no_back.
    - left. reflexivity.
    - eapply loop_contains_self;eauto.
  Qed.

End teq.

Lemma u1_exit_eq_q `(T : TeqPaths) h p
      (Hexit : exit_edge h p u1)
  : eq_loop u1 q1.
Proof.
  copy T T'.
  destruct T'.
  destruct Tlj_eq1.
  - eapply tag_depth_unroot2 in Tpath1;eauto. subst l1. split.
    + eapply teq_u1_deq_q;eauto.
    + eapply deq_loop_depth_eq. 1: eapply teq_u1_deq_q;eauto. rewrite <-Tj_len. assumption.
  - destructH. subst l1. exfalso. eapply no_exit_head;eauto.
Qed.

Lemma u2_exit_eq_q `(T : TeqPaths) h p
      (Hexit : exit_edge h p u2)
  : eq_loop u2 q1.
Proof.
  copy T T'.
  destruct T'.
  destruct Tlj_eq2. 2:destruct H.
  - eapply tag_depth_unroot2 in Tpath2;eauto. subst l2. split.
    + eapply teq_u2_deq_q;eauto.
    + eapply deq_loop_depth_eq. 1: eapply teq_u2_deq_q;eauto. rewrite <-Tj_len. assumption.
    + rewrite <-Tjj_len. rewrite <-Tloop. assumption.
  - destructH. subst l2. exfalso. eapply no_exit_head;eauto.
  - split.
    + eapply teq_u2_deq_q;eauto.
    + eapply loop_contains_deq_loop;eauto.
Qed.

Hint Resolve Tpath1 Tpath2 Tdisj Tloop Tjj_len Ttl_eq Tlj_eq1 Tlj_eq2 Tj_len : teq.
Hint Resolve teq_r1_incl_head_q teq_r2_incl_head_q teq_u1_deq_q teq_u2_deq_q Tloop : teq.

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

Lemma node_disj_find_head `(T : TeqPaths)
      (x : Lab)
      (Hx1 : x el map fst ((q1, j1) :: r1))
      (h : Lab)
      (n : ocnc_loop h x q1)
      (Hdep : depth h = S (depth q1))
      (Hpath1 : TPath (u1, l1) (q1, j1) ((q1, j1) :: r1))
      (b b0 : Tag)
      (Hin1' : (x, b) el (q1, j1) :: r1)
      (Hin2' : (x, b0) el (q2, j1) :: r2)
      (ϕ : list (Lab * Tag))
      (Hin0 : Path tcfg_edge (u1, l1) (x, b) ϕ)
      (Hin3 : Prefix ϕ ((q1, j1) :: r1))
      (ϕ0 : list (Lab * Tag))
      (Hin1 : Path tcfg_edge (u2, l2) (x, b0) ϕ0)
      (Hin4 : Prefix ϕ0 ((q2, j1) :: r2))
  : (h, 0 :: j1) ∈ ϕ.
Proof.
  decide (h = u1).
  - subst u1. eapply path_contains_back in Hin0.
    specialize Tlj_eq1 as [Heq|Hentry];[exfalso|destructH];subst.
    + eapply tag_depth_unroot2 in Hpath1;eauto with teq.
      destruct T. rewrite <-Tj_len in Hdep. lia.
    + eassumption.
  - eapply ex_entry with (p:=u1).
    + destruct n. destruct c. exact l.
    + eapply tag_depth_unroot2 in Hpath1 as Hdepu;eauto with teq.
      specialize Tlj_eq1 as [Heq|Hentry];[|destructH].
      * subst l1. intro N. rewrite Tj_len in Hdepu. rewrite Hdepu in Hdep.
        eapply loop_contains_deq_loop in N. eapply deq_loop_depth in N. lia.
      * contradict n0. destruct n. eapply eq_loop_same.
        -- split. 2: eapply loop_contains_deq_loop;eassumption.
           eapply deq_loop_depth_eq. 1: eapply loop_contains_deq_loop;eassumption.
           rewrite Hentry0 in Hdepu. cbn in Hdepu. erewrite Tj_len in Hdepu. lia.
        -- eapply loop_contains_loop_head;eauto.
        -- eauto.
    + eapply Hin0.
    + eapply tag_depth_unroot2 in Hpath1;eauto with teq.
    + setoid_rewrite <-teq_tag_eq1 at 3. 2:eapply T.
      eapply take_take_r. all: cycle 1.
      * eapply in_map with (f:=snd) in Hin1'. cbn in *. eauto.
      * eapply tag_depth_unroot2 in Hpath1;eauto with teq.
        eapply tag_depth_unroot in Hin0;eauto. rewrite Hin0.
        destruct n. destruct c. eapply loop_contains_deq_loop in l. eapply deq_loop_depth in l.
        instantiate (1:=depth x - depth q1). lia.
    + rewrite Hdep. cbn. rewrite Tj_len. lia.
Qed.

Lemma teq_node_disj `(T : TeqPaths)
      (Hjeq : j1 = j2)
  : Disjoint (q1 :: map fst r1) (q2 :: map fst r2).
Proof.
  intros x Hx1 Hx2.
  replace (q1 :: map fst r1) with  (map fst ((q1,j1) :: r1)) in Hx1 by (cbn;eauto).
  replace (q2 :: map fst r2) with  (map fst ((q2,j2) :: r2)) in Hx2 by (cbn;eauto).
  decide (deq_loop q1 x).
  - assert (eq_loop q1 x) as Heq.
    { cbn in Hx1. split;eauto. eapply teq_r1_incl_head_q;eauto. }
    replace (q1 :: map fst r1) with  (map fst ((q1,j1) :: r1)) in Hx1 by (cbn;eauto).
    replace (q2 :: map fst r2) with  (map fst ((q2,j2) :: r2)) in Hx2 by (cbn;eauto).
    eapply in_fst in Hx1. destructH.
    eapply in_fst in Hx2. destructH.
    enough (b = b0).
    { subst. eapply Tdisj;eauto. }
    assert (| b | = depth x) as Hxb1.
    {
      eapply path_to_elem in Hx1;eauto. 2: eapply Tpath1. destructH.
      eapply tag_depth_unroot in Hx0;eauto. destruct T. eapply tag_depth_unroot2 in Tpath1;eauto.
    }
    assert (| b0 | = depth x) as Hxb2.
    {
      eapply path_to_elem in Hx2;eauto. 2: eapply Tpath2. destructH.
      eapply tag_depth_unroot in Hx0;eauto. destruct T. eapply tag_depth_unroot2 in Tpath2;eauto.
      rewrite <-Tjj_len. rewrite <-Tloop. eassumption.
    }
    assert (b = j1) as Hbj1.
    {
      erewrite <-take_r_geq with (n:=depth q1) at 1.
      2: rewrite Heq,Hxb1;eauto.
      eapply teq_tag_eq1;eauto.
      eapply in_map with (f:=snd) in Hx1. cbn in *. eauto.
    }
    assert (b0 = j1) as Hbj2.
    {
      erewrite <-take_r_geq with (n:=depth q1) at 1.
      2: rewrite Heq,Hxb2;eauto.
      rewrite Tloop. subst j2.
      eapply TeqPaths_sym in T.
      eapply teq_tag_eq1;eauto.
      eapply in_map with (f:=snd) in Hx2. cbn in *. eassumption.
    }
    subst. reflexivity.
  - eapply ex_ocnc_loop in n. destructH.
    eapply ocnc_depth in n as Hdep.
    specialize Tpath1 as Hpath1.
    specialize Tpath2 as Hpath2.
    subst j2. eapply TeqPaths_sym in T as Tsym.
    eapply in_fst in Hx1 as Hin1. destructH.
    eapply in_fst in Hx2 as Hin2. destructH.
    copy Hin1 Hin1'. copy Hin2 Hin2'.
    eapply path_to_elem in Hin1;eauto. destructH.
    eapply path_to_elem in Hin2;eauto. destructH.

    assert ((h, 0 :: j1) ∈ ϕ) as Hinϕ.
    { clear Tsym. eapply node_disj_find_head;eauto. }
    assert ((h, 0 :: j1) ∈ ϕ0) as Hinϕ0.
    { clear T. eapply node_disj_find_head;eauto.
      - unfold ocnc_loop, cnc_loop.
        split;destruct n;eauto. destruct H;split;eauto. contradict H1.
        eapply eq_loop1;eauto with teq.
      - setoid_rewrite Tloop. eassumption.
    }
    eapply Tdisj. 1,2: eapply prefix_incl;eauto.
Qed.
