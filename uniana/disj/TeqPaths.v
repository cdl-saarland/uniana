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

Section teq.
  Context `(T : TeqPaths).

  Lemma teq_r1_incl_head_q : forall x, x ∈ (q1 :: map fst r1) -> deq_loop x q1.
  Proof.
    destruct T. destructH.
    intros.
    eapply spath_r1_incl_head_q in TS0;eauto.
    eapply postfix_map with (f:=fst) in TS2.
    eapply postfix_incl;eauto.
  Qed.

  Lemma teq_r2_incl_head_q : forall x, x ∈ (q2 :: map fst r2) -> deq_loop x q1.
  Proof.
    destruct T. destructH.
    intros.
    eapply spath_r2_incl_head_q in TS0;eauto.
    eapply postfix_map with (f:=fst) in TS3.
    eapply postfix_incl;eauto.
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

  copy T T'.
  destruct T.
  assert (loop_contains u2 q1 -> j1 ⊴ j2) as Hncont.
  {
    intro Q.
    eapply tagle_or in Tjj_len;destruct Tjj_len;[auto|exfalso].
    destructH.
    eapply SplitPaths_sym in TS0.
    eapply spath_no_back in TS0;eauto.
    + eapply TS0. rewrite <-Tloop. eapply Q.
    + eapply postfix_map with (f:=fst) in TS3.
      eapply postfix_incl;eauto. eapply TPath_CPath in Tpath2. cbn in Tpath2.
      eapply path_contains_back in Tpath2. eauto.
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
    destruct T. destructH. intros.
    eapply spath_no_back in TS0;eauto.
    - eapply jj_tagle;eauto.
    - eapply postfix_map with (f:=fst) in TS2. eapply postfix_incl;eauto.
  Qed.

  Lemma teq_no_back2
        (Htageq : j1 = j2)
    : forall x : Lab, x ∈ (q2 :: map fst r2) -> ~ loop_contains x q1.
  Proof.
    destruct T. destructH.
    intros. eapply SplitPaths_sym in TS0.
    subst j2.
    eapply spath_no_back in TS0;eauto.
    - rewrite Tloop. eauto.
    - reflexivity.
    - eapply postfix_map with (f:=fst) in TS3. eapply postfix_incl;eauto.
  Qed.

  Lemma teq_tag_eq1
    : forall j, j ∈ map snd ((q1,j1) :: r1) -> take_r (depth q1) j = j1.
  Proof.
    destruct T. destructH. intros.
    eapply spath_tag_eq1 in TS0;eauto.
    - eapply jj_tagle;eauto.
    - eapply postfix_map with (f:=snd) in TS2. eapply postfix_incl;eauto.
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
  - destructH. do 4 eexists. split_conj.
    + eapply SplitPaths_sym;eauto.
    + eauto.
    + eauto.
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
        split;destruct n;eauto.
        + destruct H;split;eauto. contradict H1.
          eapply eq_loop1;eauto with teq.
        + intros. eapply H0. destructH. split;eauto. destruct Tsym.
          contradict H3. eapply eq_loop1. 1:symmetry. 1,2:eauto.
      - setoid_rewrite Tloop. eassumption.
    }
    eapply Tdisj. 1,2: eapply prefix_incl;eauto.
Qed.
