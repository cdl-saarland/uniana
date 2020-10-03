Require Export DiamondIncl CncLoop.
Require Import Lia.

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

Section teq.
  Context `(T : TeqPaths).

  Lemma teq_split
    : exists s k r1' r2', SplitPaths s q1 q2 k j1 j2 (r1 ++ r1') (r2 ++ r2').
  Admitted.

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

  Lemma teq_tag_eq1
    : forall j, j ∈ map snd r1 -> take_r (depth q1) j = j1.
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

End teq.

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
Lemma ex_outermost `(C : redCFG) p q
      (Hdeq : deq_loop p q)
      (Hndeq : ~ deq_loop q p)
  : exists h, loop_contains h p /\ ~ loop_contains h q /\ forall h', deq_loop h h' -> loop_contains h' h.
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
      eapply tag_depth_unroot in Hx0;eauto. admit.
    }
    assert (| b0 | = depth x) as Hxb2.
    {
      eapply path_to_elem in Hx2;eauto. 2: eapply Tpath2. destructH.
      eapply tag_depth_unroot in Hx0;eauto. admit.
    }
    assert (b = j1) as Hbj1.
    {
      cbn in Hx1. destruct Hx1.
      - inv H. reflexivity.
      - erewrite <-take_r_geq with (n:=depth q1) at 1.
        2: rewrite Heq,Hxb1;eauto.
        eapply teq_tag_eq1;eauto.
        eapply in_map with (f:=snd) in H. cbn in H. eassumption.
    }
    assert (b0 = j1) as Hbj2.
    {
      cbn in Hx2. destruct Hx2.
      - inv H. reflexivity.
      - erewrite <-take_r_geq with (n:=depth q1) at 1.
        2: rewrite Heq,Hxb2;eauto.
        rewrite Tloop. subst j2.
        eapply TeqPaths_sym in T.
        eapply teq_tag_eq1;eauto.
        eapply in_map with (f:=snd) in H. cbn in H. eassumption.
    }
    subst. reflexivity.
  - eapply ex_ocnc_loop in n. destructH.
    eapply ocnc_depth in n as Hdep.
    specialize Tpath1 as Hpath1.
    specialize Tpath2 as Hpath2.
    subst j2. eapply TeqPaths_sym in T as Tsym.
    eapply in_fst in Hx1 as Hin1. destructH.
    eapply in_fst in Hx2 as Hin2. destructH.
    eapply path_to_elem in Hin1;eauto. destructH.
    eapply path_to_elem in Hin2;eauto. destructH.
    assert ((h, 0 :: j1) ∈ ϕ) as Hinϕ.
    {
      clear Tsym.
      decide (h = u1).
      - subst u1. eapply path_contains_back in Hin0.
        specialize Tlj_eq1 as [Heq|Hentry];[exfalso|];subst.
        + eapply tag_depth_unroot2 in Hpath1;eauto with teq.
          destruct T. rewrite <-Tj_len in Hdep. lia.
        + eassumption.
      - eapply ex_entry with (p:=u1).
        + destruct n. destruct c. exact l.
        + eapply tag_depth_unroot2 in Hpath1 as Hdepu;eauto with teq.
          specialize Tlj_eq1 as [Heq|Hentry].
          * subst l1. intro N. rewrite Tj_len in Hdepu. rewrite Hdepu in Hdep.
            eapply loop_contains_deq_loop in N. eapply deq_loop_depth in N. lia.
          * contradict n0. destruct n. eapply eq_loop_same.
            -- split. 2: eapply loop_contains_deq_loop;eassumption.
               eapply deq_loop_depth_eq. 1: eapply loop_contains_deq_loop;eassumption.
               rewrite Hentry in Hdepu. cbn in Hdepu. erewrite Tj_len in Hdepu. lia.
            -- eapply loop_contains_loop_head;eauto.
            -- destruct H. eapply loop_contains_loop_head;eauto. admit.
        + eapply Hin0.
        + eapply tag_depth_unroot2 in Hpath1;eauto with teq.
        + setoid_rewrite <-teq_tag_eq1 at 3. 2:eapply T.
          eapply take_take_r. admit. admit.
        + rewrite Hdep. cbn. rewrite Tj_len. lia.
    }
    assert ((h, 0 :: j1) ∈ ϕ0) as Hinϕ0.
    {
      admit.
    }
    eapply Tdisj. 1,2: eapply prefix_incl;eauto.
Admitted.
