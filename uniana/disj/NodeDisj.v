Require Export TeqPaths HeadRewire ContractPath.
Require Import MaxPreSuffix Lia CncLoop.

Section cfg.
  Context `{C : redCFG}.

  Infix "-->" := edge__P.
  Infix "-h>" := head_rewired_edge (at level 70).

  Lemma depth_loop_contains p
    : depth p > 0 -> exists h, loop_contains h p.
  Proof.
    intros.
    unfold depth in H.
    destruct (filter (DecPred (fun h : Lab => loop_contains h p)) (elem Lab)) eqn:E. 1:cbn in H;lia.
    cbn in H. exists e.
    assert (e ∈ (e :: l)) by (left;auto). rewrite <-E in H0.
    eapply in_filter_iff in H0. destruct H0. cbn in *. assumption.
  Qed.

  Lemma tpath_jeq_prefix u2 l2 q2 n2 j n1 r2
        (Hdep : | l2 | = depth u2)
        (Hdequ : deq_loop u2 q2)
        (Tpath2 : TPath (u2, l2) (q2, n2 :: j) ((q2, n2 :: j) :: r2))
        (Tlj_eq2 : l2 = n1 :: j /\ ~ loop_head u2
                   \/ (l2 = 0 :: n1 :: j /\ loop_head u2)
                   \/ (loop_contains u2 q2 /\ l2 = S n1 :: j))
        (Hlt : n1 < n2)
    : exists h r2',
      Prefix ((h,(S n1) :: j) :: r2') ((q2, n2 :: j) ::  r2)
      /\ innermost_loop h q2
      /\ forall x, x ∈ map fst r2' -> x <> h.
  Proof.
    eapply tag_depth_unroot in Tpath2 as Hdepq;eauto.
    assert (exists h, innermost_loop h q2) as Hinner.
    { cbn in Hdepq. specialize depth_loop_contains as Hloop. exploit Hloop. lia.
      destructH. eapply loop_contains_innermost;eauto. }
    destruct Hinner as [h Hinner]. cbn in Hinner.
    exists h.
    copy Hinner Hloop.
    destruct Hloop as [Hloop Hdeq].
    specialize (tcfg_reachability Hdep) as Hreach. destructH.
    eapply path_app' in Tpath2 as Hrooted;eauto.
    eapply loop_tag_dom with (j0:= S n1 :: j) in Hloop;eauto.
    - eapply in_app_or in Hloop. destruct Hloop.
      + eapply path_to_elem in H;eauto. destructH.
        exists (tl ϕ). split_conj.
        * destruct ϕ;[inv H0|]. cbn. path_simpl' H0. eauto.
        * assumption.
        * intros. intro N. subst x. eapply in_fst in H.
          destruct ϕ;[inv H0|]. path_simpl' H0. cbn in H. destructH.
          decide (loop_contains u2 q2).
          {
            destruct Tlj_eq2 as [Q|[Q|Q]];destructH.
            - contradict Q1. eapply loop_contains_loop_head;eauto.
            - subst l2. eapply innermost_eq_loop in Hinner. eapply loop_contains_deq_loop in l.
              eapply deq_loop_depth in l. cbn in Hdep,Hdepq. lia.
            - subst l2.
              replace u2 with h in *.
              { destruct ϕ. 1:contradiction. eapply tcfg_fresh in H0.
                - eapply Taglt_irrefl;eauto.
                - eauto.
                - cbn. lia.
              }
              eapply Hdeq in l as l'. eapply loop_contains_deq_loop in l'.
              eapply eq_loop_same.
              + split;auto.
                eapply deq_loop_depth_eq;eauto. rewrite <-Hdep. eapply innermost_eq_loop in Hinner.
                rewrite Hinner. rewrite <-Hdepq. cbn. reflexivity.
              + destruct Hinner. eapply loop_contains_loop_head;eauto.
              + eapply loop_contains_loop_head;eauto.
          }
          inv_path Hreach.
          { destruct Tlj_eq2 as [Q|[Q|Q]]. all: unfold start_tag in *;try destructH; congruence. }
          rename H2 into Hbase. destruct x.
          rename H0 into Hjump.
          enough (b ◁ S n1 :: j) as HSb.
          enough (n1 :: j ◁ b) as Hb.
          -- dependent destruction HSb.
             ++ dependent destruction Hb.
                ** lia.
                ** eapply Taglt_irrefl;eauto.
             ++ dependent destruction Hb.
                ** eapply Taglt_irrefl;eauto.
                ** eapply Taglt_irrefl. transitivity i;eauto.
          -- eapply path_to_elem with (r:=(h,b)) in Hjump;eauto. destructH.
             eapply path_from_elem with (r:=(h, n1 :: j)) in Hbase;eauto.
             2: {
               eapply PathCons in H3;eauto.
               eapply loop_tag_dom in H3.
               - destruct H3;[|eassumption]. inv H0. destruct Hinner. contradiction.
               - destruct Hinner;eauto.
               - eapply innermost_eq_loop in Hinner. rewrite Hinner.
                 destruct Tlj_eq2 as [Q|[Q|Q]];destructH;subst.
                 + rewrite take_r_geq. 2: rewrite <-Hdepq;eauto.
                   unfold sub_tag.
                   split_conj;cbn;eauto;lia.
                 + rewrite take_r_cons_drop. 2: rewrite <-Hdepq;eauto.
                   rewrite take_r_geq. 2: rewrite <-Hdepq;eauto.
                   unfold sub_tag.
                   split_conj;cbn;eauto;lia.
                 + rewrite take_r_geq. 2: rewrite <-Hdepq;eauto.
                   unfold sub_tag.
                   split_conj;cbn;eauto;lia.
               - eapply innermost_eq_loop in Hinner. rewrite Hinner. eauto.
             }
             destructH.
             eapply tcfg_fresh.
             ++ eapply path_app;eauto.
             ++ eapply innermost_eq_loop in Hinner. rewrite Hinner. cbn. cbn in Hdepq. eauto.
             ++ destruct ϕ0;[inv Hjump0|];destruct ϕ1;[inv Hbase0|]. cbn. rewrite app_length. cbn. lia.
          -- inv_path Hjump. 1:contradiction.
             eapply path_from_elem with (r:=(h,b)) in H0;eauto. destructH.
             eapply PathCons in H2;eauto.
             eapply tcfg_fresh;eauto.
             ++ eapply path_to_elem with (r:=(h,b)) in Tpath2. destructH.
                eapply tag_depth_unroot in Tpath0;eauto.
                eapply prefix_incl;eauto.
             ++ destruct ϕ0;[inv H4|]. cbn. lia.
      + exfalso.
        destruct t;cbn in H;[contradiction|].
        cbn in Hrooted.
        destruct t;[cbn in Hrooted,H;contradiction|].
        unfold TPath in Hreach. path_simpl' Hreach.
        inv_path Hreach. destruct c0.
        eapply path_from_elem in H;eauto. destructH.
        eapply PathCons in H1;eauto.
        copy Hinner Hinner'.
        eapply innermost_eq_loop in Hinner. copy H1 H1path.
        eapply tagle_monotone in H1;cycle 1.
        * rewrite Hinner. rewrite <-Hdepq. cbn. reflexivity.
        * reflexivity.
        * rewrite Hinner. eauto.
        * reflexivity.
        * rewrite take_r_geq in H1. 2: { rewrite Hinner. rewrite <-Hdepq. cbn. eauto. }
          destruct Tlj_eq2 as [Q|[Q|Q]];destructH;subst.
          -- rewrite take_r_geq in H1. 2: { rewrite Hinner. rewrite <-Hdepq. cbn. eauto. }
             destruct H1.
             ++ dependent destruction H. lia. eapply Taglt_irrefl;eauto.
             ++ inv H. lia.
          -- rewrite take_r_cons_drop in H1. 2: { rewrite Hinner. rewrite <-Hdepq. cbn. eauto. }
             rewrite take_r_geq in H1. 2: { rewrite Hinner. rewrite <-Hdepq. cbn. eauto. }
             destruct H1.
             ++ dependent destruction H. lia. eapply Taglt_irrefl;eauto.
             ++ inv H. lia.
          -- replace u2 with h in *.
             2: {
              eapply Hdeq in Q0 as l'. eapply loop_contains_deq_loop in l'.
              eapply eq_loop_same.
              + split;auto.
                eapply deq_loop_depth_eq;eauto. rewrite <-Hdep.
                rewrite Hinner. rewrite <-Hdepq. cbn. reflexivity.
              + destruct Hinner'. eapply loop_contains_loop_head;eauto.
              + eapply loop_contains_loop_head;eauto.
             }
             eapply tcfg_fresh in H1path.
             ++ eapply Taglt_irrefl;eauto.
             ++ rewrite Hinner. rewrite <-Hdepq. cbn. reflexivity.
             ++ destruct ϕ;[inv H2|]. cbn. lia.
    - eapply innermost_eq_loop in Hinner. rewrite Hinner.
      rewrite take_r_geq. 2: rewrite Hdepq;eauto.
      unfold sub_tag.
      split_conj;cbn;eauto;lia.
    - eapply innermost_eq_loop in Hinner. rewrite Hinner. rewrite <-Hdepq. cbn. reflexivity.
  Qed.

  Lemma teq_jeq_prefix u1 u2 q1 q2 l1 l2 n1 n2 j r1 r2
        (T : TeqPaths u1 u2 q1 q2 l1 l2 (n1 :: j) (n2 :: j) r1 r2)
        (Hnloop : ~ loop_contains u2 q1)
        (Hlt : n1 < n2)
    : exists h q2' r2', Prefix (h :: q2' :: map fst r2') (q2 :: map fst r2)
               /\ innermost_loop h q1
               /\ TeqPaths u1 u2 q1 q2' l1 l2 (n1 :: j) (n1 :: j) r1 r2'
               /\ (q2',n1 :: j) -t> (h, S n1 :: j).
  Proof.
    eapply tpath_jeq_prefix in Hlt as Hjeq.
    4: eapply Tpath2.
    3: rewrite <-Tloop;eapply teq_u2_deq_q;eauto.
    2: eapply teq_l_len2;eauto.
    - destructH.
      destruct r2'.
      {
        exfalso. eapply Hnloop.
        eapply prefix_singleton in Hjeq0. 2: eapply Tpath2. inv Hjeq0.
        destruct Hjeq2. rewrite Tloop. assumption.
      }
      destruct p.
      exists h, e, r2'.
      replace l with (n1 :: j) in *.
      2: {
        eapply path_prefix_path in Hjeq0. 3: eapply Tpath2. 2:eauto.
        inv_path Hjeq0. eapply tcfg_edge_destruct' in H0.
        destruct H0 as [H0|[H0|[H0|H0]]]. all: destruct H0 as [Htag Hedge].
        - exfalso. eapply basic_edge_no_loop2;eauto. destruct Hjeq2.
          eapply loop_contains_loop_head;eauto.
        - congruence.
        - destruct l;cbn in Htag;[congruence|]. inv Htag. reflexivity.
        - exfalso. destruct Hedge. eapply no_exit_head;eauto.
          destruct Hjeq2. eapply loop_contains_loop_head;eauto.
      }
      assert ((e, n1 :: j) -t> (h, S n1 :: j)) as Heedge.
      {
        eapply path_prefix_path in Hjeq0. 3: eapply Tpath2. 2:eauto. inv_path Hjeq0. eauto.
      }
      assert (eq_loop q1 e) as Heq.
      {
        destruct T.
        eapply tag_back_edge_iff in Heedge. destruct Heedge as [Heedge _]. cbn in Heedge.
        exploit Heedge. eapply back_edge_eq_loop in Heedge. rewrite Heedge.
        eapply innermost_eq_loop in Hjeq2. rewrite Hjeq2. eauto.
      }
      split_conj.
      + eapply prefix_map_fst in Hjeq0. cbn in Hjeq0. eauto.
      + rewrite Tloop. eauto.
      + destruct T.
        econstructor. 5-9:now eauto.
        * eapply Tpath1.
        * eapply path_prefix_path. 1: eauto. 1: eapply Tpath2. eapply prefix_cons;eauto.
        * eapply disjoint_subset. 1:reflexivity.
          2: eapply Tdisj.
          eapply prefix_cons in Hjeq0;eauto;eapply prefix_incl;eauto.
        * eauto.
        * destructH. eapply prefix_eq in Hjeq0 as Hjeq4. destructH.
          eapply postfix_eq in TS3. destructH.
          do 4 eexists. split_conj;cycle 1.
          -- eauto.
          -- eapply postfix_eq.
             setoid_rewrite Hjeq4 in TS3.
             exists l2'0. reflexivity.
          -- cbn.
             eapply SplitPaths_Prefix;eauto.
             eapply prefix_eq. setoid_rewrite Hjeq4 in TS3.
             rewrite app_cons_rcons in TS3. rewrite <-app_assoc in TS3.
             eexists. eauto.
      + eauto.
    - copy T T'. destruct T.
      destruct Tlj_eq2 as [Q|[Q|Q]].
      + left. split;eauto. contradict Hnloop. eapply teq_l_len2 in T' as Hlen.
        subst l2. rewrite Tj_len in Hlen. eapply deq_loop_depth_eq in Hlen;eauto.
        * eapply Hlen. eapply loop_contains_self;eauto.
        * eapply teq_u2_deq_q;eauto.
      + right. left. eauto.
      + exfalso. contradiction.
  Qed.

  Lemma node_disj
        `(D : DiamondPaths)
        (Hjeq : j1 = j2)
        (Hdeq : deq_loop q1 s)
    : Disjoint (map fst r1) (map fst r2).
  Proof.
    subst j2.
    destruct r1,r2.
    1-3: cbn; firstorder.
    diamond_subst_qj D.
    eapply teq_node_disj;eauto. eapply diamond_teq.
    - eassumption.
    - reflexivity.
    - exact D.
  Qed.

  Ltac to_cons_path H :=
    lazymatch type of H with
    | Path _ _ ?q ?r
      => let Q := fresh "Q" in
        let r2 := fresh "r" in
        eapply path_to_cons_path in H as Q;
        destruct Q as [r2 Q];
        subst r;
        rename r2 into r
    end.

  Lemma teq_node_disj_hpath' u1 u2 q1 q2 l1 l2 j r1 r2
        (T : TeqPaths u1 u2 q1 q2 l1 l2 j j (r1) (r2))
        p1 p2
        (Hedge1 : q1 -h> p1)
        (Hedge2 : q2 -h> p2)
    : exists r1' r2', HPath u1 p1 (p1 :: q1 :: r1')
                 /\ HPath u2 p2 (p2 :: q2 :: r2')
                 /\ Disjoint (q1 :: r1') (q2 :: r2')
                 /\ (q1 :: r1') ⊆ (q1 :: map fst r1)
                 /\ (q2 :: r2') ⊆ (q2 :: map fst r2).
  Proof.
    eapply teq_node_disj in T as Hndisj;eauto.
    cbn in Hndisj.
    copy T T'.
    destruct T.
    eapply TPath_CPath in Tpath1.  cbn in Tpath1.
    eapply TPath_CPath in Tpath2. cbn in Tpath2.
    eapply contract_cpath' in Tpath1.
    eapply contract_cpath' in Tpath2.
    2: { rewrite <-Tloop. eapply teq_u2_deq_q;eauto. }
    3: eauto with teq.
    2,3: cbn.
    3: intros; eapply teq_no_back;eauto.
    2: intros; rewrite <-Tloop; eapply teq_no_back2;eauto.
    repeat destructH.
    unfold HPath in *.
    to_cons_path Tpath2.
    to_cons_path Tpath0.
    exists ϕ0, ϕ.
    split_conj;eauto.
    1,2: econstructor;eauto.
    eapply disjoint_subset;eauto.
  Qed.

  Lemma teq_node_disj_hpath u1 u2 q1 q2 l1 l2 j r1 r2
        (T : TeqPaths u1 u2 q1 q2 l1 l2 j j (r1) (r2))
        p1 p2 i
        (Hedge1 : (q1,j) -t> (p1,i))
        (Hedge2 : (q2,j) -t> (p2,i))
    : exists r1' r2', HPath u1 p1 (p1 :: q1 :: r1')
                 /\ HPath u2 p2 (p2 :: q2 :: r2')
                 /\ Disjoint (q1 :: r1') (q2 :: r2')
                 /\ (q1 :: r1') ⊆ (q1 :: map fst r1)
                 /\ (q2 :: r2') ⊆ (q2 :: map fst r2).
  Proof.
    eapply teq_node_disj_hpath';eauto.
    1,2: left;split;destruct Hedge1,Hedge2;eauto.
    1,2: intro N.
    - eapply teq_no_back;eauto using loop_contains_self.
    - eapply teq_no_back2;eauto. rewrite Tloop.
      eapply loop_contains_self;eauto.
  Qed.

  Lemma teq_node_disj_prefix_hpath u1 u2 q1 q2 l1 l2 r1 r2 n1 n2 i
        (T : TeqPaths u1 u2 q1 q2 l1 l2 (n1 :: i) (n2 :: i) (r1) (r2))
        p1 p2
        (Hedge1 : (q1,n1 :: i) -t> (p1,i))
        (Hedge2 : (q2,n2 :: i) -t> (p2,i))
        (Hlt : n1 < n2)
    : exists r1' r2', HPath u1 p1 (p1 :: r1')
                 /\ HPath u2 p2 (p2 :: r2')
                 /\ Disjoint (r1') (r2')
                 /\ (r1') ⊆ (q1 :: map fst r1)
                 /\ (r2') ⊆ (q2 :: map fst r2).
  Proof.
    decide (loop_contains u2 q1).
    {
      copy T T'.
      destruct T.
      eapply TPath_CPath in Tpath1. cbn in Tpath1.
      eapply contract_cpath' in Tpath1 as Hpath1.
      2: eapply teq_u1_deq_q;eauto.
      2: intros;eapply teq_no_back;eauto.
      destructH.
      exists ϕ, ([u2]).
      split_conj.
      - econstructor;eauto. eapply tag_cons_exit in Hedge1. destructH.
        decide (loop_head q1).
        + eapply exit_edge_innermost in Hedge1 as Hinner.
          replace h with q1 in * by (eapply innermost_loop_head;eauto).
          right. eexists;eauto.
        + left. destruct Hedge1. destruct H0. split;eauto.
      - econstructor. 1:econstructor.
        eapply tag_cons_exit in Hedge2. destructH. right.
        replace h with u2 in *.
        + eexists;eauto.
        + eapply innermost_unique.
          * split;eauto. eapply teq_u2_deq_q;eauto.
          * rewrite Tloop. eapply exit_edge_innermost;eauto.
      - eapply disjoint_subset. 1:eassumption. 1:reflexivity.
        eapply disjoint_cons2. split;[|eapply Disjoint_nil2].
        intro N. eapply teq_no_back;eauto.
      - assumption.
      - eapply path_contains_back in Tpath2. eapply in_map with (f:=fst) in Tpath2.
        cbn in Tpath2. eauto.
    }
    eapply teq_jeq_prefix in Hlt;eauto.
    destructH.
    eapply teq_node_disj_hpath' in Hlt1.
    3: { eapply tag_back_edge_iff in Hlt4. cbn in Hlt4. destruct Hlt4 as [Hlt4 _]. exploit Hlt4.
         left. split;[destruct Hlt4;eauto|]. eapply back_edge_src_no_loop_head;eauto. }
    - destructH.
      exists (q1 :: r1'), (h :: q2' :: r2'0).
      split_conj;eauto.
      + eapply PathCons;eauto. right. eexists. eapply tag_cons_exit in Hedge2.
        destructH. eapply exit_edge_innermost in Hedge2 as Hinner2.
        rewrite <-Tloop in Hinner2.
        eapply innermost_unique in Hinner2. 2: eapply Hlt2. subst h0. eapply Hedge2.
      + eapply prefix_incl in Hlt0. eapply disjoint_cons2. split;auto.
        intro N. eapply teq_no_back. 1:eauto. 2: destruct Hlt2;eauto.
        eapply Hlt6 in N. auto.
      + eapply prefix_incl in Hlt0.
        eapply incl_lcons. split.
        * eapply Hlt0;eauto.
        * rewrite Hlt8. rewrite incl_lcons in Hlt0. destruct Hlt0. eauto.
    - left;split;destruct Hedge1,Hedge2;eauto;intro N.
      eapply teq_no_back;eauto using loop_contains_self.
  Qed.

  Lemma node_disj_prefix_hpath s u1 u2 p1 p2 q1 q2 k i l1 l2 n1 n2 r1 r2
        (D : DiamondPaths s u1 u2 p1 p2 q1 q2 k i l1 l2 (n1 :: i) (n2 :: i) r1 r2)
        (Hdeq : deq_loop q1 s)
        (Hlt : n1 < n2)
    : exists r1' r2', HPath u1 p1 (p1 :: r1')
                 /\ HPath u2 p2 (p2 :: r2')
                 /\ Disjoint (r1') (r2')
                 /\ r1' ⊆ map fst r1
                 /\ r2' ⊆ map fst r2.
  Proof.
    destruct r1,r2.
    - exfalso.
      destruct D. cbn in *. inv Dqj1; inv Dqj2. lia.
    - copy D D'.
      destruct D'.
      cbn in Dqj1.
      eapply path_single in Dpath1. destruct Dpath1 as [Dpath1 _]. inv Dpath1. inv Dqj1.
      cbn in Dqj2. subst p.
      inv_path Dpath2.
      eapply tpath_jeq_prefix in H as Hpre;eauto.
      2: eapply u_len2;eauto.
      2: rewrite <-Dloop.
      3: {
        eapply lj_eq2 in D as Deq;eauto.
        2: eapply le_cons_tagle;lia.
        eapply tcfg_edge_destruct' in Dsk2.
        destruct Dsk2 as [Dsk2|[Dsk2|[Dsk2|Dsk2]]].
        all: destruct Dsk2 as [Htag Hedge].
        - left. split;eauto. intro N. eapply basic_edge_no_loop2;eauto.
        - right. left. split;eauto. destruct Hedge. eauto.
        - cbn in Htag. right. right. split;eauto. rewrite <-Dloop. eapply loop_contains_ledge;eauto.
        - cbn in Htag. subst.
          destruct Deq as [Deq|[Deq|Deq]];exfalso.
          + eapply list_cycle;eauto.
          + destruct Deq. eapply list_cycle2;eauto.
          + destruct Hedge. eapply no_exit_head;eauto. eapply loop_contains_loop_head;eauto.
      }
      2: { eapply u2_deq_q;eauto. intro N. congruence. }
(*        eapply le_cons_tagle;lia.*)
      destructH.
      eapply path_prefix_path in H;eauto.
      eapply TPath_CPath in H. cbn in H.
      eapply contract_cpath' in H.
      + destructH.
        exists [], ϕ.
        split_conj;eauto.
        * econstructor.
        * econstructor;eauto.
          eapply tag_cons_exit in H0. destructH.
          replace h0 with h in H0.
          -- right. eexists;eauto.
          -- eapply loop_head_eq_loop_eq.
             1,2: destruct Hpre2,H0;eauto using loop_contains_loop_head.
             eapply eq_loop_exiting in H0. rewrite H0. eapply innermost_eq_loop in Hpre2.
             rewrite Hpre2. reflexivity.
        * firstorder 0.
        * cbn. eapply prefix_incl in Hpre0. eapply incl_map with (f:=fst) in Hpre0.
          cbn in Hpre0. transitivity (h :: map fst r2');eauto.
      + eapply innermost_eq_loop in Hpre2. rewrite Hpre2.
        rewrite <-Dloop. eapply u2_deq_q;eauto. congruence.
      + cbn. intros. intro N. eapply Hpre3;eauto.
        eapply loop_head_eq_loop_eq;[|destruct Hpre2|];eauto using loop_contains_loop_head.
        split.
        * eapply innermost_eq_loop in Hpre2. rewrite Hpre2. rewrite <-Dloop.
          eapply r2_incl_head_q;eauto.
          eapply prefix_incl in Hpre0.
          eapply incl_map with (f:=fst) in Hpre0. cbn in Hpre0. cbn. eapply Hpre0. right. auto.
        * eapply loop_contains_deq_loop;eauto.
    - exfalso.
      copy D D'.
      destruct D.
      cbn in Dqj1,Dqj2.
      subst p. inv Dqj2.
      eapply path_single in Dpath2. destruct Dpath2 as [Dpath2 _]. inv Dpath2.
      inv_path Dpath1.
      eapply path_rcons in Dsk1;eauto.
      eapply tagle_monotone_eq_loop in Dsk1.
      + eapply lt_cons_ntagle;eauto.
      + eapply j_len2;eauto.
      + cbn. rewrite map_rcons. cbn. intros. rewrite In_rcons in H1.
        destruct H1 as [H1|[H1|H1]]. 1,2: subst x0.
        * destruct Dloop;eauto.
        * reflexivity.
        * rewrite <-Dloop. eapply r1_incl_head_q;eauto. cbn. right. eauto.
      + symmetry. eauto.
    - diamond_subst_qj D. eapply diamond_teq in D as T;eauto.
      2: eapply le_cons_tagle;lia.
      eapply teq_node_disj_prefix_hpath in T;eauto.
      1,2: destruct D;inv_path Dpath1; inv_path Dpath2;eauto.
  Qed.

  Lemma node_disj_hpath s p1 p2 u1 u2 q1 q2 k i l1 l2 j1 j2 r1 r2
        (D : DiamondPaths s u1 u2 p1 p2 q1 q2 k i l1 l2 j1 j2 r1 r2)
        (Hdeq : deq_loop q1 s)
        (Hjeq : j1 = j2)
    : exists r1' r2', HPath u1 p1 (p1 :: r1')
                 /\ HPath u2 p2 (p2 :: r2')
                 /\ Disjoint r1' r2'
                 /\ r1' ⊆ map fst r1
                 /\ r2' ⊆ map fst r2.
  Proof.
    destruct r1,r2.
    - exists [],[].
      destruct D.
      eapply path_single in Dpath1. destruct Dpath1. inv H.
      eapply path_single in Dpath2. destruct Dpath2. inv H.
      split_conj. 1,2: econstructor.
      all: cbn;firstorder 0.
    - copy D D'. destruct D.
      eapply path_single in Dpath1. destruct Dpath1. inv H.
      eapply TPath_CPath in Dpath2. destruct p as [q j]. cbn in Dpath2. inv_path Dpath2.
      cbn in Dqj1, Dqj2. inv Dqj1. inv Dqj2.
      eapply contract_cpath' in H.
      + cbn in Dpath2. destructH.
        exists [], ϕ.
        split_conj. 3,4: cbn;firstorder 0.
        * econstructor.
        * econstructor;eauto. unfold head_rewired_edge. left;split;eauto.
          intros N. eapply no_back2;eauto. cbn. left;eauto. rewrite Dloop.
          eapply loop_contains_self;eauto.
        * cbn. eassumption.
      + rewrite <-Dloop. eapply u2_deq_q; eauto. congruence.
      + cbn. intros. rewrite <-Dloop. eapply no_back2;eauto.
        right. cbn. eauto.
    - copy D D'. destruct D.
      eapply path_single in Dpath2. destruct Dpath2. inv H.
      eapply TPath_CPath in Dpath1. destruct p as [q j]. cbn in Dpath1. inv_path Dpath1.
      cbn in Dqj1, Dqj2. inv Dqj1. inv Dqj2.
      eapply contract_cpath' in H.
      + cbn in Dpath1. destructH.
        exists ϕ, [].
        split_conj. 3,5: cbn;firstorder 0.
        * econstructor;eauto. unfold head_rewired_edge. left;split;eauto.
          intros N. eapply no_back;eauto;[reflexivity| |]. cbn. left;eauto.
          eapply loop_contains_self;eauto.
        * econstructor.
        * cbn. eassumption.
    + eapply u1_deq_q; eauto. congruence.
    + cbn. intros. eapply no_back;eauto;[reflexivity|].
      right. cbn. auto.
    - diamond_subst_qj D. subst j2.
      eapply diamond_teq in D as T;eauto;[|reflexivity].
      destruct D.
      eapply teq_node_disj_hpath in T.
      2,3: inv_path Dpath1;inv_path Dpath2;eauto.
      destructH.
      eexists;eexists;split_conj;eauto.
  Qed.

End cfg.
