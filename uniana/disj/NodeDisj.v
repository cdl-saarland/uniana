Require Export TeqPaths HeadRewire ContractPath.
Require Import MaxPreSuffix Lia.

Section cfg.
  Context `{C : redCFG}.

  Infix "-->" := edge__P.
  Infix "-h>" := head_rewired_edge (at level 70).

  Lemma tpath_jeq_prefix u2 l2 q2 n2 j n1 r2
        (Tpath2 : TPath (u2, l2) (q2, n2 :: j) ((q2, n2 :: j) :: r2))
        (Tlj_eq2 : l2 = n1 :: j \/ l2 = 0 :: n1 :: j \/ loop_contains u2 q2)
        (Hlt : n1 < n2)
    : exists h r2',
      Prefix ((h,(S n1) :: j) :: r2') ((q2, n2 :: j) ::  r2)
      /\ innermost_loop h q2
      /\ forall x, x ∈ map fst r2' -> x <> h.
  Proof.
  Admitted.

  Lemma teq_jeq_prefix u1 u2 q1 q2 l1 l2 n1 n2 j r1 r2
        (T : TeqPaths u1 u2 q1 q2 l1 l2 (n1 :: j) (n2 :: j) r1 r2)
        (Hlt : n1 < n2)
    : exists h r2', Prefix (h :: map fst r2') (q2 :: map fst r2)
               /\ innermost_loop h q1
               /\ TeqPaths u1 u2 q1 h l1 l2 (n1 :: j) (n1 :: j) r1 r2'.
  Proof.
    destruct T.
  Admitted.

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
    eapply teq_jeq_prefix in Hlt;eauto.
    destructH.
    eapply teq_node_disj_hpath' in Hlt3;eauto.
    - destructH.
      do 2 eexists;split_conj;eauto.
      eapply prefix_incl in Hlt0.
      transitivity (h :: map fst r2');eauto.
    - left;split;destruct Hedge1,Hedge2;eauto;intro N.
      eapply teq_no_back;eauto using loop_contains_self.
    - right. exists q2.
      eapply tag_cons_exit in Hedge2. destructH.
      replace h with h0;eauto.
      eapply loop_head_eq_loop_eq.
      + destruct Hedge2. eapply loop_contains_loop_head;eauto.
      + destruct Hlt2. eapply loop_contains_loop_head;eauto.
      + eapply innermost_eq_loop in Hlt2. rewrite Hlt2.
        eapply eq_loop_exiting in Hedge2.
        rewrite Hedge2.
        symmetry. eapply Tloop.
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
      2: rewrite <-Dloop; eapply lj_eq2;eauto.
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
