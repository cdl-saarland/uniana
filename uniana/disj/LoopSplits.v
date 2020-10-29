Require Export GetSucc SplitsT DiamondPaths SplitsSound LastCommon.
Require Import Lia.

Lemma tl_eq `(C : redCFG) (h q1 q2 e1 e2 : Lab) (i j1 j2 : Tag) t1 t2
          (Hpath1 : TPath (root,start_tag) (e1,i) ((e1,i) :: (q1,j1) :: t1))
          (Hpath2 : TPath (root,start_tag) (e2,i) ((e2,i) :: (q2,j2) :: t2))
          (Hexit1 : exit_edge h q1 e1)
          (Hexit2 : exit_edge h q2 e2)
  : tl j1 = tl j2.
Proof.
  inversion Hpath1;inversion Hpath2;subst.
  replace q1 with (fst (q1,j1)) in Hexit1 by (cbn;auto).
  replace j1 with (snd (q1,j1)) by (cbn;auto).
  replace q2 with (fst (q2,j2)) in Hexit2 by (cbn;auto).
  replace j2 with (snd (q2,j2)) by (cbn;auto). destruct b;destruct b0.
  path_simpl' H0. path_simpl' H5. cbn.
  eapply tag_exit_iff' in H3.
  eapply tag_exit_iff' in H8.
  destruct H3,H8. auto.
  all: eexists;eauto.
Qed.

Lemma exiting_eq_loop `(C : redCFG) h q1 q2 e1 e2
      (Hexit1 : exit_edge h q1 e1)
      (Hexit2 : exit_edge h q2 e2)
  : eq_loop q1 q2.
Proof.
  transitivity h.
  - symmetry. eapply eq_loop_exiting;eauto.
  - eapply eq_loop_exiting;eauto.
Qed.

Lemma diamond_path_to_latch `(C : redCFG) s u1 u2 e1 e2 q1 q2 h k i l1 l2 n1 n2 r1 r2
      (D : DiamondPaths s u1 u2 e1 e2 q1 q2 k i l1 l2 (n1 :: i) (n2 :: i) r1 r2)
      (Hinner : innermost_loop h q1)
      (Hle : n1 < n2)
  : exists r2', TPath (q2, n2 :: i) (h,(S n2) :: i) r2'.
Proof.
  eapply innermost_eq_loop in Hinner as Heq.
  destruct Hinner as [Hloop Hdeq].
  rewrite Dloop in Hloop.
  destruct Hloop. destructH.
  eapply loop_cutting in H2.
  - destructH.
    eapply tcfg_path_acyclic with (i0:=n2 :: i) in H2.
    + destructH.
      exists ((h, S n2 :: i) :: t). econstructor;eauto.
      eapply tcfg_back_edge;eauto.
    + eapply back_edge_eq_loop in H0. rewrite H0. rewrite <-Dloop. symmetry. auto.
    + eapply j_len2;eauto.
  - intros. contradict H3.
    destr_r' π;subst. 1:contradiction.
    decide (h0 = h).
    + subst h0.
      rewrite rev_rcons. cbn. rewrite <-in_rev.
      path_simpl' H2. eapply In_rcons in H3. destruct H3;[subst;contradiction|]. eauto.
    + rewrite Dloop in Hdeq. eapply Hdeq in H.
      eapply path_from_elem in H3;eauto. destructH.
      eapply dom_loop_contains in H4 as Hdom;cycle 1.
      * eapply loop_contains_ledge;eauto.
      * contradict n. eapply eq_loop_same. 2,3: eapply loop_contains_loop_head;eauto.
        split;eapply loop_contains_deq_loop;eauto.
      * rewrite rev_rcons. cbn. rewrite <-in_rev. path_simpl' H2.
        dependent destruction H5.
        -- path_simpl' H4. contradiction.
        -- eapply rcons_eq1 in x. subst l'. eapply postfix_incl;eauto.
Qed.

Lemma diamond_path_to_same_exit `(C : redCFG) s u1 u2 h e1 e2 q1 q2 k i l1 l2 n1 n2 r1 r2
      (D : DiamondPaths s u1 u2 e1 e2 q1 q2 k i l1 l2 (n1 :: i) (n2 :: i) r1 r2)
      (Hexit : exit_edge h q1 e1)
      (Hle : n1 < n2)
  : exists r2', TPath (q2, n2 :: i) (e1, i) ((e1, i) :: r2') /\ Disjoint r1 r2'.
Proof.
  eapply eq_loop_exiting in Hexit as Heq.
  eapply exit_edge_innermost in Hexit as Hlatch1.
  eapply diamond_path_to_latch in D as Hlatch. 2,3:eauto. destructH.
  destruct Hlatch1.
  eapply loop_reachs_member in H.
  destruct H.
  eapply tcfg_path_acyclic with (i0:=S n2 :: i) in H. 2:eauto.
  2: { rewrite Heq. eapply j_len1 in D. cbn in *. lia. }
  destructH.
  eapply path_app' in H as Q;eauto.
  assert ((q1,S n2 :: i) -t> (e1,i)) as Hedge.
  { eapply tcfg_exit_edge. eexists. eauto. }
  eapply PathCons in Hedge. 2:eauto.
  eexists. split;[eauto|].
(*  rewrite <-app_nil_r at 1. eapply disjoint_app_app. 3,4: eapply Disjoint_nil1.
  2: eapply disjoint_subset;[reflexivity|eapply tl_incl |eauto].*)
  unfold Disjoint. intros. intro N.
  destruct a.
  eapply tag_depth_unroot_elem in N as Hdep;eauto.
  2: { setoid_rewrite <-j_len2. 2:eauto. cbn. reflexivity. }
  assert (deq_loop e h) as Hdeq.
  { rewrite Heq. eapply r1_incl_head_q;eauto. replace e with (fst (e,t0)) by (cbn;auto).
    eapply in_map;eauto. }
  enough (take_r (depth h) t0 ⊴ n1 :: i) as Htle.
  enough (n2 :: i ⊴ take_r (depth h) t0) as Hlet.
  enough (n1 :: i ◁ n2 :: i) as Hlt.
  - eapply tagle_taglt_trans in Hlt;eauto.
    eapply taglt_tagle_trans in Hlt;eauto.
    eapply Taglt_irrefl;eauto.
  - econstructor. lia.
  - eapply path_to_elem in N as Hϕ;eauto. destructH.
    eapply tagle_monotone with (h0:=h) in Hϕ0;eauto.
    + setoid_rewrite take_r_geq in Hϕ0 at 1;eauto.
      rewrite Heq. setoid_rewrite <-j_len1. 2:eapply D. cbn. lia.
    + setoid_rewrite <-j_len2. 2:eauto. reflexivity.
    + rewrite Heq. rewrite Dloop. reflexivity.
  - specialize Dpath1 as Dpath.
    specialize Dqj1 as Dqj.
    destruct r1;[contradiction|].
    inv_path Dpath. destruct p.
    cbn in Dqj. inv Dqj.
    eapply path_from_elem in H1 as Hϕ;eauto. destructH.
    eapply tagle_monotone with (h0:=h) in Hϕ0;eauto.
    + setoid_rewrite take_r_geq in Hϕ0 at 2;eauto.
      rewrite Heq. setoid_rewrite <-j_len1;eauto.
    + rewrite Heq. reflexivity.
Qed.

Theorem lc_disj_exits_lsplits' `{redCFG}
          (s e1 e2 q1 q2 h : Lab) (i k : Tag) (t1 t2 : list Coord) (n1 n2 : nat)
          (Hlc : last_common ((q1,n1 :: i) :: t1) ((q2,n2 :: i) :: t2) (s,k))
          (Hexit1 : exit_edge h q1 e1)
          (Hexit2 : exit_edge h q2 e2)
          (Hpath1 : TPath (root,start_tag) (e1,i) ((e1,i) :: (q1,n1 :: i) :: t1))
          (Hpath2 : TPath (root,start_tag) (e2,i) ((e2,i) :: (q2,n2 :: i) :: t2))
          (Hneq : n1 < n2)
  : s ∈ splitsT e1.
Proof.
  destruct Hlc. destructH.
  rename x into r1.
  rename l2' into r2.
  remember (hd (e1,i) (rev r1)) as ul1.
  remember (hd (e2,i) (rev r2)) as ul2.
  destruct ul1 as [u1 l1].
  destruct ul2 as [u2 l2].
  eapply tag_depth' in Hpath1 as Hdepe1.
  eapply tag_depth' in Hpath2 as Hdepe2.
  assert (DiamondPaths s u1 u2 e1 e2 q1 q2 k i l1 l2 (n1 :: i) (n2 :: i) r1 r2) as D.
  {
    inv_path Hpath1. inv_path Hpath2.
    eapply postfix_path in H1;eauto.
    eapply postfix_path in H0;eauto.
    econstructor.
    - destr_r' r1;subst.
      + cbn in Hequl1. inv Hequl1. cbn in H1. inv_path H1. eauto.
      + rewrite rev_rcons in Hequl1. cbn in Hequl1. subst x1.
        eapply path_nlrcons_edge;eauto.
    - destr_r' r2;subst.
      + cbn in Hequl2. inv Hequl2. cbn in H0. inv_path H0. eauto.
      + rewrite rev_rcons in Hequl2. cbn in Hequl2. subst x1.
        eapply path_nlrcons_edge;eauto.
    - destr_r' r1;subst.
      + cbn in Hequl1. inv Hequl1. econstructor.
      + eapply PathCons;eauto.
        rewrite rev_rcons in Hequl1. cbn in Hequl1. subst x1.
        eapply path_rcons_rinv;eauto.
    - destr_r' r2;subst.
      + cbn in Hequl2. inv Hequl2. econstructor.
      + eapply PathCons;eauto.
        rewrite rev_rcons in Hequl2. cbn in Hequl2. subst x1.
        eapply path_rcons_rinv;eauto.
    - destruct r1; cbn; cbn in H1; inv_path H1; eauto.
    - destruct r2; cbn; cbn in H0; inv_path H0; eauto.
    - auto.
    - eapply exiting_eq_loop;eauto.
    - eapply tag_depth_unroot2;eauto. eapply tag_depth';eauto.
  }
  inv_path Hpath1. inv_path Hpath2.
  eapply Dpath_sq2 in D as Hϕ2.
  eapply diamond_path_to_same_exit in D as Hlatch;eauto.
  destructH. destruct D.
  eapply path_app' in Hlatch0 as Hlatch3;eauto.
  eapply splitsT_spec. (*
  *)
  destruct r2.
  - cbn in Dqj2. inv Dqj2.
    destr_r' r2';subst.
    { eapply path_single in Hlatch0. inv Hlatch0. inv H9. exfalso. eapply list_cycle;eauto. }
    rewrite <-cons_rcons_assoc in Hlatch0. unfold TPath in Hlatch0. path_simpl' Hlatch0.
    rewrite cons_rcons_assoc in Hlatch0.
    eapply path_rcons_inv' in Hlatch0. destructH. destruct p.
    do 8 eexists. split_conj.
    1: eapply Dpath1. 1: eapply Hlatch2. 2,3,5:eauto.
    + cbn. eapply disjoint_subset. 1: reflexivity. 2: eapply Hlatch1.
      intros y Hy. eapply In_rcons;eauto.
    + cbn. left. destruct r1. 2:congruence. cbn in Dqj1. inv Dqj1. lia.
  - cbn in Hlatch3.
    rewrite app_assoc in Hlatch3.
    eapply path_rcons_inv' in Hlatch3. destructH. destruct p0.
    do 8 eexists. split_conj.
    1: eapply Dpath1. 1: eapply Hlatch2. 2,3,5:eauto.
    + cbn. rewrite <-app_nil_r at 1. eapply disjoint_app_app. 3,4:eapply Disjoint_nil1.
      1,2:eauto. eapply disjoint_subset. 1:reflexivity. 2:eapply Ddisj.
      intros y Hy. right;eauto.
    + cbn. right.
      destruct r2';cbn in *.
      * eapply path_single in Hlatch0. inv Hlatch0. inv H9. exfalso. eapply list_cycle;eauto.
      * congruence.
Qed.

Theorem lc_disj_exits_lsplits `{redCFG}
          (s e1 e2 q1 q2 h : Lab) (i k : Tag) (t1 t2 : list Coord) j1 j2
          (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
          (Hexit1 : exit_edge h q1 e1)
          (Hexit2 : exit_edge h q2 e2)
          (Hpath1 : TPath (root,start_tag) (e1,i) ((e1,i) :: (q1,j1) :: t1))
          (Hpath2 : TPath (root,start_tag) (e2,i) ((e2,i) :: (q2,j2) :: t2))
          (Hneq : j1 <> j2)
  : s ∈ splitsT e1 \/ s ∈ splitsT e2.
Proof.
  inv_path Hpath1.
  inv_path Hpath2.
  eapply tag_exit_eq' in Hexit1 as Htexit1;eauto.
  eapply tag_exit_eq' in Hexit2 as Htexit2;eauto.
  destruct Htexit1 as [n1 Htexit1].
  destruct Htexit2 as [n2 Htexit2].
  subst j1 j2.
  specialize (Nat.lt_total n1 n2) as Hlt.
  destruct Hlt as [Hlt|[Heq|Hlt]].
  - left. eapply lc_disj_exits_lsplits'; eauto.
  - subst. contradiction.
  - right. eapply last_common_sym in Hlc.
    eapply lc_disj_exits_lsplits';eauto.
Qed.

Corollary lc_disj_exit_lsplits `{redCFG} (s e q1 q2 h : Lab) (i j1 j2 k : Tag) (t1 t2 : list Coord)
          (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
          (Hexit1 : exit_edge h q1 e)
          (Hexit2 : exit_edge h q2 e)
          (Hpath1 : TPath (root,start_tag) (e,i) ((e,i) :: (q1, j1) :: t1))
          (Hpath2 : TPath (root,start_tag) (e,i) ((e,i) :: (q2, j2) :: t2))
          (Hneq : j1 <> j2)
  : s ∈ splitsT e.
Proof.
  eapply lc_disj_exits_lsplits in Hlc;eauto.
  tauto.
Qed.
