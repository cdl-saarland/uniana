Require Export GetSucc SplitsT DiamondPaths SplitsSound LastCommon.


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

Lemma exited_eq_loop `(C : redCFG) h q1 q2 e1 e2
      (Hexit1 : exit_edge h q1 e1)
      (Hexit2 : exit_edge h q2 e2)
  : eq_loop e1 e2.
Proof.
Admitted. (*
  transitivity h.
  - symmetry. eapply eq_loop_exiting;eauto.
  - eapply eq_loop_exiting;eauto.
Qed.
           *)

Lemma diamond_path_to_latch `(C : redCFG) s u1 u2 e1 e2 q1 q2 k i l1 l2 n1 n2 r1 r2
      (D : DiamondPaths s u1 u2 e1 e2 q1 q2 k i l1 l2 (n1 :: i) (n2 :: i) r1 r2)
      (Hle : n1 <= n2)
  : exists h r2', TPath (q2, n2 :: i) (h,(S n1) :: i) r2' /\ Disjoint r1 r2' /\ innermost_loop h q1.
Admitted.

Theorem lc_disj_exits_lsplits `{redCFG}
          (s e1 e2 q1 q2 h : Lab) (i j1 j2 k : Tag) (t1 t2 : list Coord)
          (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
          (Hexit1 : exit_edge h q1 e1)
          (Hexit2 : exit_edge h q2 e2)
          (Hpath1 : TPath (root,start_tag) (e1,i) ((e1,i) :: (q1,j1) :: t1))
          (Hpath2 : TPath (root,start_tag) (e2,i) ((e2,i) :: (q2,j2) :: t2))
  : s ∈ splitsT e1 \/ s ∈ splitsT e2.
Proof.
  destruct Hlc. destructH.
  rename x into r1.
  rename l2' into r2.
  remember (hd (e1,i) (rev r1)) as ul1.
  remember (hd (e2,i) (rev r2)) as ul2.
  destruct ul1 as [u1 l1].
  destruct ul2 as [u2 l2].
  assert (DiamondPaths s u1 u2 e1 e2 q1 q2 k i l1 l2 j1 j2 r1 r2) as D.
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
    - admit.
  }
  inv_path Hpath1. inv_path Hpath2.
  eapply tag_exit_eq' in Hexit1;eauto.
  eapply tag_exit_eq' in Hexit2;eauto.
  destruct Hexit1 as [n1 Hexit1].
  destruct Hexit2 as [n2 Hexit2].
  subst j1 j2.
  specialize (Nat.le_ge_cases n1 n2) as Ncase.
  destruct Ncase;[left|right].
  - eapply diamond_path_to_latch in D;eauto.
    destructH.
    eapply splitsT_spec.
    Lemma cpath_tcfg_path `(C : redCFG) p q π i
          (Hpath : CPath p q π)
          (Hdep : depth p = |i|)
      : exists t j, TPath (p,i) (q,j) t /\ map fst t = π.
    Admitted.
    destruct D3.
    eapply loop_reachs_member in H10.
    destruct H10.
    eapply subgraph_path' in H10;eauto.
    eapply cpath_tcfg_path in H10.
    2: symmetry;eapply tag_depth'.
    2: { eapply path_app';eauto. }
    destructH.
    do 8 eexists.
    split_conj.
    + admit.
    + admit.
    + cbn. admit.
    + admit.
Admitted.

Corollary lc_disj_exit_lsplits `{redCFG} (s e q1 q2 h : Lab) (i j1 j2 k : Tag) (t1 t2 : list Coord)
          (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
          (Hexit1 : exit_edge h q1 e)
          (Hexit2 : exit_edge h q2 e)
          (Hpath1 : TPath (root,start_tag) (e,i) ((e,i) :: (q1, j1) :: t1))
          (Hpath2 : TPath (root,start_tag) (e,i) ((e,i) :: (q2, j2) :: t2))
  : s ∈ splitsT e.
Proof.
  eapply lc_disj_exits_lsplits in Hlc;eauto.
  tauto.
Qed.
