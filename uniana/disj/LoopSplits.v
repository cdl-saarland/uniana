Require Export EqNeqDisj GetSucc SplitsT.


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

Theorem lc_disj_exits_lsplits `{redCFG}
          (s e1 e2 q1 q2 h : Lab) (i j1 j2 k : Tag) (t1 t2 : list Coord)
          (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
          (Hexit1 : exit_edge h q1 e1)
          (Hexit2 : exit_edge h q2 e2)
          (Hpath1 : TPath (root,start_tag) (e1,i) ((e1,i) :: (q1,j1) :: t1))
          (Hpath2 : TPath (root,start_tag) (e2,i) ((e2,i) :: (q2,j2) :: t2))
  : s ∈ splitsT e1 \/ s ∈ splitsT e2.
Proof.
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
