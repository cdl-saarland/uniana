Require Export EqNeqDisj SplitsDef.

Section disj.
  Context `(C : redCFG).
  Variables  (s e1 e2 q1 q2 h : Lab) (i j1 j2 k : Tag) (t1 t2 r1 r2 : list (Lab * Tag)).
  Hypotheses (Hlc : last_common' ((q1,j1) :< t1) ((q2,j2) :< t2) r1 r2 (s,k))
             (Hexit1 : exit_edge h q1 e1)
             (Hexit2 : exit_edge h q2 e2)
             (Hpath1 : TPath (root,start_tag) (e1,i) ((e1,i) :<: (q1,j1) :< t1))
             (Hpath2 : TPath (root,start_tag) (e2,i) ((e2,i) :<: (q2,j2) :< t2))
             (Hneq : j1 <> j2).
  
  Theorem lc_disj_exits_lsplits_base
          (Hdep : depth s = depth q1)
    : exists (qq qq' : Lab), (s,qq,qq') ∈ splits' h e1 \/ (s,qq,qq') ∈ splits' h e2.
  Proof.
  Admitted.

  Lemma t1_tpath
    : TPath (root,start_tag) (q1,j1) ((q1,j1) :< t1).
  Proof.
    inversion Hpath1.
    path_simpl' H0. eauto.
  Qed.

  Lemma t2_tpath
    : TPath (root,start_tag) (q2,j2) ((q2,j2) :< t2).
  Proof.
    inversion Hpath2.
    path_simpl' H0. eauto.
  Qed.

  Lemma r_neq
    : r1 <> r2.
  Proof.
    unfold last_common' in Hlc. destructH.
    destruct r1,r2; try (intro N;congruence).
    - exfalso. cbn in *. simpl_nl' Hlc0. simpl_nl' Hlc2.
      eapply postfix_hd_eq in Hlc0.
      eapply postfix_hd_eq in Hlc2.
      inversion Hlc0; inversion Hlc2;subst. congruence. 
    - intro N. inversion N. subst.
      eapply Hlc1;eauto.
  Qed.

  Lemma q1_eq_q2
    : eq_loop q1 q2.
  Proof.
    eapply eq_loop_exiting in Hexit1.
    eapply eq_loop_exiting in Hexit2.
    rewrite <-Hexit1, <-Hexit2.
    reflexivity.
  Qed.

  Lemma tl_j_eq
    : tl j1 = tl j2.
  Proof.
    inversion Hpath1.
    inversion Hpath2.
    path_simpl' H0.
    path_simpl' H5.
    eapply tag_exit_iff in H3. destruct H3 as [_ H3].
    eapply tag_exit_iff in H8. destruct H8 as [_ H8].
    rewrite <-H3. rewrite <-H8. reflexivity.
    - admit.
    - admit.
  Admitted.
    
    
(*
  Lemma s_deq_q : deq_loop s q1.
  Proof.
    rewrite last_common'_iff in Hlc. copy Hlc Hlc'. destructH' Hlc'.
    do 2 rewrite nlcons_to_list in Hlc.
    inversion Hpath1. inversion Hpath2.
    path_simpl' H0.
    path_simpl' H5.
    do 2 rewrite nlcons_to_list in Hlc'.
    eapply s_deq_q;eauto.
    - admit.
    - eapply eq_loop_exiting in Hexit1.
      eapply eq_loop_exiting in Hexit2.
      rewrite <-Hexit1, <-Hexit2. reflexivity.
    - eapply tag_exit_iff in H3.
      eapply tag_exit_iff in H5. *)
End disj.

Hint Resolve t1_tpath t2_tpath r_neq q1_eq_q2 tl_j_eq.
  
Theorem lc_disj_exits_lsplits' `{redCFG}
          (s e1 e2 q1 q2 h : Lab) (i j1 j2 k : Tag) (t1 t2 r1 r2 : list Coord)
          (Hlc : last_common' ((q1,j1) :< t1) ((q2,j2) :< t2) r1 r2 (s,k))
          (Hexit1 : exit_edge h q1 e1)
          (Hexit2 : exit_edge h q2 e2)
          (Hpath1 : TPath (root,start_tag) (e1,i) ((e1,i) :<: (q1,j1) :< t1))
          (Hpath2 : TPath (root,start_tag) (e2,i) ((e2,i) :<: (q2,j2) :< t2))
          (Hneq : j1 <> j2)
  : exists (qq qq' : Lab), (s,qq,qq') ∈ splits' h e1 \/ (s,qq,qq') ∈ splits' h e2.
Proof.
  remember (depth s - depth q1) as n. 
  revert dependent Lab.
  induction n;intros.
  - eapply lc_disj_exits_lsplits_base;eauto. 
    enough (depth q1 <= depth s).
    { omega. }
    eapply deq_loop_depth.
    eapply s_deq_q;eauto.
  - admit.
Admitted.
  
Theorem lc_disj_exits_lsplits `{redCFG}
          (s e1 e2 q1 q2 h : Lab) (i j1 j2 k : Tag) (t1 t2 : list Coord)
          (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
          (Hexit1 : exit_edge h q1 e1)
          (Hexit2 : exit_edge h q2 e2)
          (Hpath1 : TPath (root,start_tag) (e1,i) ((e1,i) :<: (q1,j1) :< t1))
          (Hpath2 : TPath (root,start_tag) (e2,i) ((e2,i) :<: (q2,j2) :< t2))
          (Hneq : j1 <> j2)
  : exists (qq qq' : Lab), (s,qq,qq') ∈ splits' h e1 \/ (s,qq,qq') ∈ splits' h e2.
Proof.
  do 2 rewrite nlcons_to_list in Hlc.
  rewrite last_common'_iff in Hlc. destructH.
  eapply lc_disj_exits_lsplits';eauto.
Qed.

Corollary lc_disj_exit_lsplits `{redCFG} (s e q1 q2 h : Lab) (i j1 j2 k : Tag) (t1 t2 : list Coord)
          (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
          (Hexit1 : exit_edge h q1 e)
          (Hexit2 : exit_edge h q2 e)
          (Hpath1 : TPath (root,start_tag) (e,i) ((e,i) :<: (q1, j1) :< t1))
          (Hpath2 : TPath (root,start_tag) (e,i) ((e,i) :<: (q2, j2) :< t2))
          (Hneq : j1 <> j2)
  : exists (qq qq' : Lab), (s,qq,qq') ∈ splits' h e.
Proof.
  eapply lc_disj_exits_lsplits in Hlc;eauto.
  destructH. eexists;eexists. destruct Hlc;eauto.
Qed.
