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
    
End disj.

Hint Resolve t1_tpath t2_tpath r_neq q1_eq_q2 tl_j_eq.

Lemma impl_lift `(C : redCFG) (s q1' : Lab) (h q1 q2 e1 e2 : local_impl_CFG_type C q1')
      (t1 t2 r1 r2 : list (Lab * Tag)) (k i j1 j2 : Tag)
      (Heq : q1' = `q1)
      (Hlc : last_common' ((`q1, j1) :< t1) ((`q2, j2) :< t2) r1 r2 (s, k))
      (Hexit1 : exit_edge (`h) (`q1) (`e1))
      (Hexit2 : exit_edge (`h) (`q2) (`e2))
      (Hpath1 : TPath (root, start_tag) (`e1, i) ((`e1, i) :<: (`q1, j1) :< t1))
      (Hpath2 : TPath (root, start_tag) (`e2, i) ((`e2, i) :<: (`q2, j2) :< t2))
      (t1' := impl_tlist q1' t1)
      (t2' := impl_tlist q1' t2)
      (r1' := impl_tlist q1' r1)
      (r2' := impl_tlist q1' r2)
      (C' := local_impl_CFG C q1')
  : exists s', last_common' ((q1,j1) :< t1') ((q2,j2) :< t2') r1' r2' (s',j1)
          /\ exit_edge (redCFG:=C') h q1 e1
          /\ exit_edge (redCFG:=C') h q2 e2
          /\ TPath (C:=C') (↓ purify_implode q1', start_tag) (e1, i) ((e1, i) :<: (q1, j1) :< t1')
          /\ TPath (C:=C') (↓ purify_implode q1', start_tag) (e2, i) ((e2, i) :<: (q2, j2) :< t2')
          /\ depth s' = depth q1.
Admitted.


(*  TODO: adapt this form :
Theorem lc_disj_exits_lsplits' `{redCFG}
          (s e1 e2 q1 q2 h : Lab) (j1 j2 k : Tag) (t1 t2 : ne_list Coord) (r1 r2 : list Coord)
          (Hlc : last_common' t1 t2 r1 r2 (s,k))
          (Hexit1 : exit_edge h q1 e1)
          (Hexit2 : exit_edge h q2 e2)
          (Hpath1 : TPath (root,start_tag) (q1,j1) t1)
          (Hpath2 : TPath (root,start_tag) (q2,j2) t2)
          (Hneq : r1 <> r2)
          (Htag : tl j1 = tl j2)
          (Htagle : hd 0 j1 < hd 0 j2)
  : exists (qq qq' : Lab), (s,qq,qq') ∈ splits' h e1 \/ (s,qq,qq') ∈ splits' h e2.
 *)

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
  - assert (implode_nodes (head_exits_CFG H q1) q1 q1) as Hq1 by admit.
    assert (implode_nodes (head_exits_CFG H q1) q1 q2) as Hq2 by admit.
    assert (implode_nodes (head_exits_CFG H q1) q1 e1) as He1 by admit.
    assert (implode_nodes (head_exits_CFG H q1) q1 e2) as He2 by admit.
    assert (implode_nodes (head_exits_CFG H q1) q1 h) as Hh by admit.
    cstr_subtype Hq1. cstr_subtype Hq2. cstr_subtype He1. cstr_subtype He2. cstr_subtype Hh.
    eapply impl_lift in Hlc as Hlc';eauto.
    destructH.
    eapply lc_disj_exits_lsplits_base in Hlc'0. 2-7:eauto.
    destruct Hlc'0 as [qq [qq' [Hlc'0|Hlc'0]]].
    + setoid_rewrite splits'_spec. admit.
      (* show that qq & qq' are exit_edges of s' on H, then construct the coresponding paths to them
       * and show that last_common holds for these paths, bc they are subpaths. 
       * then exploit IHn, use resulting qq_ih & qq'_ih as witnesses, choose the complicated case,
       * there s',qq,qq' are the witnesses and you get one condition by IHn and the other by Hlc'0 *)
    + (* analogous *) admit.
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
