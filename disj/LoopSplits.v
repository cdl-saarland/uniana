Require Export EqNeqDisj SplitsDef.

Section disj.
  Context `(C : redCFG).
  
  Load X_vars.
  Notation "pi -t> qj" := (tcfg_edge pi qj = true) (at level 50).

  Variables  (e1 e2 h : Lab).
  Hypotheses (Hexit1 : exit_edge h q1 e1)
             (Hexit2 : exit_edge h q2 e2)
             (Hle : hd 0 j1 <= hd 0 j2).
  
  Theorem lc_disj_exits_lsplits_base
          (Hdep : depth s = depth q1)
    : exists (qq qq' : Lab), (s,qq,qq') ∈ splits' h e1 \/ (s,qq,qq') ∈ splits' h e2.
  Proof.
  Admitted.

  Lemma splits'_edge1 qq qq'
    (Hsp : (s,qq,qq') ∈ splits' h e1)
    : edge s qq = true.
  Admitted.
  
  Lemma splits'_edge2 qq qq'
    (Hsp : (s,qq,qq') ∈ splits' h e2)
    : edge s qq' = true.
  Admitted.

(*  Lemma t1_tpath
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
*)
  Lemma q1_eq_q2
    : eq_loop q1 q2.
  Proof.
    eapply eq_loop_exiting in Hexit1.
    eapply eq_loop_exiting in Hexit2.
    rewrite <-Hexit1, <-Hexit2.
    reflexivity.
  Qed.
(*
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
  Admitted. *)
    
End disj.

Hint Resolve q1_eq_q2.

Lemma impl_lift_exit_edge `(C : redCFG) (q' : Lab) (h q e : local_impl_CFG_type C q')
      (Hexit : exit_edge (`h) (`q) (`e))
      (Heq : eq_loop (`q) q')
  : exit_edge (redCFG:= local_impl_CFG C q') h q e.
Admitted.

Lemma impl_lift `(C : redCFG) (s q1' : Lab) (h q1 q2 e1 e2 : local_impl_CFG_type C q1')
      (t1 t2 : ne_list (Lab * Tag)) (r1 r2 : list (Lab * Tag)) (k i j1 j2 : Tag)
      (Hlc : last_common' t1 t2 r1 r2 (s, k))
      (Hpath1 : TPath (root, start_tag) (`q1, j1) t1)
      (Hpath2 : TPath (root, start_tag) (`q2, j2) t2)
      (Hexit1 : exit_edge (`h) (`q1) (`e1))
      (Hexit2 : exit_edge (`h) (`q2) (`e2))
      (Heq : eq_loop q1' (`q1))
      (Hneq : r1 <> r2)
      (r1' := impl_tlist q1' r1)
      (r2' := impl_tlist q1' r2)
      (C' := local_impl_CFG C q1')
  : exists s' (t1' t2' : ne_list (local_impl_CFG_type C q1' * Tag)),
    impl_tlist q1' t1 = t1'
    /\ impl_tlist q1' t2 = t2'
    /\ last_common' t1' t2' r1' r2' (s',j1)
    /\ TPath (C:=C') (↓ purify_implode q1', start_tag) (q1, j1) t1'
    /\ TPath (C:=C') (↓ purify_implode q1', start_tag) (q2, j2) t2'
    /\ exit_edge (redCFG:=C') h q1 e1
    /\ exit_edge (redCFG:=C') h q2 e2
    /\ r1' <> r2'
    /\ depth (`s') = S (depth q1).
Admitted.

Lemma exists_or_exists_switch (X : Type) (P P' : X -> X -> Prop)
      (Q Q' : X -> X -> X -> Prop) (R : X -> X -> X -> X -> X -> Prop)
  : (exists v w z, (Q v w z /\ exists x y, R x y v w z)
              \/ Q' v w z /\ exists x y, R x y v w z)
    -> exists (x y : X), (P x y \/ exists v w z, Q v w z /\ R x y v w z)
                   \/ (P' x y \/ exists v w z, Q' v w z /\ R x y v w z).
Proof.
  intro N. destructH. destruct N as [[N1 N2]|[N1 N2]];destructH.
  - exists x, y. left. firstorder.
  - exists x, y. right. firstorder.
Qed.

(* TODO: I should define s' properly and prove its properties gradually *)

Theorem lc_disj_exits_lsplits' `{redCFG}
          (s e1 e2 q1 q2 h : Lab) (j1 j2 k : Tag) (t1 t2 : ne_list Coord) (r1 r2 : list Coord)
          (Hlc : last_common' t1 t2 r1 r2 (s,k))
          (Hpath1 : TPath (root,start_tag) (q1,j1) t1)
          (Hpath2 : TPath (root,start_tag) (q2,j2) t2)
          (Hexit1 : exit_edge h q1 e1)
          (Hexit2 : exit_edge h q2 e2)
          (Hneq : r1 <> r2)
          (Htag : tl j1 = tl j2)
          (Htagle : hd 0 j1 <= hd 0 j2)
  : exists (qq qq' : Lab), (s,qq,qq') ∈ splits' h e1 \/ (s,qq,qq') ∈ splits' h e2.
Proof.
  remember (depth s - depth q1).
  revert Htag Htagle.
  revert dependent Lab. 
  revert j1 j2 k.
  induction n;intros.
  - eapply lc_disj_exits_lsplits_base;eauto.
    enough (depth q1 <= depth s) by omega.
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
    eapply lc_disj_exits_lsplits_base in Hlc'1. 2-11:eauto. 2:admit.
    destruct Hlc'0 as [qq [qq' [Hlc'0|Hlc'0]]]. setoid_rewrite splits'_spec.
    eapply exists_or_exists_switch.
    destructH.
    exists (`s'), (`qq), (`qq').
    assert (exists qe1, exit_edge (` s') qe1 (` qq)) as Hqe1 by admit.
    assert (exists qe2, exit_edge (` s') qe2 (` qq')) as Hqe2 by admit. do 2 destructH.
    destruct Hlc'1;[left|right].
    + cbn. split.
      * cstr_subtype He1. cstr_subtype Hh. eapply splits'_loop_splits__imp.
        1: eapply eq_loop_exiting;eauto. eauto.
      * eapply IHn. 4,5: eauto. all:eauto. 1,2: admit. clear - Hlc'9 Heqn Hqe1.
        cbn in Heqn.
        assert (depth qe1 = depth (`s')) by admit. rewrite H0.
        setoid_rewrite Hlc'9.
        assert (depth (C:=local_impl_CFG H q1) (↓ purify Hq1) = depth q1) by admit.
        setoid_rewrite H1. omega.
    + 
      (* show that qq & qq' are exit_edges of s' on H, then construct the coresponding paths to them
       * and show that last_common holds for these paths, bc they are subpaths. 
       * then exploit IHn, use resulting qq_ih & qq'_ih as witnesses, choose the complicated case,
       * there s',qq,qq' are the witnesses and you get one condition by IHn and the other by Hlc'0 *)
      admit.
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
  decide (hd 0 j1 <= hd 0 j2).
  - rewrite last_common'_iff in Hlc. destructH.
    eapply lc_disj_exits_lsplits'. 1-5,8:eauto.
    + inversion Hpath1. path_simpl' H1. eauto.
    + inversion Hpath2. path_simpl' H1. eauto.
    + admit.
    + inversion Hpath1. path_simpl' H1. eapply tag_exit_iff in H4. admit.
  - (* analogous *) admit.
Admitted.

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
