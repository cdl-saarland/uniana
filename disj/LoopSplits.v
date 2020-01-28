Require Export EqNeqDisj SplitsDef GetSucc.

Require Import LiftShift.

Section disj.

  Context `(D : disjPathsE).
  
  Hypotheses (Htag : tl j1 = tl j2)
             (Htagleq : hd 0 j1 <= hd 0 j2)
             (Hextra : j1 = j2 -> exists π, CPath q2 h (π :r: q2) /\ Disjoint (map fst r1) π).

  Lemma lc_disj_exits_lsplits_base_lt
        (Hdep : depth s = depth q1)
        (Htaglt : hd 0 j1 < hd 0 j2)
    : ( s, qs1, qs2) ∈ loop_splits C h e1.
  Proof.
  Admitted. (* FIXME *)
  
  Lemma lc_disj_exits_lsplits_base_eq π
          (Hdep : depth s = depth q1)
          (Htageq : j1 = j2)
          (Hlatchp : CPath q2 h (π ++ [q2]))
          (Hlatchd : Disjoint (map fst r1) π)
    : (s,qs1,qs2) ∈ loop_splits C h e1.
  Proof.
  Admitted. (* FIXME *)


  Lemma hd_eq_eq
        (Hheq : hd 0 j1 = hd 0 j2)
    : j1 = j2.
  Proof.
    seapply eq_loop_exiting Hexit1 Hexit1'.
    seapply eq_loop_exiting Hexit2 Hexit2'.
    eapply hd_tl_len_eq; eauto with disjPaths.
    erewrite tag_depth. 2:eapply Hpath1.
    erewrite tag_depth. 2:eapply Hpath2.
    2,3: eapply path_contains_front. 2: eapply Hpath2. 2: eapply Hpath1.
    rewrite <-Hexit1'. rewrite <-Hexit2'. reflexivity.
  Qed.
  
  Corollary lc_disj_exits_lsplits_base
          (Hdep : depth s = depth q1)
    : (s,qs1,qs2) ∈ loop_splits C h e1.
  Proof.
    seapply le_lt_or_eq Htagleq Q. 
    destruct Q.
    - eapply lc_disj_exits_lsplits_base_lt;eauto.
    - eapply hd_eq_eq in H. copy Hextra Hextra'. exploit Hextra'. destructH.
      eapply lc_disj_exits_lsplits_base_eq;eauto.
  Qed.
    
  Corollary lc_disj_exits_lsplits_base'
          (Hdep : depth s = depth q1)
    : (s,qs1,qs2) ∈ splits' h e1.
  Proof.
    rewrite splits'_spec. left.
    eapply lc_disj_exits_lsplits_base;eauto.
  Qed.
                            (* FIXME *)
  Lemma disj_latch_path_or
        (Heq : j1 = j2)
    : exists π, (CPath q2 h (π :r: q2) /\ Disjoint (map fst r1) π)
           \/ (CPath q1 h (π :r: q1) /\ Disjoint (map fst r2) π).
  Proof.
    clear Hextra Htagleq Htag.
    destruct Hexit1 as [Hin1 [Hnin1 Hedge1]].
    destruct Hexit2 as [Hin2 [Hnin2 Hedge2]].
    copy Hin1 Hin1'. copy Hin2 Hin2'.
    unfold loop_contains in Hin1, Hin2.
    destruct Hin1 as [p1 [ϕ1 [Hb1 [Hp1 Htl1]]]].
    destr_r' ϕ1;subst. 1: inversion Hp1.
    path_simpl' Hp1.
    decide (exists x, x ∈ map fst r2 /\ x ∈ (h :: l)).
    - destruct Hin2 as [p2 [ϕ2 [Hb2 [Hp2 Htl2]]]].
      destr_r' ϕ2;subst. 1: inversion Hp2.
      path_simpl' Hp2.
      decide (exists y, y ∈ map fst r1 /\ y ∈ (h :: l0)).
      + exfalso.
        rename e into Hx.
        rename e0 into Hy.
        clear x x0.
        do 2 destructH.
        destruct Hy1;[subst y;eapply no_head;eauto with disjPaths|]. 
        destruct Hx1.
        {
          subst x. eapply no_head. 1: eapply last_common'_sym. all: eauto with disjPaths.
        }
        rename H0 into Hx. 
        rename H into Hy.
        destr_r' l;subst. 1:inversion Hx.
        destr_r' l0;subst. 1: inversion Hy.
        rename x0 into q1'. rename x1 into q2'.
        eapply path_nlrcons_edge in Hp1 as Hedge1'.
        eapply path_nlrcons_edge in Hp2 as Hedge2'.
        eapply path_rcons_rinv in Hp1.
        eapply path_rcons_rinv in Hp2.
        (* construct paths to x & y *)
        eapply path_to_elem in Hp2.
        2: eauto.
        eapply path_to_elem in Hp1.
        2: eauto.
        destruct Hp1 as [πx1 [Hπx1 Hπx1_p]].
        destruct Hp2 as [πy2 [Hπy2 Hπy2_p]].
        (* construct paths to the q's *)
        specialize (r1_tpath Hlc Hpath1) as Hr1.
        eapply TPath_CPath in Hr1. cbn in Hr1. rewrite map_rcons in Hr1. cbn in Hr1.
        specialize (r2_tpath Hlc Hpath2) as Hr2.
        eapply TPath_CPath in Hr2. cbn in Hr2. rewrite map_rcons in Hr2. cbn in Hr2.
        destr_r' r1;subst. 1:cbn in Hy0;contradiction.
        destr_r' r2;subst. 1:cbn in Hx0;contradiction.
        rewrite map_rcons in Hr1,Hr2.
        eapply path_rcons_rinv in Hr1. 
        eapply path_rcons_rinv in Hr2. 
        eapply path_from_elem in Hr1;[|auto|rewrite map_rcons in Hy0;eapply Hy0].
        eapply path_from_elem in Hr2;[|auto|rewrite map_rcons in Hx0;eapply Hx0].
        destruct Hr1 as [πy1 [Hπy1 Hπy1_p]].
        destruct Hr2 as [πx2 [Hπx2 Hπx2_p]].
        eapply path_app' in Hπx2 as HQ;eauto.
        eapply path_app in Hedge1';eauto.
        eapply path_app' in Hedge1';eauto.
        eapply path_rcons in Hedge2';eauto.
        clear Hedge1'. rename Hedge2' into Hedge1'.
        eapply dom_self_loop in Hedge1'.
        * clear - Hedge1' Hπx2.
          destruct πx2;[inversion Hπx2|].
          cbn in *. inversion Hedge1';subst. congruence'.
        * eapply exit_edge_innermost;eapply Hexit2.
        * eapply path_contains_front in Hπx2.
          specialize (no_head Hlc Hpath1 Hpath2) as Hnh1. do 3 exploit' Hnh1.
          1-3: eauto with disjPaths.
          specialize (Hnh1 h).
          specialize (no_head (last_common'_sym Hlc) Hpath2 Hpath1) as Hnh2.
          exploit' Hnh2;[symmetry;eauto with disjPaths|]. 
          do 2 exploit' Hnh2. specialize (Hnh2 h).
          clear - Htl2 Htl1 Hπx1 Hπx2 Hπy1 Hπy2 Hπx1_p Hπx2_p Hπy1_p Hπy2_p Hnh1 Hnh2 Hin1' Hin2'.
          intro N. eapply in_app_or in N.
          rewrite rev_rcons in Htl1.
          rewrite rev_rcons in Htl2.
          unfold tl in Htl1,Htl2.
          rewrite <-in_rev in Htl1,Htl2.
          destruct N. (* special cases : q2 = h & h = s *)
          -- eapply in_app_or in H.
             destruct H;[|eapply Htl2;eapply prefix_incl;eauto;eapply tl_incl;eauto].
             eapply in_app_or in H.
             destruct H;[|eapply Hnh1;[eapply postfix_incl;eauto|eauto]].
             2: rewrite map_rcons;auto.
             eapply in_app_or in H.
             destruct H;[|eapply Htl1;eapply prefix_incl;eauto;eapply tl_incl;eauto].
             eapply Hnh2;[eapply postfix_incl;eauto|eauto].
             rewrite map_rcons;auto.
          -- cbn in H. destruct H;[|contradiction]. subst q2. eapply Hnh2;eauto.
             eapply postfix_incl; eauto. rewrite map_rcons;auto.
      (* q2 ->+ y ->* q1 ->+ x ->* q2 *)
      + exists (h :: l0). left. cbn. split.
        * econstructor;eauto. eapply back_edge_incl;eauto.
        * do 2 simpl_dec' n. intros X H. destruct (n X);[contradiction|auto].
    - exists (h :: l). right. cbn. split.
      + econstructor;eauto. eapply back_edge_incl;eauto.
      + do 2 simpl_dec' n. intros X H. destruct (n X);[contradiction|auto].
  Qed.
    
End disj.

(* To turn disjPaths around I have to leave and reenter section *)

Section disj.

  Context `(D : disjPathsE).
  Hypotheses (Htag : tl j1 = tl j2)
             (Htagleq : hd 0 j1 <= hd 0 j2)
             (Hextra : j1 = j2 -> exists π, CPath q2 h (π :r: q2) /\ Disjoint (map fst r1) π).

  Lemma eqn_sdeq n
        (Heqn : S n = depth s - depth q1)
    : deq_loop s q1.
  Admitted.

  Lemma eqn_ndeq n
        (Heqn : S n = depth s - depth q1)
    : ~ deq_loop q1 s.
  Proof.
    clear - Heqn.
    intro N.
    eapply deq_loop_depth in N.
    omega.
  Qed.
  
Theorem lc_disj_exits_lsplits'
  : (s,qs1,qs2) ∈ splits' h e1.
Proof.
  remember (depth s - depth q1).
  revert Hextra.
  revert dependent Lab. clear - Htag Htagleq.
  revert i1 i2 j1 j2 k js1 js2 Htag Htagleq.
  induction n;intros.
  - eapply lc_disj_exits_lsplits_base';eauto.
    enough (depth q1 <= depth s) by omega.
    eapply deq_loop_depth.
    eapply s_deq_q;eauto with disjPaths.
  - eapply eqn_ndeq in Heqn as Hndeq.
    eapply eqn_sdeq in Heqn as Hsdeq.
    specialize (ex_impl_dP1 D0) as I. exploit I. destructH.
    specialize (lift_disjPathsE (I:=I)) as Q.
    eapply lc_disj_exits_lsplits_base in Q.
    2,3:eauto.
    3: { (*match goal with |- _ = ?a => assert (a = depth q1) end.
         - eapply impl_depth_self_eq. rewrite <-Hex0. reflexivity.
         - admit. (*setoid_rewrite H.*) *)
      admit. 
    }
    2: admit. (* lift hextra *)
    setoid_rewrite splits'_spec.
    right.
    exists (`s'), (`qs1'), (`qs2').
    split.
    + specialize (@splits'_loop_splits__imp _ _ _ _ C q1 h' e1' s' qs1' qs2') as QQ.
      assert (h = `h') as Hheq by admit. 
      exploit QQ.
      * eapply eq_loop_exiting;eauto with disjPaths. destruct D. rewrite <-Hheq.
        eapply Hexit1.
      * destruct I. setoid_rewrite <-He1 in QQ. setoid_rewrite <-Hheq in QQ. eauto.
    + (* case distinction on trichotomy: we have to distinguish different cases,
         because the IHn can be applied in two different, symmetrical ways *)
      specialize (Nat.lt_trichotomy n1 n2) as Nrel.
      destruct Nrel as [Nlt|[Neq|Nlt]]; [left| |right].
      * eapply IHn; cycle 2. (*eapply IHn with (i1:=j1) (i2:=j2) (j1:=n1::j1) (j2:=n2::j1);cycle 2.*)
        -- eapply disjPathsE_shift_lt.
        -- admit.
        -- intro N. inversion N. rewrite H0 in Nlt. clear - Nlt. omega. 
        -- cbn. reflexivity.
        -- unfold hd. eapply Nat.lt_le_incl. eapply Nlt.
      * specialize (disjPathsE_shift_eq Neq) as Dshift.
        eapply disj_latch_path_or in Dshift as Hπ. 2: clear - Neq;f_equal;eauto.
        destruct Hπ as [π [Hπ | Hπ]];[left|right].
        -- eapply IHn. 3:eapply Dshift. 1,2:cbn;eauto. 1:rewrite Neq;reflexivity. admit.
           intro N. eexists;eauto.
        -- eapply splits'_sym.
           eapply IHn. 3:eapply disjPathsE_sym;eapply Dshift. 1,2:cbn;eauto.
           1: rewrite Neq;reflexivity.
           admit.
           intro N. eexists;eauto. 
      * eapply splits'_sym.
        eapply IHn;cycle 2.
        -- eapply disjPathsE_sym. 
           eapply disjPathsE_shift_lt2.
        -- admit. 
        -- intro N. inversion N. rewrite H0 in Nlt. clear - Nlt. omega. 
        -- cbn. reflexivity.
        -- unfold hd. clear - Nlt. eapply Nat.lt_le_incl;auto.
Admitted.

End disj.

(*
  Lemma impl_shift_lc
    : last_common' tt1 tt2 rr1 rr2 (s, k).
  Proof.
    unfold tt1, tt2. 
    eapply last_common_app_eq1 in Hlc as Htt1.
    eapply last_common_app_eq2 in Hlc as Htt2.
    do 2 rewrite <-app_assoc.
    eapply last_common_prefix.
    setoid_rewrite <-Htt1 at 1. setoid_rewrite <-Htt2. eapply Hlc.
    1,2: unfold rr1, rr2; eapply prefix_nincl_prefix'.
  Qed.

  Lemma impl_shift_succ1
    : (qs1, js1) ≻ (s, k) | (` qs1', j1) :: tt1.
  Proof.
    eapply last_common_app_eq1 in Hlc as Htt1.
    clear - Hsucc1 Hpath1 Hexit1 Htt1.
    eapply succ_in_prefix_nd;eauto.
    - enough ((` qs1',j1) ∈ r1) as Hel1.
      + eapply prefix_eq.
        eapply prefix_nincl_prefix in Hel1.
        eapply prefix_eq in Hel1. destructH.
        exists ((`e1', tl j1) :: l2').
        rewrite Htt1.
        unfold tt1, rr1.
        setoid_rewrite Hel1 at 1.
        rewrite <-app_assoc. rewrite <-app_comm_cons at 1. setoid_rewrite <-app_comm_cons.
        rewrite <-app_assoc. reflexivity.
      + (* because (s',j1) is in t1' and <> the hd of t1', i.e. q1, its successor is in r1 *)
        admit. 
    - unfold tt1. 
      eapply in_or_app. left. eapply In_rcons. left. auto.
    - eapply tpath_NoDup. 
      econstructor;eauto 1.
      unfold "`".
      eapply exit_edge_tcfg_edge;eauto.
  Admitted.
    
  Lemma impl_shift_succ2
    : (qs2, js2) ≻ (s, k) | (` qs2', j1) :: tt2.
  Proof.
    eapply last_common_app_eq2 in Hlc as Htt2.
    clear - Htt2 Hsucc2 Hpath2 Hexit2. cbn in Hsucc2.
    eapply succ_in_prefix_nd;eauto.
    - eapply prefix_eq.
      enough ((` qs2',j1) ∈ r2) as Hel2.
      + eapply prefix_nincl_prefix in Hel2.
        eapply prefix_eq in Hel2. destructH.
        exists ((`e2', tl j2) :: l2').
        rewrite Htt2.
        unfold tt2, rr2. setoid_rewrite Hel2 at 1.
        rewrite <-app_assoc. rewrite <-app_comm_cons at 1. setoid_rewrite <-app_comm_cons.
        rewrite <-app_assoc. reflexivity.
      + admit. (* as above *)
    - unfold tt2. 
      eapply in_or_app. left. eapply In_rcons. left. auto.
    - eapply tpath_NoDup. 
      econstructor;eauto 1.
      unfold "`".
      eapply exit_edge_tcfg_edge;eauto.
  Admitted.
 *)

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
  destruct H3,H8.
  rewrite <-H1, <-H3;auto.
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
  : exists (qq qq' : Lab), (s,qq,qq') ∈ splits' h e1 \/ (s,qq,qq') ∈ splits' h e2.
Proof.
  assert (tl j1 = tl j2) as Htl_eq by (eapply tl_eq;eauto).
  rewrite last_common'_iff in Hlc. destructH.
  inversion Hpath1. inversion Hpath2. subst.
  replace b with (q1,j1) in *. clear b.
  2: { eapply path_front in H1. auto. }
  replace b0 with (q2,j2) in *. clear b0.
  2: { eapply path_front in H6. auto. } 
  path_simpl' H1. path_simpl' H6.
  specialize (Nat.lt_trichotomy (hd 0 j1) (hd 0 j2)) as Nrel.
  assert (exists js1 js2 qs1 qs2,
             disjPaths H q1 q2 s ((q1,j1)::t1) ((q2,j2)::t2)
                       l1' l2' j1 j2 k i i e1 e2 qs1 qs2 js1 js2) as D.
  { do 4 eexists; econstructor; eauto. 3: eapply exiting_eq_loop;eauto.
    2: eapply last_common'_sym in Hlc. 
    (*1,2: rewrite <-surjective_pairing;eapply get_succ_cons.
    2: eapply last_common'_sym in Hlc.
    all: eapply last_common_in1;eapply last_common'_iff;do 2 eexists;eauto.*)
    all: admit.
  }
  destructH.
  assert (disjPathsE D h) as D'.
  { econstructor;eauto. }
  destruct Nrel as [Nlt|[Neq|Nlt]];[| |].
  - do 2 eexists.
    left. eapply lc_disj_exits_lsplits';eauto. (*
    + econstructor;eauto;rewrite <-surjective_pairing;eapply get_succ_cons.
      2: eapply last_common'_sym in Hlc.
      all: eapply last_common_in1;eapply last_common'_iff;do 2 eexists;eauto.*)
    + omega.
    + intro N. rewrite N in Nlt. clear - Nlt. omega. 
  - eapply hd_eq_eq in Neq;eauto.
    specialize (disj_latch_path_or D' Neq) as Hlatch.
    destruct Hlatch as [π [Hlatch|Hlatch]].
    + do 2 eexists.
      left. eapply lc_disj_exits_lsplits';eauto. rewrite Neq. reflexivity.
    + do 2 eexists.
      right. eapply lc_disj_exits_lsplits'.
      1: eapply disjPathsE_sym;eauto.
      2: rewrite Neq.
      all: eauto. 
  - do 2 eexists.
    right. eapply lc_disj_exits_lsplits'.
    + eapply disjPathsE_sym; eauto.
    + symmetry. auto. 
    + omega.
    + intro N. rewrite N in Nlt. clear - Nlt. omega.
Admitted.

Corollary lc_disj_exit_lsplits `{redCFG} (s e q1 q2 h : Lab) (i j1 j2 k : Tag) (t1 t2 : list Coord)
          (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
          (Hexit1 : exit_edge h q1 e)
          (Hexit2 : exit_edge h q2 e)
          (Hpath1 : TPath (root,start_tag) (e,i) ((e,i) :: (q1, j1) :: t1))
          (Hpath2 : TPath (root,start_tag) (e,i) ((e,i) :: (q2, j2) :: t2))
  : exists (qq qq' : Lab), (s,qq,qq') ∈ splits' h e.
Proof.
  eapply lc_disj_exits_lsplits in Hlc;eauto.
  destructH. eexists;eexists. destruct Hlc;eauto.
Qed.
