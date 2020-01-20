Require Export EqNeqDisj SplitsDef GetSucc.

Reserved Infix "-t>" (at level 50).

Class disjPaths `(C : redCFG)
      (q1 q2 s : Lab) (t1 t2 : list (Lab * Tag)) (r1 r2 : list (Lab * Tag)) (j1 j2 k : Tag)
      (e1 e2 h qs1 qs2 : Lab) (js1 js2 : Tag) :=
  {
    Hlc : last_common' t1 t2 r1 r2 (s,k);
    Hpath1 : TPath (root,start_tag) (q1,j1) t1;
    Hpath2 : TPath (root,start_tag) (q2,j2) t2;
    Htag : tl j1 = tl j2;
    Htagleq : hd 0 j1 <= hd 0 j2
    where "pi -t> qj" := (tcfg_edge pi qj = true);
    Hexit1 : exit_edge h q1 e1;
    Hexit2 : exit_edge h q2 e2;
    Hsucc1 : (qs1, js1) ≻ (s, k) | (e1, tl j1) :: t1;
    Hsucc2 : (qs2, js2) ≻ (s, k) | (e2, tl j2) :: t2;
    Hextra : j1 = j2 -> exists π, CPath q2 h (π :r: q2) /\ Disjoint (map fst r1) π
  }.

Ltac seapply H Q Q'
  := specialize Q as Q';
     eapply H in Q'.

Lemma q1_eq_q2 `(D : disjPaths)
  : eq_loop q1 q2.
Proof.
  seapply eq_loop_exiting Hexit1 Hexit1'.
  seapply eq_loop_exiting Hexit2 Hexit2'.
  rewrite <-Hexit1', <-Hexit2'.
  reflexivity. 
Qed.

Lemma q2_eq_q1 `(D : disjPaths)
  : eq_loop q2 q1.
Proof.
  symmetry. eapply q1_eq_q2;eauto.
Qed.
  
Hint Resolve Hlc Hpath1 Hpath2 Htag Htagleq Hexit1 Hexit2 Hsucc1 Hsucc2 Hextra q1_eq_q2 q2_eq_q1
  : disjPaths.



Section lift.

  Context `(C : redCFG).

  Definition cnc_loop s q s'
    := loop_contains s' s /\ ~ deq_loop q s'.
  
  Definition ocnc_loop s q s'
    := cnc_loop s q s' /\ forall x, cnc_loop s q s' -> deq_loop x s'.
  
  Variables (q s : Lab).

  Variable (s' : local_impl_CFG_type C q).
  
  Local Definition C' := local_impl_CFG C q.
  Variables (q1' q2' : local_impl_CFG_type C q)
            (t1 t2 : list (Lab * Tag)) (r1 r2 : list (Lab * Tag)) (j1 j2 k : Tag)
            (e1' e2' h' : local_impl_CFG_type C q)
            (qs1 qs2 : Lab) (js1 js2 : Tag).
  Hypothesis (Heq : eq_loop q (`q1')).

  Local Definition t1' := impl_tlist q t1.
  Local Definition t2' := impl_tlist q t2.
  
  Local Definition r1' := impl_tlist q r1.
  Local Definition r2' := impl_tlist q r2.
  
  Local Definition qs1' := fst (get_succ (s', j1) (e1', tl j1) t1').
  Local Definition qs2' := fst (get_succ (s', j1) (e2', tl j2) t2').
  
  Instance lift_disjPaths
           (Hndeq : ~ deq_loop q s)
           (Hsdeq : deq_loop s q)
           (Hocnc : ocnc_loop s q (`s'))
    : disjPaths C (`q1') (`q2') s t1 t2 r1 r2 j1 j2 k (`e1') (`e2') (`h') qs1 qs2 js1 js2
      -> disjPaths (local_impl_CFG C q) q1' q2' s' t1' t2' r1' r2' j1 j2 j1 e1' e2' h' qs1' qs2' j1 j1.
  intro H.
  Admitted.

End lift.

Section disj.

  Context `(D : disjPaths).

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
    - eapply hd_eq_eq in H. specialize Hextra as Hextra. exploit Hextra. destructH.
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


(*
Definition max_cont_cont_loop `{C : redCFG} h p q
  := loop_contains h p /\ ~ deq_loop q h
     /\ forall h', loop_contains h' h -> ~ loop_contains h q -> h = h'.

Lemma ex_max_cont_cont `(C : redCFG) (h' p q : Lab)
      (Hinp : loop_contains h' p)
      (Hinq : loop_contains h' q)
      (Hndeq : ~ deq_loop q p)
  : exists h, max_cont_cont_loop h p q.
Admitted.
                                
Section maxcont.
  Context `(C : redCFG).
  Variables (h p q : Lab) (i j : Tag) (t t' : list (Lab * Tag)).
  Hypotheses (Hpath : TPath (root,start_tag) (q,j) (t' >: (p,i) :+ t))
             (Hmcc : max_cont_cont_loop h p q).

  Lemma mcc_in_t
    : (h,take_r (|j|) i) ∈ t.
  Admitted.

  Lemma ex_exit_mcc
    : exists qe e j', exit_edge h qe e /\ (e,j) ≻ (qe, j') | t' /\ tl j' = j.
  Admitted.

End maxcont.
 *)

Parameter get_ocnc_loop : forall `(C : redCFG), Lab -> Lab -> Lab.
Parameter get_ocnc_spec : forall `(C : redCFG) s q,
    ~ deq_loop q s -> deq_loop s q -> ocnc_loop C s q (get_ocnc_loop C s q).

Section disj.

  Context `(D : disjPaths).
  
  Local Definition s' := get_ocnc_loop C s q1.

  Lemma Hs' s'
        (Hndeq : ~ deq_loop q1 s)
        (Hsdeq : deq_loop s q1)
    : implode_nodes C q1 s'.
  Proof.
  Admitted.

  Local Lemma Hq1 : implode_nodes (head_exits_CFG C q1) q1 q1.
  Proof.
    left. reflexivity.
  Qed.

  Local Lemma Hq2 : implode_nodes (head_exits_CFG C q1) q1 q2.
  Proof.
    eapply head_exits_implode_nodes_inv1;left. eapply q2_eq_q1;eauto.
  Qed.
  
  Local Lemma He1 : implode_nodes (head_exits_CFG C q1) q1 e1.
  Proof.
    eapply head_exits_implode_nodes_inv1;left. eapply deq_loop_exited. eauto with disjPaths.
  Qed.

  Hint Resolve deq_loop_exited eq_loop1 eq_loop2 deq_loop_exiting eq_loop_exiting : deq.
  
  Local Lemma He2 : implode_nodes (head_exits_CFG C q1) q1 e2.
  Proof.
    eapply head_exits_implode_nodes_inv1;left. eapply eq_loop1;[eapply q2_eq_q1;eauto|].
    eapply deq_loop_exited. eauto with disjPaths.
  Qed.
  
  Local Lemma Hh : implode_nodes (head_exits_CFG C q1) q1 h.
  Proof.
    eapply head_exits_implode_nodes_inv1;left.
    eapply eq_loop_exiting;eauto with disjPaths.
  Qed.

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
  revert dependent Lab. clear.
  revert j1 j2 k js1 js2. 
  induction n;intros.
  - eapply lc_disj_exits_lsplits_base';eauto.
    enough (depth q1 <= depth s) by omega.
    eapply deq_loop_depth.
    eapply s_deq_q;eauto with disjPaths.
  - (* Show that some interesting nodes are in the imploded CFG *)
(*    assert (implode_nodes (head_exits_CFG C q1) q1 q1) as Hq1.
    { left. reflexivity. }
    enough (implode_nodes (head_exits_CFG C q1) q1 q2) as Hq2.
    enough (implode_nodes (head_exits_CFG C q1) q1 e1) as He1.
    enough (implode_nodes (head_exits_CFG C q1) q1 e2) as He2.
    enough (implode_nodes (head_exits_CFG C q1) q1 h) as Hh.
    2-5: eapply head_exits_implode_nodes_inv1;left; eauto using deq_loop_exited.
    2: eapply eq_loop_exiting;eauto. 3: destruct Heq;eauto.
    2: transitivity q2;destruct Heq;eauto;eapply deq_loop_exited;eauto.*)

    (* It is necessary to copy these hypotheses because they are used implicitly in Heq, 
     * and cstr_subtype wouldn't be able to modify Hexit1 & Hexit2. *)
    copy D D'.
    (* Construct the imploded type for them *)
    cstr_subtype Hq1. cstr_subtype Hq2.  cstr_subtype He1. cstr_subtype He2. cstr_subtype Hh.
    (* Lift all some properties to the imploded graph *)
    cbn in Heqn.

    eapply eqn_ndeq in Heqn as Hndeq.
    eapply eqn_sdeq in Heqn as Hsdeq.
    
    specialize (get_ocnc_spec Hndeq Hsdeq) as Hocnc.
    pose (s'' := impl_of_original' (p:=s') (Hs' _ Hndeq Hsdeq)).
    eapply lift_disjPaths in D'. 2:cbn;reflexivity. 2,3:auto.
    2: { instantiate (1:= s''). cbn. eapply Hocnc. } 
    
    eapply lc_disj_exits_lsplits_base in D'.
    2: { match goal with |- _ = ?a => assert (a = depth q1) end.
         - eapply impl_depth_self_eq. cbn. reflexivity.
         - setoid_rewrite H.
           admit.
    }
    setoid_rewrite splits'_spec.
    right.
    pose (t1' := impl_tlist q1 t1).
    pose (t2' := impl_tlist q1 t2). 
    pose (qs1' := fst (get_succ (s'',j1) (↓ purify He1, tl j1) t1')).
    pose (qs2' := fst (get_succ (s'',j1) (↓ purify He2, tl j2) t2')).
    exists (`s''), (`qs1'), (`qs2').
    split.
    + eapply splits'_loop_splits__imp. cbn.
      * eapply eq_loop_exiting;eauto with disjPaths.
      * eauto. 
    (* consequence of Hlc' *)
    + (* we will apply the IH in four similar cases in two different ways, 
         therefore all the assumption of IHn are shown before the cases destinction *)
      assert (exists qe1 n1, exit_edge s') qe1 (` qs1') /\ (`qs1',j1) ≻ (qe1,n1 :: j1) | (r1 :r: (s,k)))
        as [qe1 [n1 [Hqee1 Hqes1]]].
      { eapply ex_s_exiting1;eauto. } 
      (*assert (depth (C:=C') (q1') = depth q1) as Hdep''.
      { setoid_rewrite impl_depth_self_eq;[reflexivity| cbn; eauto]. }
      setoid_rewrite Hdep'' in Hdep'. clear Hdep''.*)
      assert (exists qe2 n2, exit_edge (` s') qe2 (` qs2') /\ (`qs2',j1) ≻ (qe2,n2 :: j1) | (r2 :r: (s,k)))
        as [qe2 [n2 [Hqee2 Hqes2]]].
      { eapply ex_s_exiting2;eauto. }
      pose (rr1 := prefix_nincl (` qs1',j1) r1).
      pose (rr2 := prefix_nincl (` qs2',j1) r2).
      pose (tt1 := rr1 :r: (s,k) ++ prefix_nincl (s,k) t1).
      pose (tt2 := rr2 :r: (s,k) ++ prefix_nincl (s,k) t2).
      assert (last_common' tt1 tt2 rr1 rr2 (s, k)) as Hlc_ih.
      { eapply impl_shift_lc;eauto. }
      specialize (r1_tpath Hlc Hpath1) as Hr1.
      specialize (r2_tpath Hlc Hpath2) as Hr2.
      assert (n = depth s - depth qe1) as Hdep1.
      {
        cbn in Heqn.
        assert (depth qe1 = depth (`s')).
        { eapply eq_loop_exiting in Hqee1. rewrite Hqee1. eauto. }
        rewrite H.
        unfold s'.
        setoid_rewrite <-S_depth_s;eauto.
        setoid_rewrite dep_eq;eauto.
        clear - Heqn Hsdeq.
        eapply deq_loop_depth in Hsdeq;eauto.
        cbn in *. omega.
      }
      assert (n = depth s - depth qe2) as Hdep2.
      {
        enough (eq_loop qe1 qe2) as Hqe_eq.
        { rewrite <-Hqe_eq. eapply Hdep1. }
        eapply eq_loop_exiting in Hqee1.
        eapply eq_loop_exiting in Hqee2.
        transitivity (` s');eauto. symmetry;eauto.
      }
      assert (TPath (root, start_tag) (qe1, n1 :: j1) tt1) as Hpathtt1.
      {
        eapply tpath_shift. 2: eapply Hpath1. all:cbn;eauto.
        eapply last_common_in1. eapply last_common'_iff. do 2 eexists;eauto.
      }
      assert (TPath (root, start_tag) (qe2, n2 :: j1) tt2) as Hpathtt2.
      {
        eapply tpath_shift. 2: eapply Hpath2. all:cbn;eauto.
        eapply last_common'_sym in Hlc. eapply last_common_in1.
        eapply last_common'_iff. do 2 eexists;eauto.
      }
(*     *)
      assert ((qs1, js1) ≻ (s, k) | (` qs1', j1) :: tt1) as Hsucctt1.
      { eapply impl_shift_succ1;eauto. }      
      assert ((qs2, js2) ≻ (s, k) | (` qs2', j1) :: tt2) as Hsucctt2.
      { eapply impl_shift_succ2;eauto. }
(*  *)
      (* case distinction on trichotomy: we have to distinguish different cases,
         because the IHn can be applied in two different, symmetrical ways *)
      specialize (Nat.lt_trichotomy n1 n2) as Nrel.
      destruct Nrel as [Nlt|[Neq|Nlt]]; [left| |right].
      * eapply IHn. 
        1-5,9: solve [eauto]. 2-4: solve [cbn;eauto].
        -- intro N. exfalso. inversion N. clear - Nlt H0. omega. 
        -- cbn. clear - Nlt. omega.
      * eapply f_equal with (f:=fun x => hd 0 (x :: j1)) in Neq as Neq'.
        eapply hd_eq_eq in Neq';eauto. 
        eapply disj_latch_path_or in Neq';eauto. 2:subst n1;cbn;eauto.
        destruct Neq' as [π [[Hpathπ Hdisjπ]|[Hpathπ Hdisjπ]]];[left|right].
        -- eapply IHn.
           1-5,7,9: solve [eauto]. 1-3: solve [cbn;eauto].
           cbn. clear - Neq. omega.
        -- eapply splits'_sym.
           eapply IHn.
           1: eapply last_common'_sym.
           1-5,7,9: solve [eauto]. 1-3: solve [cbn;eauto].
           cbn. clear - Neq. omega.
      * eapply splits'_sym.
        eapply IHn.
        1: eapply last_common'_sym.
        1-5,9: solve [eauto]. 2-4: solve [cbn;eauto].
        -- intro N. exfalso. inversion N. clear - Nlt H0. omega.
        -- cbn. clear - Nlt. omega.
           (* show that qq & qq' are exit_edges of s' on H, then construct the coresponding paths to them
            * and show that last_common holds for these paths, bc they are subpaths. 
            * then exploit IHn, use resulting qq_ih & qq'_ih as witnesses, choose the complicated case,
            * there s',qq,qq' are the witnesses and you get one condition by IHn and the other by Hlc'0 *)
Qed.


End disj.


  

Definition imploding_head `(C : redCFG) h p := exists e, exited p e /\ eq_loop h e.

Section ocnc.
  Context `{C : redCFG}.
  Variables (s q : Lab).
  Definition get_ocnc_loop : Lab
    := if (decision (s = q)) then s else q.
  Hypotheses (Hndeq : ~ deq_loop q s)
             (Hdeq : deq_loop s q).
  (* Let get_ocnc_loop be the outermost loop such that
   * - loop_contains (`s'') s (i.e. in the non-imploded CFG it contains s)
   * - ~ deq_loop q (`s'') (i.e. in the non-imploded CFG it does not contain q *)
                              

  Lemma ocnc_in_s
    : loop_contains get_ocnc_loop s.
  Proof.
  Admitted.
  
  Lemma q_ndeq_ocnc
    : ~ deq_loop q get_ocnc_loop.
  Proof.
  Admitted.
    
  Lemma outermost_ocnc
    : forall x : Lab, loop_contains x s -> ~ deq_loop q x
                 -> deq_loop x get_ocnc_loop.
  Proof.
  Admitted.
  
  Lemma implode_nodes_ocnc
    : implode_nodes C q get_ocnc_loop.
  Admitted.
End ocnc.

Section lift_one.

  Context `(C : redCFG).
  Variables (s q : Lab).
  Variables (h' q' e' : local_impl_CFG_type C q)
            (t : list (Lab * Tag)) (j : Tag).
  Local Definition C'' := local_impl_CFG C q.
  Local Definition s'' := get_ocnc_loop s q.

  Definition s' := impl_of_original' implode_nodes_ocnc. 
  
  Lemma S_depth_s
    : S (depth (C:=C'') s') = depth s''.
    (* as s'' is the an outermost loop head not containing q, 
     * implosion reduces its depth by one *)
  Admitted.
  
  Lemma impl_lift_exit_edge 
        (Hexit : exit_edge (`h') (`q') (`e'))
    : exit_edge (redCFG:= local_impl_CFG C q) h' q' e'.
  Proof.
    clear - Hexit.
    (* if a q' -> e' is a loop exit of h' in C
     * and q',e' and h' all still exist in the imploded CFG
     * then this edge is still such a loop exit,
     * because implosion only removes edges adjacent to removed nodes *)
  Admitted.

  Local Definition t' := impl_tlist q t.

  Lemma impl_lift_tpath
        (Hpath : TPath (root,start_tag) (`q',j) t)
    : TPath (C:=C'') (↓ purify_implode q, start_tag) (q', j) t'.
    clear - Hpath.
  Admitted.
    
  Lemma ex_s_exit (x' : local_impl_CFG_type C q) i i'
        (Hsucc : (x',i') ≻ (s',i) | (e',tl j) :: t')
    : exited (s'') (` x').
  Proof.
    clear - Hsucc.
  Admitted.

End lift_one.

Lemma tpath_shift `(C : redCFG) (q qe s : Lab) (j i k : Tag) (q' e' s' : local_impl_CFG_type C q) n
      (t : list Coord) (t' : list (local_impl_CFG_type C q * Tag)) r
      (Heq : eq_loop q (` q'))
      (Hpath : TPath (root, start_tag) (` q', j) t)
      (Hr : TPath (s, k) (` q', j) (r :r: (s, k)))
      (Hel : (s, k) ∈ t)
      (qs' := fst (get_succ (s', i) (e', tl j) t') : local_impl_CFG_type C q)
      (Hqes1 : (` qs', i) ≻ (qe, n :: i) | r :r: (s, k))
      (rr := prefix_nincl (` qs', i) r : list (Lab * Tag))
      (tt := (rr :r: (s, k)) ++ prefix_nincl (s, k) t : list (Lab * Tag))
  : TPath (root, start_tag) (qe, n :: i) tt.
Proof.
  subst tt.
  fold (tl ((s,k) :: prefix_nincl (s,k) t)). 
  eapply path_app'.
  ++ eapply path_prefix_path; [eauto|eapply Hpath|]. eapply prefix_nincl_prefix.
     eauto.
  ++ eapply path_prefix_path in Hr;cycle 1.
     ** specialize (prefix_nincl_prefix' r (`qs',i)) as Hrr.
        eapply prefix_rcons in Hrr. rewrite rcons_cons' in Hrr. eauto.
     ** subst rr.
        
        enough ((qe,n :: i) = hd (s,k) (prefix_nincl (` qs',i) r :r: (s,k))).
        { admit. }
        admit. (* critical *) 
Admitted.

Module Lift.
Section lift.
  Context `(C : redCFG).
  Variables (s q1 qs1 qs2 : Lab) (h' q1' q2' e1' e2' : local_impl_CFG_type C q1)
            (t1 t2 : list (Lab * Tag)) (r1 r2 : list (Lab * Tag)) (k j1 j2 js1 js2 : Tag).
  Hypotheses (Hlc : last_common' t1 t2 r1 r2 (s, k))
             (Hpath1 : TPath (root, start_tag) (`q1', j1) t1)
             (Hpath2 : TPath (root, start_tag) (`q2', j2) t2)
             (Hexit1 : exit_edge (`h') (`q1') (`e1'))
             (Hexit2 : exit_edge (`h') (`q2') (`e2'))
             (Hsucc1 : (qs1,js1) ≻ (s,k) | (`e1',tl j1) :: t1)
             (Hsucc2 : (qs2,js2) ≻ (s,k) | (`e2',tl j2) :: t2)
             (Hloop : eq_loop (`q1') (`q2'))
             (Hextra : j1 = j2 -> exists π, CPath (` q2') (` h') (π :r: `q2') /\ Disjoint (map fst r1) π)
             (Heq : eq_loop q1 (`q1')).

  Local Definition r1' := impl_tlist q1 r1.
  Local Definition r2' := impl_tlist q1 r2.
  Local Definition C' := C'' C q1.
  Local Definition Lab' := local_impl_CFG_type C q1.
  Local Definition t1' := t' C q1 t1. 
  Local Definition t2' := t' C q1 t2.

  Lemma impl_lift_tpath1
    : TPath (C:=C') (↓ purify_implode q1, start_tag) (q1', j1) t1'.
  Proof.
    eapply impl_lift_tpath;eauto.
  Qed.

  Lemma impl_lift_tpath2
    : TPath (C:=C') (↓ purify_implode q1, start_tag) (q2', j2) t2'.
  Proof.
    eapply impl_lift_tpath;eauto.
  Qed.

  Lemma impl_lift_exit1
    : exit_edge (redCFG:=C') h' q1' e1'.
  Proof.
    eapply impl_lift_exit_edge;eauto.
  Qed.

  Lemma impl_lift_exit2
    : exit_edge (redCFG:=C') h' q2' e2'.
  Proof.
    eapply impl_lift_exit_edge;eauto.
  Qed.

  Lemma impl_lift_extra
    : j1 = j2 -> exists π, CPath (H:=C') q2' h' (π :r: q2') /\ Disjoint (map fst r1') π.
    intro H. exploit Hextra.
    clear - Hextra.
  Admitted.

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
  
  (** step case **)
  
  Hypotheses (Hndeq : ~ deq_loop q1 s)
             (Hsdeq : deq_loop s q1).
    
  Local Definition s' := s' q1.

  Lemma impl_lift_lc
    : last_common' t1' t2' r1' r2' (s',j1).
  Admitted.
                             
  Local Definition qs1' := fst (get_succ (s', j1) (e1', tl j1) t1').
  Local Definition qs2' := fst (get_succ (s', j1) (e2', tl j2) t2').

  Lemma s_in_t1'
    : (s',j1) ∈ t1'.
  Proof.
    eapply last_common_in1. eapply last_common'_iff. do 2 eexists;eauto using impl_lift_lc.
  Qed.
    
  Lemma s_in_t2'
    :(s',j1) ∈ t2'.
  Proof.
    eapply last_common_in1. eapply last_common_sym. eapply last_common'_iff.
    do 2 eexists;eauto using impl_lift_lc.
  Qed.

  Lemma dep_eq
    : depth (C:=C') s' = depth q1.
  Proof.
    eapply Nat.le_antisymm.
    - eapply impl_depth_max.
    - setoid_rewrite impl_depth_self_eq at 1. 2:eauto.
      clear - Hndeq Hsdeq.
  Admitted.
  
  Lemma impl_lift_succ1
    : (qs1',j1) ≻ (s',j1) | (e1', tl j1) :: t1'.
    (* the tag j1 is correct, because in the step case there would be a double exit otherwise 
     * the assumption has to be stated with the (e,tl j1) :: ..  because in the base case 
     * qs = e might hold 
     *)
  Admitted.

  Lemma impl_lift_succ2
    : (qs2',j1) ≻ (s',j1) | (e2', tl j2) :: t2'.
  Admitted.
  
  Lemma ex_s_exit1
    : exited (` s') (` qs1').
  Proof.
    eapply ex_s_exit;eauto.
    eapply impl_lift_succ1.
  Qed.

  Lemma ex_s_exit2
    : exited (` s') (` qs2').
  Proof.
    eapply ex_s_exit;eauto.
    eapply impl_lift_succ2.
  Qed.

  Lemma ex_s_exiting1
    : exists qe1 n1, exit_edge (` s') qe1 (` qs1') /\ (`qs1',j1) ≻ (qe1,n1 :: j1) | (r1 :r: (s,k)).
  Proof.
    eapply (exit_succ_exiting (C:=C)).
    - eapply r1_tpath;eauto.
    - eapply ex_s_exit1;eauto. 
    - unfold qs1'. admit.
  Admitted.
    
  Lemma ex_s_exiting2
    : exists qe2 n2, exit_edge (` s') qe2 (` qs2') /\ (`qs2',j1) ≻ (qe2,n2 :: j1) | (r2 :r: (s,k)).
  Proof.
    eapply (exit_succ_exiting (C:=C)).
    - eapply r2_tpath;eauto.
    - eapply ex_s_exit2;eauto. 
    - unfold qs2'. admit.
  Admitted.
  
  Local Definition rr1 := prefix_nincl (` qs1',j1) r1.
  Local Definition rr2 := prefix_nincl (` qs2',j1) r2.
  Local Definition tt1 := rr1 :r: (s,k) ++ prefix_nincl (s,k) t1.
  Local Definition tt2 := rr2 :r: (s,k) ++ prefix_nincl (s,k) t2.
  
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
  
End lift.
End Lift.

Import Lift.

Section lsplits.
  Context `(C : redCFG).
  Variables (s e1 e2 q1 q2 qs1 qs2 h : Lab) (j1 j2 k js1 js2 : Tag)
            (t1 t2 : list (@Coord Lab)) (r1 r2 : list (@Coord Lab)).
  Hypotheses (Hlc : last_common' t1 t2 r1 r2 (s,k))
             (Hpath1 : TPath (root,start_tag) (q1,j1) t1)
             (Hpath2 : TPath (root,start_tag) (q2,j2) t2)
             (Hexit1 : exit_edge h q1 e1)
             (Hexit2 : exit_edge h q2 e2)
             (Htag : tl j1 = tl j2)
             (Htagle : hd 0 j1 <= hd 0 j2)
             (Hextra : j1 = j2 -> exists π, CPath q2 h (π :r: q2) /\ Disjoint (map fst r1) π)
             (Hsucc1 : (qs1,js1) ≻ (s,k) | (e1,tl j1) :: t1)
             (Hsucc2 : (qs2,js2) ≻ (s,k) | (e2,tl j2) :: t2).


  Local Lemma Heq : eq_loop q1 q2.
  Proof.
    eapply q1_eq_q2;eauto.
  Qed.

  Hint Immediate Heq.

  Local Lemma Hq1 : implode_nodes (head_exits_CFG C q1) q1 q1.
  Proof.
    left. reflexivity.
  Qed.

  Local Lemma Hq2 : implode_nodes (head_exits_CFG C q1) q1 q2.
  Proof.
    eapply head_exits_implode_nodes_inv1;left. apply Heq.
  Qed.
  
  Local Lemma He1 : implode_nodes (head_exits_CFG C q1) q1 e1.
  Proof.
    eapply head_exits_implode_nodes_inv1;left; eauto using deq_loop_exited.
  Qed.

  Hint Resolve Heq deq_loop_exited eq_loop1 eq_loop2 deq_loop_exiting eq_loop_exiting : deq.
  
  Local Lemma He2 : implode_nodes (head_exits_CFG C q1) q1 e2.
  Proof.
    eapply head_exits_implode_nodes_inv1;left; eauto using deq_loop_exited.
    eauto with deq.
  Qed.
  
  Local Lemma Hh : implode_nodes (head_exits_CFG C q1) q1 h.
  Proof.
    eapply head_exits_implode_nodes_inv1;left.
    eapply eq_loop_exiting;eauto.
  Qed.

  Local Lemma Hlc'
        (Hsdeq : deq_loop s q1)
        (Hndeq : ~ deq_loop q1 s)
    : last_common' (Lift.t1' C q1 t1) (Lift.t2' C q1 t2) (Lift.r1' C q1 r1) 
                   (Lift.r2' C q1 r2) (Lift.s' C q1, j1).
  Proof.
    cstr_subtype Hq1. cstr_subtype Hq2. cstr_subtype Hh. cstr_subtype He1. cstr_subtype He2.
    cbn in Hsdeq,Hndeq. 
    eapply impl_lift_lc. all:eauto;cbn in *; auto.
  Qed.

  Local Lemma Hsucc1'
        (Hsdeq : deq_loop s q1)
        (Hndeq : ~ deq_loop q1 s)
    : (Lift.qs1' (↓ purify He1) t1 j1, j1) ≻ (Lift.s' C q1, j1)
  | (↓ purify He1, tl j1) :: Lift.t1' C q1 t1.
  Proof.
    cstr_subtype Hq1. cstr_subtype Hq2. cstr_subtype Hh. cstr_subtype He1. cstr_subtype He2.
    eapply impl_lift_succ1;eauto;cbn in *;auto.
  Qed.
  
  Local Lemma Hsucc2'
        (Hsdeq : deq_loop s q1)
        (Hndeq : ~ deq_loop q1 s)
    : (Lift.qs2' (↓ purify He2) t2 j1 j2, j1) ≻ (Lift.s' C q1, j1)
  | (↓ purify He2, tl j2) :: Lift.t2' C q1 t2.
  Proof.
    cstr_subtype Hq1. cstr_subtype Hq2. cstr_subtype Hh. cstr_subtype He1. cstr_subtype He2.
    eapply impl_lift_succ2;eauto;cbn in *;auto.
  Qed.

(*  Local Arguments depth {_ _ _ _} _.
  Local Lemma Hdep'
        (Hsdeq : deq_loop s q1)
        (Hndeq : ~ deq_loop q1 s)
    : depth (Lift.C' C q1) (Lift.s' C q1) = depth (Lift.C' C q1) (↓ purify Hq1).
  Proof.
    unfold Lift.C', C''. unfold Lift.s'. 
    setoid_rewrite impl_depth_self_eq at 2. [|eauto]. eapply dep_eq;eauto.*)
  
Theorem lc_disj_exits_lsplits'
  : (s,qs1,qs2) ∈ splits' h e1.
Proof.
  remember (depth s - depth q1).
  revert Htag Htagle.
  revert dependent Lab. clear.
  revert j1 j2 k js1 js2. 
  induction n;intros.
  - eapply lc_disj_exits_lsplits_base';eauto.
    enough (depth q1 <= depth s) by omega.
    eapply deq_loop_depth.
    eapply s_deq_q;eauto.
  - (* Show that some interesting nodes are in the imploded CFG *)
(*    assert (implode_nodes (head_exits_CFG C q1) q1 q1) as Hq1.
    { left. reflexivity. }
    enough (implode_nodes (head_exits_CFG C q1) q1 q2) as Hq2.
    enough (implode_nodes (head_exits_CFG C q1) q1 e1) as He1.
    enough (implode_nodes (head_exits_CFG C q1) q1 e2) as He2.
    enough (implode_nodes (head_exits_CFG C q1) q1 h) as Hh.
    2-5: eapply head_exits_implode_nodes_inv1;left; eauto using deq_loop_exited.
    2: eapply eq_loop_exiting;eauto. 3: destruct Heq;eauto.
    2: transitivity q2;destruct Heq;eauto;eapply deq_loop_exited;eauto.*)

    (* It is necessary to copy these hypotheses because they are used implicitly in Heq, 
     * and cstr_subtype wouldn't be able to modify Hexit1 & Hexit2. *)
    copy Hexit1 Hexit1''. copy Hexit2 Hexit2''.
    (* Construct the imploded type for them *)
    cstr_subtype Hq1. cstr_subtype Hq2.  cstr_subtype He1. cstr_subtype He2. cstr_subtype Hh.
    (* Lift all some properties to the imploded graph *)
    cbn in Heqn.
    eapply eqn_ndeq in Heqn as Hndeq.
    eapply eqn_sdeq in Heqn as Hsdeq . 2-11:eauto. 
    eapply impl_lift_exit1 in Hexit1'' as Hexit1'.
    eapply impl_lift_exit2 in Hexit2'' as Hexit2'.
    eapply impl_lift_tpath1 in Hpath1 as Hpath1'.
    eapply impl_lift_tpath2 in Hpath2 as Hpath2'.
    specialize Hlc' as Hlc'. exploit Hlc'.
    eapply lc_disj_exits_lsplits_base in Hlc'. 2-8: solve [eauto].
    2,3: eauto using impl_lift_succ2, impl_lift_succ1.
    3: { intros jeq; exploit' Hextra; eapply impl_lift_extra;eauto. }
          Local Arguments depth {_ _ _ _} _.
    2: { setoid_rewrite impl_depth_self_eq at 2;[|eauto]. eapply dep_eq;eauto. }

      idtac.
      unfold Lift.C', C''.
      
      specialize (@impl_depth_self_eq _ _ _ _ C q1 (↓ purify Hq1)) as Q.
      unfold "`" in Q. symmetry.
      clear - Q.
      setoid_rewrite Q.
      - admit.
      - eapply dep_eq.
      admit. } (*
      unfold Lift.s'.
      setoid_rewrite impl_depth_self_eq.
      3:cbn;reflexivity.
      1:reflexivity.
      eapply dep_eq;eauto. } *)
    setoid_rewrite splits'_spec.
    right.
    pose (s' := s'' C q1). 
    pose (t1' := t' C q1 t1).
    pose (t2' := t' C q1 t2).
    pose (qs1' := fst (get_succ (s',j1) (↓ purify He1, tl j1) t1')).
    pose (qs2' := fst (get_succ (s',j1) (↓ purify He2, tl j2) t2')).
    exists (`s'), (`qs1'), (`qs2').
    split.
    + eapply splits'_loop_splits__imp. cbn.
      * rewrite Heq. eapply eq_loop_exiting;eauto.
      * eauto. 
    (* consequence of Hlc' *)
    + (* we will apply the IH in four similar cases in two different ways, 
         therefore all the assumption of IHn are shown before the cases destinction *)
      assert (exists qe1 n1, exit_edge (` s') qe1 (` qs1') /\ (`qs1',j1) ≻ (qe1,n1 :: j1) | (r1 :r: (s,k)))
        as [qe1 [n1 [Hqee1 Hqes1]]].
      { eapply ex_s_exiting1;eauto. } 
      (*assert (depth (C:=C') (q1') = depth q1) as Hdep''.
      { setoid_rewrite impl_depth_self_eq;[reflexivity| cbn; eauto]. }
      setoid_rewrite Hdep'' in Hdep'. clear Hdep''.*)
      assert (exists qe2 n2, exit_edge (` s') qe2 (` qs2') /\ (`qs2',j1) ≻ (qe2,n2 :: j1) | (r2 :r: (s,k)))
        as [qe2 [n2 [Hqee2 Hqes2]]].
      { eapply ex_s_exiting2;eauto. }
      pose (rr1 := prefix_nincl (` qs1',j1) r1).
      pose (rr2 := prefix_nincl (` qs2',j1) r2).
      pose (tt1 := rr1 :r: (s,k) ++ prefix_nincl (s,k) t1).
      pose (tt2 := rr2 :r: (s,k) ++ prefix_nincl (s,k) t2).
      assert (last_common' tt1 tt2 rr1 rr2 (s, k)) as Hlc_ih.
      { eapply impl_shift_lc;eauto. }
      specialize (r1_tpath Hlc Hpath1) as Hr1.
      specialize (r2_tpath Hlc Hpath2) as Hr2.
      assert (n = depth s - depth qe1) as Hdep1.
      {
        cbn in Heqn.
        assert (depth qe1 = depth (`s')).
        { eapply eq_loop_exiting in Hqee1. rewrite Hqee1. eauto. }
        rewrite H.
        unfold s'.
        setoid_rewrite <-S_depth_s;eauto.
        setoid_rewrite dep_eq;eauto.
        clear - Heqn Hsdeq.
        eapply deq_loop_depth in Hsdeq;eauto.
        cbn in *. omega.
      }
      assert (n = depth s - depth qe2) as Hdep2.
      {
        enough (eq_loop qe1 qe2) as Hqe_eq.
        { rewrite <-Hqe_eq. eapply Hdep1. }
        eapply eq_loop_exiting in Hqee1.
        eapply eq_loop_exiting in Hqee2.
        transitivity (` s');eauto. symmetry;eauto.
      }
      assert (TPath (root, start_tag) (qe1, n1 :: j1) tt1) as Hpathtt1.
      {
        eapply tpath_shift. 2: eapply Hpath1. all:cbn;eauto.
        eapply last_common_in1. eapply last_common'_iff. do 2 eexists;eauto.
      }
      assert (TPath (root, start_tag) (qe2, n2 :: j1) tt2) as Hpathtt2.
      {
        eapply tpath_shift. 2: eapply Hpath2. all:cbn;eauto.
        eapply last_common'_sym in Hlc. eapply last_common_in1.
        eapply last_common'_iff. do 2 eexists;eauto.
      }
(*     *)
      assert ((qs1, js1) ≻ (s, k) | (` qs1', j1) :: tt1) as Hsucctt1.
      { eapply impl_shift_succ1;eauto. }      
      assert ((qs2, js2) ≻ (s, k) | (` qs2', j1) :: tt2) as Hsucctt2.
      { eapply impl_shift_succ2;eauto. }
(*  *)
      (* case distinction on trichotomy: we have to distinguish different cases,
         because the IHn can be applied in two different, symmetrical ways *)
      specialize (Nat.lt_trichotomy n1 n2) as Nrel.
      destruct Nrel as [Nlt|[Neq|Nlt]]; [left| |right].
      * eapply IHn. 
        1-5,9: solve [eauto]. 2-4: solve [cbn;eauto].
        -- intro N. exfalso. inversion N. clear - Nlt H0. omega. 
        -- cbn. clear - Nlt. omega.
      * eapply f_equal with (f:=fun x => hd 0 (x :: j1)) in Neq as Neq'.
        eapply hd_eq_eq in Neq';eauto. 
        eapply disj_latch_path_or in Neq';eauto. 2:subst n1;cbn;eauto.
        destruct Neq' as [π [[Hpathπ Hdisjπ]|[Hpathπ Hdisjπ]]];[left|right].
        -- eapply IHn.
           1-5,7,9: solve [eauto]. 1-3: solve [cbn;eauto].
           cbn. clear - Neq. omega.
        -- eapply splits'_sym.
           eapply IHn.
           1: eapply last_common'_sym.
           1-5,7,9: solve [eauto]. 1-3: solve [cbn;eauto].
           cbn. clear - Neq. omega.
      * eapply splits'_sym.
        eapply IHn.
        1: eapply last_common'_sym.
        1-5,9: solve [eauto]. 2-4: solve [cbn;eauto].
        -- intro N. exfalso. inversion N. clear - Nlt H0. omega.
        -- cbn. clear - Nlt. omega.
           (* show that qq & qq' are exit_edges of s' on H, then construct the coresponding paths to them
            * and show that last_common holds for these paths, bc they are subpaths. 
            * then exploit IHn, use resulting qq_ih & qq'_ih as witnesses, choose the complicated case,
            * there s',qq,qq' are the witnesses and you get one condition by IHn and the other by Hlc'0 *)
Qed.

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

Theorem lc_disj_exits_lsplits `{redCFG}
          (s e1 e2 q1 q2 h : Lab) (i j1 j2 k : Tag) (t1 t2 : list Coord)
          (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
          (Hexit1 : exit_edge h q1 e1)
          (Hexit2 : exit_edge h q2 e2)
          (Hpath1 : TPath (root,start_tag) (e1,i) ((e1,i) :: (q1,j1) :: t1))
          (Hpath2 : TPath (root,start_tag) (e2,i) ((e2,i) :: (q2,j2) :: t2))
          (Hneq : j1 <> j2)
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
  destruct Nrel as [Nlt|[Neq|Nlt]];[|exfalso|].
  - do 2 eexists.
    left. eapply lc_disj_exits_lsplits';eauto.
    3,4:rewrite <-surjective_pairing;eapply get_succ_cons.
    4: eapply last_common'_sym in Hlc.
    3,4: eapply last_common_in1;eapply last_common'_iff;do 2 eexists;eauto.
    + omega.
    + intro N. contradiction.
  - eapply hd_eq_eq in Neq;eauto. 
  - do 2 eexists.
    right. eapply lc_disj_exits_lsplits'.
    1: eapply last_common'_sym in Hlc;eauto.
    all: eauto.
    3,4:rewrite <-surjective_pairing;eapply get_succ_cons.
    3: eapply last_common'_sym in Hlc.
    3,4: eapply last_common_in1;eapply last_common'_iff;do 2 eexists;eauto.
    + omega.
    + intro N. rewrite N in Hneq. contradiction.
Qed.

Corollary lc_disj_exit_lsplits `{redCFG} (s e q1 q2 h : Lab) (i j1 j2 k : Tag) (t1 t2 : list Coord)
          (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
          (Hexit1 : exit_edge h q1 e)
          (Hexit2 : exit_edge h q2 e)
          (Hpath1 : TPath (root,start_tag) (e,i) ((e,i) :: (q1, j1) :: t1))
          (Hpath2 : TPath (root,start_tag) (e,i) ((e,i) :: (q2, j2) :: t2))
          (Hneq : j1 <> j2)
  : exists (qq qq' : Lab), (s,qq,qq') ∈ splits' h e.
Proof.
  eapply lc_disj_exits_lsplits in Hlc;eauto.
  destructH. eexists;eexists. destruct Hlc;eauto.
Qed. 
