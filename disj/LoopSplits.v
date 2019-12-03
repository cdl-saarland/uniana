Require Export EqNeqDisj SplitsDef GetSucc.

Section disj.
  Context `(C : redCFG).

  Variable (t1 t2 : ne_list (Lab * Tag)) (r1 r2 : list (Lab * Tag)) (q1 q2 s : Lab) (j1 j2 k : Tag).
  Hypotheses (Hlc : last_common' t1 t2 r1 r2 (s,k))
             (Hpath1 : TPath (root,start_tag) (q1,j1) t1)
             (Hpath2 : TPath (root,start_tag) (q2,j2) t2)
             (*           (Hneq : r1 <> r2) (* <-> r1 <> nil \/ r2 <> nil *)*)
             (Hloop : eq_loop q1 q2)
             (Htag : tl j1 = tl j2)
             (Htagleq : hd 0 j1 <= hd 0 j2).

  Notation "pi -t> qj" := (tcfg_edge pi qj = true) (at level 50).

  Variables  (e1 e2 h qs1 qs2 : Lab) (js1 js2 : Tag).
  Hypotheses (Hexit1 : exit_edge h q1 e1)
             (Hexit2 : exit_edge h q2 e2)
             (Hsucc1 : (qs1, js1) ≻ (s, k) | (e1, tl j1) :: t1)
             (Hsucc2 : (qs2, js2) ≻ (s, k) | (e2, tl j2) :: t2).

  Lemma lc_disj_exits_lsplits_base_lt
        (Hdep : depth s = depth q1)
        (Htaglt : hd 0 j1 < hd 0 j2)
    : ( s, qs1, qs2) ∈ loop_splits C h e1.
  Proof.
  Admitted. (* FIXME *)
  
  Lemma lc_disj_exits_lsplits_base_eq π
          (Hdep : depth s = depth q1)
          (Htageq : j1 = j2)
          (Hlatchp : CPath q2 h (π >: q2))
          (Hlatchd : Disjoint (map fst r1) π)
    : (s,qs1,qs2) ∈ loop_splits C h e1.
  Proof.
  Admitted. (* FIXME *)

  Lemma hd_eq_eq
        (Hheq : hd 0 j1 = hd 0 j2)
    : j1 = j2.
  Proof.
    clear - Hexit1 Hexit2 Hpath1 Hpath2 Hheq Htag.
    eapply eq_loop_exiting in Hexit1.
    eapply eq_loop_exiting in Hexit2.
    eapply hd_tl_len_eq;eauto.
    erewrite tag_depth. 2:eapply Hpath1.
    erewrite tag_depth. 2:eapply Hpath2.
    2,3: eapply path_contains_front;eauto.
    rewrite <-Hexit1. rewrite <-Hexit2. reflexivity.
  Qed.
  
  Corollary lc_disj_exits_lsplits_base
          (Hdep : depth s = depth q1)
          (Hextra : j1 = j2 -> exists π, CPath q2 h (π >: q2) /\ Disjoint (map fst r1) π)
    : (s,qs1,qs2) ∈ loop_splits C h e1.
  Proof.
    eapply le_lt_or_eq in Htagleq as Q. 
    destruct Q.
    - eapply lc_disj_exits_lsplits_base_lt;eauto.
    - eapply hd_eq_eq in H. exploit Hextra. destructH.
      eapply lc_disj_exits_lsplits_base_eq;eauto.
  Qed.
    
  Corollary lc_disj_exits_lsplits_base'
          (Hdep : depth s = depth q1)
          (Hextra : j1 = j2 -> exists π, CPath q2 h (π >: q2) /\ Disjoint (map fst r1) π)
    : (s,qs1,qs2) ∈ splits' h e1.
  Proof.
    rewrite splits'_spec. left.
    eapply lc_disj_exits_lsplits_base;eauto.
  Qed.
  
  Lemma disj_latch_path_or
        (Heq : j1 = j2)
    : exists π, (CPath q2 h (π >: q2) /\ Disjoint (map fst r1) π)
           \/ (CPath q1 h (π >: q1) /\ Disjoint (map fst r2) π).
  Proof.
    destruct Hexit1 as [Hin1 [Hnin1 Hedge1]].
    destruct Hexit2 as [Hin2 [Hnin2 Hedge2]].
    copy Hin1 Hin1'. copy Hin2 Hin2'.
    unfold loop_contains in Hin1, Hin2.
    destruct Hin1 as [p1 [ϕ1 [Hb1 [Hp1 Htl1]]]].
    destr_r ϕ1.
    path_simpl' Hp1.
    decide (exists x, x ∈ map fst r2 /\ x ∈ (h :: l)).
    - destruct Hin2 as [p2 [ϕ2 [Hb2 [Hp2 Htl2]]]].
      destr_r ϕ2.
      path_simpl' Hp2.
      decide (exists y, y ∈ map fst r1 /\ y ∈ (h :: l0)).
      + exfalso.
        rename e into Hx.
        rename e0 into Hy.
        do 2 destructH.
        destruct Hy1;[subst y;eapply no_head;eauto|].
        destruct Hx1.
        {
          subst x. eapply no_head. 1: eapply last_common'_sym. all: eauto.
          - symmetry;eauto.
          - rewrite Heq. eauto.
        }
        destruct l;[inversion H0|].
        destruct l0;[inversion H|].
        cbn in Hp1, Hp2.
        rewrite nl_cons_lr_shift in Hp1.
        rewrite nl_cons_lr_shift in Hp2.
        eapply path_nlrcons_edge in Hp1 as Hedge1'.
        eapply path_nlrcons_edge in Hp2 as Hedge2'.
        eapply path_rcons_inv in Hp1. destructH.
        eapply path_rcons_inv in Hp2. destructH.
        replace (ne_back (e :< l)) with p in *.
        2: { symmetry. eapply path_back;eauto. }
        replace (ne_back (e0 :< l0)) with p0 in *.
        2: { symmetry. eapply path_back;eauto. }
        (* construct paths to the q's *)
        specialize (r1_tpath Hlc Hpath1) as Hr1.
        eapply TPath_CPath in Hr1. cbn in Hr1. rewrite ne_map_nl_rcons in Hr1. cbn in Hr1.
        specialize (r2_tpath Hlc Hpath2) as Hr2.
        eapply TPath_CPath in Hr2. cbn in Hr2. rewrite ne_map_nl_rcons in Hr2. cbn in Hr2.
        destruct r1 as [|b rr1];[cbn in Hy0;contradiction|].
        destruct r2 as [|c rr2];[cbn in Hx0;contradiction|].
        cbn in Hr1,Hr2.
        rewrite nl_cons_lr_shift in Hr1,Hr2.
        eapply path_rcons_inv in Hr1. destruct Hr1 as [rp1 Hr1].
        eapply path_rcons_inv in Hr2. destruct Hr2 as [rp2 Hr2].
        eapply path_from_elem in Hr1;eauto.
        2: { simpl_nl;eauto. }
        eapply path_from_elem in Hr2;eauto.
        2: simpl_nl;eauto.
        (* construct paths to x & y *)
        eapply path_to_elem in Hp2.
        2: simpl_nl;eauto.
        eapply path_to_elem in Hp1.
        2: simpl_nl;eauto.
        do 4 destructH.
        eapply path_app in Hr0 as HQ;eauto.
        eapply path_app_conc in Hedge1';eauto.
        eapply path_app in Hedge1';eauto.
        eapply path_rcons in Hedge1';eauto.
        eapply dom_self_loop in Hedge1'.
        * clear - Hedge1'.
          destruct ϕ4;cbn in *.
          all: destruct ϕ;[|destruct ϕ].
          all: destruct ϕ0;[|destruct ϕ0].
          all: destruct ϕ3;cbn in *;congruence.
        * eapply exit_edge_innermost;eapply Hexit2.
        * simpl_nl.
          eapply path_contains_front in Hr0.
          specialize (no_head Hlc Hpath1 Hpath2) as Hnh1. do 3 exploit' Hnh1. specialize (Hnh1 h).
          specialize (no_head (last_common'_sym Hlc) Hpath2 Hpath1) as Hnh2.
          exploit' Hnh2;[symmetry;eauto|]. rewrite Heq in Hnh2.
          do 2 exploit' Hnh2. specialize (Hnh2 h).
          clear - Htl2 Htl1 Hp4 Hr3 Hr4 Hp4 Hp3 Hnh1 Hnh2 Hin1' Hin2' Hr0.
          intro N. eapply in_app_or in N.
          simpl_nl' Htl2. simpl_nl' Htl1. simpl_nl' Hp3. simpl_nl' Hp4. simpl_nl' Hr3. simpl_nl' Hr4.
          rewrite rev_rcons in Htl1.
          rewrite rev_rcons in Htl2.
          unfold tl in Htl1,Htl2.
          rewrite <-in_rev in Htl1,Htl2.
          destruct N. (* special cases : q2 = h & h = s *)
          -- eapply in_app_or in H.
             destruct H;[|eapply Htl2;eapply prefix_incl;eauto;eapply tl_incl;eauto].
             eapply in_app_or in H.
             destruct H;[|eapply Hnh1;[eapply postfix_incl;eauto|eauto]].
             eapply in_app_or in H.
             destruct H;[|eapply Htl1;eapply prefix_incl;eauto;eapply tl_incl;eauto].
             eapply Hnh2;[eapply postfix_incl;eauto|eauto].
          -- cbn in H. destruct H;[|contradiction]. subst a0. eapply Hnh2;eauto.
             eapply postfix_incl; eauto.
      (* q2 ->+ y ->* q1 ->+ x ->* q2 *)
      + exists (h :: l0). left. cbn. split.
        * econstructor;eauto. eapply back_edge_incl;eauto.
        * do 2 simpl_dec' n. intros x H. destruct (n x);[contradiction|auto].
    - exists (h :: l). right. cbn. split.
      + econstructor;eauto. eapply back_edge_incl;eauto.
      + do 2 simpl_dec' n. intros x H. destruct (n x);[contradiction|auto].
  Qed.

  Lemma q1_eq_q2
    : eq_loop q1 q2.
  Proof.
    eapply eq_loop_exiting in Hexit1.
    eapply eq_loop_exiting in Hexit2.
    rewrite <-Hexit1, <-Hexit2.
    reflexivity.
  Qed.
    
End disj.

Hint Resolve q1_eq_q2.

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

Definition imploding_head `(C : redCFG) h p := exists e, exited p e /\ eq_loop h e.

Section lift_one.

  Context `(C : redCFG).
  Variables (s q : Lab).
  Hypotheses (Hndeq : ~ deq_loop q s)
             (Hdeq : deq_loop s q).

  (* Let s'' be the outermost loop such that
   * - loop_contains (`s'') s (i.e. in the non-imploded CFG it contains s)
   * - ~ deq_loop q (`s'') (i.e. in the non-imploded CFG it does not contain q *)
  Parameter s'' : local_impl_CFG_type C q.
  Axiom s_in_s
    : loop_contains (`s'') s.
  Axiom q_ndeq_s'
    : ~ deq_loop q (`s'').
  Axiom outermost_s'
    : forall x : Lab, loop_contains x s -> ~ deq_loop q x
           -> deq_loop x (`s'').

  Variables (h' q' e' : local_impl_CFG_type C q)
            (t : ne_list (Lab * Tag)) (j : Tag).
  Local Definition C'' := local_impl_CFG C q.
(*
  Lemma s_imploding_head
    : imploding_head C q (`s'').
    clear - Hdeq Hndeq.
*)
  
  Lemma S_depth_s
    : S (depth (C:=local_impl_CFG C q) s'') = depth (`s'').
    clear - Hdeq Hndeq.
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

  Local Definition t' := match impl_tlist q t with
                         | nil => ne_single (h',j) (* never happening *)
                         | a :: l => a :< l
                         end.

  Lemma impl_tlist_eq
        (Hpath : TPath (root,start_tag) (`q',j) t)
        (Heq : eq_loop q (`q'))
    : impl_tlist q t = t'.
  Proof.
    eapply impl_tlist_tpath with (h:=q) in Hpath as Hpath'.
    Unshelve.
    2: { eapply implode_nodes_root_inv. } 2: { left. eapply Heq. }
    destruct Hpath'. destruct H.
    unfold t'. destruct impl_tlist.
    - destruct x;cbn in H0;congruence.
    - simpl_nl. reflexivity.
  Qed.

  Lemma impl_lift_tpath
        (Hpath : TPath (root,start_tag) (`q',j) t)
    : TPath (C:=C'') (↓ purify_implode q, start_tag) (q', j) t'.
    clear - Hpath.
  Admitted.
    
  Lemma ex_s_exit (x' : local_impl_CFG_type C q) i i'
        (Hsucc : (x',i') ≻ (s'',i) | (e',tl j) :: t')
    : exited (` s'') (` x').
  Proof.
    clear - Hndeq Hdeq Hsucc.
  Admitted.

End lift_one.

Lemma tpath_shift `(C : redCFG) (q qe s : Lab) (j i k : Tag) (q' e' s' : local_impl_CFG_type C q) n
      (t : ne_list Coord) (t' : ne_list (local_impl_CFG_type C q * Tag)) r
      (Heq : eq_loop q (` q'))
      (Hpath : TPath (root, start_tag) (` q', j) t)
      (Hr : TPath (s, k) (` q', j) (r >: (s, k)))
      (Hel : (s, k) ∈ t)
      (qs' := fst (get_succ (s', i) (e', tl j) t') : local_impl_CFG_type C q)
      (Hqes1 : (` qs', i) ≻ (qe, n :: i) | r :r: (s, k))
      (rr := prefix_nincl (` qs', i) r : list (Lab * Tag))
      (tt := (rr >: (s, k)) :+ prefix_nincl (s, k) t : ne_list (Lab * Tag))
  : TPath (root, start_tag) (qe, n :: i) tt.
Proof.
  subst tt.
  fold (tl ((s,k) :: prefix_nincl (s,k) t)). setoid_rewrite nlcons_to_list.
  eapply path_app.
  ++ eapply path_prefix_path;[eapply Hpath|]. simpl_nl. eapply prefix_nincl_prefix.
     eauto.
  ++ simpl_nl. 
     eapply path_prefix_path in Hr;cycle 1.
     ** simpl_nl. eapply prefix_rcons. eapply prefix_nincl_prefix'.
     ** subst rr.
        enough ((qe,n :: i) = ne_front (prefix_nincl (` qs',i) r >: (s,k))).
        { setoid_rewrite H. eapply Hr. }
        admit. (* critical *) 
Admitted.

Module Lift.
Section lift.
  Context `(C : redCFG).
  Variables (s q1 qs1 qs2 : Lab) (h' q1' q2' e1' e2' : local_impl_CFG_type C q1)
            (t1 t2 : ne_list (Lab * Tag)) (r1 r2 : list (Lab * Tag)) (k j1 j2 js1 js2 : Tag).
  Hypotheses (Hlc : last_common' t1 t2 r1 r2 (s, k))
             (Hpath1 : TPath (root, start_tag) (`q1', j1) t1)
             (Hpath2 : TPath (root, start_tag) (`q2', j2) t2)
             (Hexit1 : exit_edge (`h') (`q1') (`e1'))
             (Hexit2 : exit_edge (`h') (`q2') (`e2'))
             (Hsucc1 : (qs1,js1) ≻ (s,k) | (`e1',tl j1) :: t1)
             (Hsucc2 : (qs2,js2) ≻ (s,k) | (`e2',tl j2) :: t2)
             (Hloop : eq_loop (`q1') (`q2'))
             (Hextra : j1 = j2 -> exists π, CPath (` q2') (` h') (π >: `q2') /\ Disjoint (map fst r1) π)
             (Heq : eq_loop q1 (`q1')).

  Local Definition r1' := impl_tlist q1 r1.
  Local Definition r2' := impl_tlist q1 r2.
  Local Definition C' := C'' C q1.
  Local Definition Lab' := local_impl_CFG_type C q1.
  Local Definition t1' := t' h' t1 j1.
  Local Definition t2' := t' h' t2 j2.
  
  Lemma impl_tlist_eq1
    : impl_tlist q1 t1 = t1'.
  Proof.
    eapply impl_tlist_eq;eauto.
  Qed.
  
  Lemma impl_tlist_eq2
    : impl_tlist q1 t2 = t2'.
  Proof.
    eapply impl_tlist_eq;eauto.
    rewrite <-Hloop. eapply Heq.
  Qed.

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
    : j1 = j2 -> exists π, CPath (H:=C') q2' h' (π >: q2') /\ Disjoint (map fst r1') π.
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
    
  Local Definition s' := s'' C q1.

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
    - setoid_rewrite <-impl_depth_self_eq at 1. 2:eauto.
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
  Local Definition tt1 := rr1 >: (s,k) :+ prefix_nincl (s,k) t1.
  Local Definition tt2 := rr2 >: (s,k) :+ prefix_nincl (s,k) t2.
  
  Lemma impl_shift_lc
    : last_common' tt1 tt2 rr1 rr2 (s, k).
  Proof.
    unfold tt1, tt2. simpl_nl. 
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
        rewrite <-nlconc_to_list. simpl_nl.
        rewrite <-app_assoc. rewrite <-app_comm_cons at 1. setoid_rewrite <-app_comm_cons.
        rewrite <-app_assoc. reflexivity.
      + (* because (s',j1) is in t1' and <> the hd of t1', i.e. q1, its successor is in r1 *)
        admit. 
    - unfold tt1. rewrite <-nlconc_to_list. simpl_nl.
      eapply in_or_app. left. eapply In_rcons. left. auto.
    - rewrite nlcons_to_list. eapply tpath_NoDup. simpl_nl.
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
        rewrite <-nlconc_to_list. simpl_nl.
        rewrite <-app_assoc. rewrite <-app_comm_cons at 1. setoid_rewrite <-app_comm_cons.
        rewrite <-app_assoc. reflexivity.
      + admit. (* as above *)
    - unfold tt2. rewrite <-nlconc_to_list. simpl_nl.
      eapply in_or_app. left. eapply In_rcons. left. auto.
    - rewrite nlcons_to_list. eapply tpath_NoDup. simpl_nl.
      econstructor;eauto 1.
      unfold "`".
      eapply exit_edge_tcfg_edge;eauto.
  Admitted.
  
End lift.
End Lift.

Import Lift.

Theorem lc_disj_exits_lsplits' `(C : redCFG)
        (s e1 e2 q1 q2 qs1 qs2 h : Lab) (j1 j2 k js1 js2 : Tag)
        (t1 t2 : ne_list Coord) (r1 r2 : list Coord)
        (Hlc : last_common' t1 t2 r1 r2 (s,k))
        (Hpath1 : TPath (root,start_tag) (q1,j1) t1)
        (Hpath2 : TPath (root,start_tag) (q2,j2) t2)
        (Hexit1 : exit_edge h q1 e1)
        (Hexit2 : exit_edge h q2 e2)
        (Htag : tl j1 = tl j2)
        (Htagle : hd 0 j1 <= hd 0 j2)
        (Hextra : j1 = j2 -> exists π, CPath q2 h (π >: q2) /\ Disjoint (map fst r1) π)
        (Hsucc1 : (qs1,js1) ≻ (s,k) | (e1,tl j1) :: t1)
        (Hsucc2 : (qs2,js2) ≻ (s,k) | (e2,tl j2) :: t2)
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
    assert (implode_nodes (head_exits_CFG C q1) q1 q1) as Hq1.
    { left. reflexivity. }
    assert (eq_loop q1 q2) as Heq by (eapply q1_eq_q2;eauto).
    enough (implode_nodes (head_exits_CFG C q1) q1 q2) as Hq2.
    enough (implode_nodes (head_exits_CFG C q1) q1 e1) as He1.
    enough (implode_nodes (head_exits_CFG C q1) q1 e2) as He2.
    enough (implode_nodes (head_exits_CFG C q1) q1 h) as Hh.
    2-5: eapply head_exits_implode_nodes_inv1;left; eauto using deq_loop_exited.
    2: eapply eq_loop_exiting;eauto. 3: destruct Heq;eauto.
    2: transitivity q2;destruct Heq;eauto;eapply deq_loop_exited;eauto. 
    (* Construct the imploded type for them *)
    cstr_subtype Hq1. cstr_subtype Hq2. cstr_subtype He1. cstr_subtype He2. cstr_subtype Hh. 
    (* Lift all some properties to the imploded graph *)
    cbn in Heq. 
    eapply eqn_ndeq in Heqn as Hndeq;eauto.
    eapply eqn_sdeq in Heqn as Hsdeq;eauto.
    eapply impl_lift_lc in Hlc as Hlc';eauto.
    eapply impl_lift_exit1 in Hexit1 as Hexit1'.
    eapply impl_lift_exit2 in Hexit2 as Hexit2'.
    eapply impl_lift_tpath1 in Hpath1 as Hpath1'.
    eapply impl_lift_tpath2 in Hpath2 as Hpath2'.
    eapply lc_disj_exits_lsplits_base in Hlc'. 2-8: solve [eauto].
    5: { intros jeq; exploit' Hextra; eapply impl_lift_extra;eauto. }
    2,3: eauto using impl_lift_succ2, impl_lift_succ1.
    2: { setoid_rewrite impl_depth_self_eq at 2;[|eauto]. eapply dep_eq;eauto. }
    setoid_rewrite splits'_spec.
    right.
    pose (s' := s'' C q1). 
    pose (t1' := Lift.t1' (↓ purify Hh) t1 j1).
    pose (t2' := Lift.t2' (↓ purify Hh) t2 j2).
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
      pose (tt1 := rr1 >: (s,k) :+ prefix_nincl (s,k) t1).
      pose (tt2 := rr2 >: (s,k) :+ prefix_nincl (s,k) t2).
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
          (Hpath1 : TPath (root,start_tag) (e1,i) ((e1,i) :<: (q1,j1) :< t1))
          (Hpath2 : TPath (root,start_tag) (e2,i) ((e2,i) :<: (q2,j2) :< t2))
          (Hexit1 : exit_edge h q1 e1)
          (Hexit2 : exit_edge h q2 e2)
  : tl j1 = tl j2.
Proof.
  inversion Hpath1;inversion Hpath2;subst.
  path_simpl' H0. path_simpl' H5.
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
          (Hpath1 : TPath (root,start_tag) (e1,i) ((e1,i) :<: (q1,j1) :< t1))
          (Hpath2 : TPath (root,start_tag) (e2,i) ((e2,i) :<: (q2,j2) :< t2))
          (Hneq : j1 <> j2)
  : exists (qq qq' : Lab), (s,qq,qq') ∈ splits' h e1 \/ (s,qq,qq') ∈ splits' h e2.
Proof.
  assert (tl j1 = tl j2) as Htl_eq by (eapply tl_eq;eauto).
  do 2 rewrite nlcons_to_list in Hlc.
  rewrite last_common'_iff in Hlc. destructH.
  inversion Hpath1. inversion Hpath2. subst.
  path_simpl' H1. path_simpl' H6.
  specialize (Nat.lt_trichotomy (hd 0 j1) (hd 0 j2)) as Nrel.
  destruct Nrel as [Nlt|[Neq|Nlt]];[|exfalso|].
  - do 2 eexists.
    left. eapply lc_disj_exits_lsplits';eauto.
    3,4:simpl_nl;rewrite <-surjective_pairing;eapply get_succ_cons;simpl_nl' Hlc.
    4: eapply last_common'_sym in Hlc.
    3,4: eapply last_common_in1;eapply last_common'_iff;do 2 eexists;eauto.
    + omega.
    + intro N. contradiction.
  - eapply hd_eq_eq in Neq;eauto. 
  - do 2 eexists.
    right. eapply lc_disj_exits_lsplits'.
    1: eapply last_common'_sym in Hlc;eauto.
    all: eauto.
    3,4:simpl_nl;rewrite <-surjective_pairing;eapply get_succ_cons;simpl_nl' Hlc.
    3: eapply last_common'_sym in Hlc.
    3,4: eapply last_common_in1;eapply last_common'_iff;do 2 eexists;eauto.
    + omega.
    + intro N. rewrite N in Hneq. contradiction.
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
