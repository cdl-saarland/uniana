Require Export EqNeqDisj SplitsDef.

Section disj.
  Context `(C : redCFG).
  
  Load X_vars.
  Notation "pi -t> qj" := (tcfg_edge pi qj = true) (at level 50).

  Variables  (e1 e2 h qs1 qs2 : Lab) (js1 js2 : Tag).
  Hypotheses (Hexit1 : exit_edge h q1 e1)
             (Hexit2 : exit_edge h q2 e2)
             (Hsucc1 : (qs1, js1) ≻ (s, k) | (e1, tl j1) :: t1)
             (Hsucc2 : (qs2, js2) ≻ (s, k) | (e2, tl j2) :: t2).

  Fixpoint get_succ (A : eqType) (a e : A) (l : list A)
    := match l with
       | nil => e
       | b :: l => if decision (a = b) then e else get_succ a b l
       end.

(*  Local Definition qq := fst (get_succ (s,k) (e1,tl j1) t1).
  Local Definition qq' := fst (get_succ (s,k) (e2, tl j2) t2). *)

  Lemma lc_disj_exits_lsplits_base_lt
        (Hdep : depth s = depth q1)
        (Htaglt : hd 0 j1 < hd 0 j2)
    : ( s, qs1, qs2) ∈ loop_splits C h e1.
  Proof.
  Admitted.
  
  Lemma lc_disj_exits_lsplits_base_eq π
          (Hdep : depth s = depth q1)
          (Htageq : j1 = j2)
          (Hlatchp : CPath q2 h (π >: q2))
          (Hlatchd : Disjoint (map fst r1) π)
    : (s,qs1,qs2) ∈ loop_splits C h e1.
  Proof.
  Admitted.

  Lemma hd_tl_len_eq (A : Type) (l l' : list A) (a : A)
        (Hheq : hd a l = hd a l')
        (Hteq : tl l = tl l')
        (Hleq : | l | = | l' |)
    : l = l'.
  Proof.
    clear - Hheq Hteq Hleq.
    revert dependent l'. induction l; intros; destruct l';cbn in *;eauto. 1,2: congruence.
    f_equal;eauto.
  Qed.                          

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

  Lemma dom_self_loop p π
        (Hpath : CPath p p π)
        (Hinl : innermost_loop h p)
        (Hnin : h ∉ π)
    : π = ne_single p.
    clear - Hpath Hinl Hnin.
  Admitted.
  
  Lemma exit_edge_innermost q e
        (Hexit : exit_edge h q e)
    : innermost_loop h q.
    clear - Hexit.
  Admitted.
  
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
      +
        (*assert (h ∉ map fst r1) as Hh1.
        { intro N. eapply no_head;eauto. }
        assert (h ∉ map fst r2) as Hh2.
        { intro N. eapply no_head. 1:eapply last_common'_sym. all:eauto.
          symmetry;eauto. rewrite Heq;eauto. }
        destruct l,l0.
        1-3: exists [h];cbn. 1-2: right. 3: left.
               1-3:split;[econstructor;eauto using back_edge_incl
                         |intros z R1 R2;destruct R2;[subst|];contradiction]. *)
        exfalso.
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



Definition imploding_head `(C : redCFG) h p := exists e, exited p e /\ deq_loop h e.

Section lift_one.

  Context `(C : redCFG).
  Variables (s q : Lab) (h' q' e' : local_impl_CFG_type C q)
            (t : ne_list (Lab * Tag)) (r : list (Lab * Tag)) (j : Tag).
  Local Definition C'' := local_impl_CFG C q.

  Hypotheses (Hpath : TPath (root,start_tag) (`q',j) t)
             (Hexit : exit_edge (`h') (`q') (`e'))
             (Heq : eq_loop q (`q'))
             (Hndeq : ~ deq_loop q s)
             (Hdeq : deq_loop s q).

  Definition s'' : local_impl_CFG_type C q.
    clear - Heq Hdeq Hndeq.
  Admitted.

  Lemma s_in_s
    : loop_contains (`s'') s.
  Admitted.
  
  Lemma q_ndeq_s'
    : ~ deq_loop q (`s'').
  Admitted.

  Lemma s_imploding_head
    : imploding_head C q (`s'').
  Admitted.
  
  Lemma impl_lift_exit_edge
    : exit_edge (redCFG:= local_impl_CFG C q) h' q' e'.
    clear - Hexit.
  Admitted.

  Local Definition t' := match impl_tlist q t with
                         | nil => ne_single (h',j) (* never happening *)
                         | a :: l => a :< l
                         end.

  Lemma impl_tlist_eq
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
  
  Lemma ex_s_exit (x' : local_impl_CFG_type C q) i i'
        (Hsucc : (x',i') ≻ (s'',i) | t')
    : exited (` s'') (` x').
  Proof.
  Admitted.
  
  Lemma impl_lift_tpath
    : TPath (C:=C'') (↓ purify_implode q, start_tag) (q', j) t'.
    clear - Hpath.
  Admitted.

End lift_one.

Lemma exists_or_exists_switch (X : Type) (P P' : X -> X -> Prop)
      (Q Q' : X -> X -> X -> Prop) (R : X -> X -> X -> X -> X -> Prop)
  : (exists v w z, (Q v w z \/ Q' v w z) /\ exists x y, R x y v w z)
    -> exists (x y : X), (P x y \/ exists v w z, Q v w z /\ R x y v w z)
                   \/ (P' x y \/ exists v w z, Q' v w z /\ R x y v w z).
Proof.
  intro N. destructH. destruct N0.
  all: exists x, y;firstorder.
Qed.

Lemma exists_or_exists_destruct (X : Type) (P P' Q Q' : X -> X -> Prop)
  : (exists (x y : X), (P x y \/ Q x y)
                  \/ (P' x y \/ Q' x y))
    -> (exists (x y : X), P x y \/ P' x y)
                   \/ exists (x y : X), Q x y \/ Q' x y.
Proof.
  firstorder.
Qed.

Lemma exit_succ_exiting `(C : redCFG) (p q h e : Lab) (k i j : Tag) r
      (Hpath : TPath (p,k) (q,j) (r >: (p,k)))
      (Hexit : exited h e)
      (Hel : (e,i) ∈ r)
  : exists qe n, exit_edge h qe e /\ (e,i) ≻ (qe,n :: i) | r :r: (p,k).
Admitted.      

Lemma impl_depth_self_eq `(C : redCFG) (q : Lab) (q' : local_impl_CFG_type C q)
      (Heq : eq_loop q (` q'))
  : depth (C:=local_impl_CFG C q) q' = depth q.
Admitted.

Lemma splits'_sym `(C : redCFG) (s h e q q' : Lab)
              (Hsp : (s,q,q') ∈ splits' h e)
  : (s,q',q) ∈ splits' h e.
Admitted.

Lemma get_succ_cons (A : eqType) (l : list A) (a b : A)
      (Hel : a ∈ l)
  : get_succ a b l ≻ a | b :: l.
Proof.
Admitted.

Lemma succ_in_prefix_nd (A : Type) (l l' : list A) (a b c : A)
      (Hpre : Prefix (c :: l) l')
      (Hel : a ∈ l)
      (Hsucc : b ≻ a | l')
      (Hnd : NoDup l')
  : b ≻ a | c :: l.
Admitted.

Lemma exit_edge_tcfg_edge `(C : redCFG) (h p q : Lab) (j : Tag)
      (Hexit : exit_edge h q p)
  : tcfg_edge (q,j) (p,tl j) = true.
Proof.
  cbn. conv_bool.
  unfold eff_tag. 
  decide (q ↪ p).
  - exfalso. eapply no_exit_head;eauto. exists q. auto.
  - unfold exit_edge in Hexit. destructH. split;[auto|].
    decide (exists h0, exit_edge h0 q p).
    + reflexivity.
    + exfalso. eapply n0. exists h. unfold exit_edge. eauto.
Qed.

Lemma impl_depth_max `(C : redCFG) (q : Lab) (p : local_impl_CFG_type C q)
  : depth (C:=local_impl_CFG C q) p <= depth (C:=C) q.
Admitted.

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

Module lift.
Section lift.
  Load X_vars_lift.
  
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
  Admitted.

  (* step case *)

  Hypotheses (Hsdeq : deq_loop s q1)
             (Hndeq : ~ deq_loop q1 s).
  
  Local Definition s' := s'' Heq Hndeq Hsdeq.

  Lemma impl_lift_lc
    : last_common' t1' t2' r1' r2' (s',j1).
  Admitted.
                             
  Local Definition qs1' := fst (get_succ (s', j1) (e1', tl j1) t1').
  Local Definition qs2' := fst (get_succ (s', j1) (e2', tl j2) t2').
  
  Lemma ex_s_exit1
    : exited (` s') (` qs1').
  Proof.
    eapply ex_s_exit;eauto.
  Admitted.

  Lemma ex_s_exit2
    : exited (` s') (` qs2').
  Proof.
    eapply ex_s_exit;eauto.
  Admitted.

End lift.
End lift.

Section disj.

Load X_vars_lift.
Variables (qs1 qs2 : Lab) (js1 js2 : Tag).
Hypotheses (Hsucc1 : (qs1,js1) ≻ (s,k) | (`e1',tl j1) :: t1)
           (Hsucc2 : (qs2,js2) ≻ (s,k) | (`e2',tl j2) :: t2)
           (Htag : tl j1 = tl j2)
           (Htagle : hd 0 j1 <= hd 0 j2).

(*Goal (s,qs1,qs2) ∈ splits' (`h') (`e1').*)
  
Theorem lc_disj_exits_lsplits' `{redCFG}
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
  revert dependent Lab.
  revert j1 j2 k js1 js2.
  induction n;intros.
  - eapply lc_disj_exits_lsplits_base';eauto.
    enough (depth q1 <= depth s) by omega.
    eapply deq_loop_depth.
    eapply s_deq_q;eauto.
  - (* Show that some interesting nodes are in the imploded CFG *)
    assert (implode_nodes (head_exits_CFG H q1) q1 q1) as Hq1.
    { left. reflexivity. }
    assert (eq_loop q1 q2) as Heq by (eapply q1_eq_q2;eauto).
    enough (implode_nodes (head_exits_CFG H q1) q1 q2) as Hq2.
    enough (implode_nodes (head_exits_CFG H q1) q1 e1) as He1.
    enough (implode_nodes (head_exits_CFG H q1) q1 e2) as He2.
    enough (implode_nodes (head_exits_CFG H q1) q1 h) as Hh.
    2-5: eapply head_exits_implode_nodes_inv1;left; eauto using deq_loop_exited.
    2: eapply eq_loop_exiting;eauto. 3: destruct Heq;eauto.
    2: transitivity q2;destruct Heq;eauto;eapply deq_loop_exited;eauto.
    (* Construct the imploded type for them *)
    cstr_subtype Hq1. cstr_subtype Hq2. cstr_subtype He1. cstr_subtype He2. cstr_subtype Hh.
    (* Lift all some properties to the imploded graph *)
    eapply impl_lift_lc in Hlc as Hlc';eauto.
    eapply impl_lift_exit1 in Hexit1 as Hexit1'.
    eapply impl_lift_exit2 in Hexit2 as Hexit2'.
    eapply impl_lift_tpath1 in Hpath1 as Hpath1'.
    eapply impl_lift_tpath2 in Hpath2 as Hpath2'.
    assert ((s',j1) ∈ t1') as Hel1'.
    { eapply last_common_in1. eapply last_common'_iff. do 2 eexists;eauto. }
    assert ((s',j1) ∈ t2') as Hel2'.
    { eapply last_common_in1. eapply last_common_sym. eapply last_common'_iff. do 2 eexists;eauto. }
    eapply lc_disj_exits_lsplits_base in Hlc'. 2-8,12:solve [eauto].
    2,3: rewrite <-surjective_pairing;eapply get_succ_cons;eauto.
    2: {
      eapply Nat.le_antisymm.
      - setoid_rewrite impl_depth_self_eq at 2;[|cbn;reflexivity].
        eapply impl_depth_max.
      - eapply deq_loop_depth. admit. (* FIXME *)
    } 
    setoid_rewrite splits'_spec.
    right.
    pose (qs1' := fst (get_succ (s',j1) (↓ purify He1, tl j1) t1')).
    pose (qs2' := fst (get_succ (s',j1) (↓ purify He2, tl j2) t2')).
    exists (`s'), (`qs1'), (`qs2').
    split.
    + eapply splits'_loop_splits__imp. cbn.
      * eapply eq_loop_exiting;eauto.
      * eauto. 
    (* consequence of Hlc' *)
    + (* we will apply the IH in four similar cases in two different ways, 
         therefore all the assumption of IHn are shown before the cases destinction *)
      assert (exists qe1 n1, exit_edge (` s') qe1 (` qs1') /\ (`qs1',j1) ≻ (qe1,n1 :: j1) | (r1 :r: (s,k)))
        as [qe1 [n1 [Hqee1 Hqes1]]].
      {
        eapply (exit_succ_exiting (C:=H)).
        - eapply r1_tpath;eauto.
        - eapply ex_s_exit in Hdep';eauto.
        - subst qs1'. admit.
          (* r1 is non-nil, because otherwise there would be a double exit *)
      }
      assert (depth (C:=local_impl_CFG H q1) (↓ purify Hq1) = depth q1) as Hdep''.
      { rewrite impl_depth_self_eq;cbn; reflexivity. }
      setoid_rewrite Hdep'' in Hdep'. clear Hdep''.
      assert (exists qe2 n2, exit_edge (` s') qe2 (` qs2') /\ (`qs2',j1) ≻ (qe2,n2 :: j1) | (r2 :r: (s,k)))
        as [qe2 [n2 [Hqee2 Hqes2]]].
      {
        eapply (exit_succ_exiting (C:=H)).
        - eapply r2_tpath;eauto.
        - eapply ex_s_exit. 3: cbn;eauto. all:eauto.
          rewrite impl_depth_self_eq;eauto using q1_eq_q2.
        - subst qs2'. admit.
          (* r2 is non-nil, because otherwise there would be a double exit *)
      }
      eapply last_common_app_eq1 in Hlc as Htt1.
      eapply last_common_app_eq2 in Hlc as Htt2.
      pose (rr1 := prefix_nincl (` qs1',j1) r1).
      pose (rr2 := prefix_nincl (` qs2',j1) r2).
      pose (tt1 := rr1 >: (s,k) :+ prefix_nincl (s,k) t1).
      pose (tt2 := rr2 >: (s,k) :+ prefix_nincl (s,k) t2).
      assert (last_common' tt1 tt2 rr1 rr2 (s, k)) as Hlc_ih.
      {
        subst tt1 tt2. simpl_nl. do 2 rewrite <-nlconc_to_list. simpl_nl. unfold rcons.
        do 2 rewrite <-app_assoc.
        eapply last_common_prefix.
        setoid_rewrite <-Htt1 at 1. setoid_rewrite <-Htt2. eapply Hlc.
        1,2: subst rr1 rr2; eapply prefix_nincl_prefix'.
      }
      specialize (r1_tpath Hlc Hpath1) as Hr1.
      specialize (r2_tpath Hlc Hpath2) as Hr2.
      assert (n = depth s - depth qe1) as Hdep1.
      {
        clear - Hdep' Heqn Hqee1.
        cbn in Heqn.
        assert (depth qe1 = depth (`s')).
        { eapply eq_loop_exiting in Hqee1. rewrite Hqee1. eauto. }
        rewrite H0.
        setoid_rewrite Hdep'.
        omega.
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
(*    assert ((qs1, js1) ≻ (s, k) | t1) as HSucc1 by admit.
      assert ((qs2, js2) ≻ (s, k) | t2) as HSucc2 by admit. (* otw. qs1 would be a double exit *) *)
      assert ((qs1, js1) ≻ (s, k) | (` qs1', j1) :: tt1) as Hsucctt1.
      {
        clear - Htt1 Hsucc1 Hpath1 Hexit1.
        eapply succ_in_prefix_nd;eauto.
        - enough ((` qs1',j1) ∈ r1) as Hel1.
          + eapply prefix_eq.
            eapply prefix_nincl_prefix in Hel1.
            eapply prefix_eq in Hel1. destructH.
            exists ((e1, tl j1) :: l2').
            rewrite Htt1.
            subst tt1 rr1.
            setoid_rewrite Hel1 at 1.
            rewrite <-nlconc_to_list. simpl_nl.
            rewrite <-app_assoc. rewrite <-app_comm_cons at 1. setoid_rewrite <-app_comm_cons.
            unfold rcons. rewrite <-app_assoc. reflexivity.
          + (* because (s',j1) is in t1' and <> the hd of t1', i.e. q1, its successor is in r1 *)
            admit. 
        - subst tt1. rewrite <-nlconc_to_list. simpl_nl.
          eapply in_or_app. left. eapply In_rcons. left. auto.
        - rewrite nlcons_to_list. eapply tpath_NoDup. simpl_nl.
          econstructor;eauto 1.
          unfold "`".
          eapply exit_edge_tcfg_edge;eauto.
      }
      assert ((qs2, js2) ≻ (s, k) | (` qs2', j1) :: tt2) as Hsucctt2.
      {
        clear - Htt2 Hsucc2 Hpath2 Hexit2. cbn in Hsucc2.
        eapply succ_in_prefix_nd;eauto.
        - eapply prefix_eq.
          enough ((` qs2',j1) ∈ r2) as Hel2.
          + eapply prefix_nincl_prefix in Hel2.
            eapply prefix_eq in Hel2. destructH.
            exists ((e2, tl j2) :: l2').
            rewrite Htt2.
            subst tt2 rr2. setoid_rewrite Hel2 at 1.
            rewrite <-nlconc_to_list. simpl_nl.
            rewrite <-app_assoc. rewrite <-app_comm_cons at 1. setoid_rewrite <-app_comm_cons.
            unfold rcons. rewrite <-app_assoc. reflexivity.
          + admit. (* as above *)
        - subst tt2. rewrite <-nlconc_to_list. simpl_nl.
          eapply in_or_app. left. eapply In_rcons. left. auto.
        - rewrite nlcons_to_list. eapply tpath_NoDup. simpl_nl.
          econstructor;eauto 1.
          unfold "`".
          eapply exit_edge_tcfg_edge;eauto.
      }
(*  *)
      (* case distinction on trichotomy: we have to distinguish different cases,
         because the IHn can be applied in two different, symmetrical ways *)
      specialize (Nat.lt_trichotomy n1 n2) as Nrel.
      destruct Nrel as [Nlt|[Neq|Nlt]]; [left| |right].
      * eapply IHn. 
        1-5,9: solve [eauto]. 2-4: solve [cbn;eauto].
        -- intro N. exfalso. inversion N. clear - Nlt H1. omega. 
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
        -- intro N. exfalso. inversion N. clear - Nlt H1. omega.
        -- cbn. clear - Nlt. omega.
           (* show that qq & qq' are exit_edges of s' on H, then construct the coresponding paths to them
            * and show that last_common holds for these paths, bc they are subpaths. 
            * then exploit IHn, use resulting qq_ih & qq'_ih as witnesses, choose the complicated case,
            * there s',qq,qq' are the witnesses and you get one condition by IHn and the other by Hlc'0 *)
Admitted.

Lemma tl_eq `(C : redCFG) (h q1 q2 e1 e2 : Lab) (i j1 j2 : Tag) t1 t2
          (Hpath1 : TPath (root,start_tag) (e1,i) ((e1,i) :<: (q1,j1) :< t1))
          (Hpath2 : TPath (root,start_tag) (e2,i) ((e2,i) :<: (q2,j2) :< t2))
          (Hexit1 : exit_edge h q1 e1)
          (Hexit2 : exit_edge h q2 e2)
  : tl j1 = tl j2.
Proof.
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
