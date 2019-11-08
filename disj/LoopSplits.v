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
  Admitted.
  
  Lemma lc_disj_exits_lsplits_base_eq π
          (Hdep : depth s = depth q1)
          (Htageq : j1 = j2)
          (Hlatchp : CPath q2 h (π >: q2))
          (Hlatchd : Disjoint (map fst r1) π)
    : (s,qs1,qs2) ∈ loop_splits C h e1.
  Proof.
  Admitted.

  Lemma hd_eq_eq
        (Hheq : hd 0 j1 = hd 0 j2)
    : j1 = j2.
    clear - Hexit1 Hexit2 Hpath1 Hpath2 Hheq.
  Admitted.
  
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
  Admitted.

  Lemma splits'_edge1 
    : edge s qs1 = true.
  Admitted.
  
  Lemma splits'_edge2
    : edge s qs2 = true.
  Admitted.

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


Lemma impl_lift_exit_edge `(C : redCFG) (q' : Lab) (h q e : local_impl_CFG_type C q')
      (Hexit : exit_edge (`h) (`q) (`e))
      (Heq : eq_loop (`q) q')
  : exit_edge (redCFG:= local_impl_CFG C q') h q e.
Admitted.

Section lift.
  Context `(C : redCFG).
  Variables (s q1 : Lab) (h' q1' q2' e1' e2' : local_impl_CFG_type C q1)
            (t1 t2 : ne_list (Lab * Tag)) (r1 r2 : list (Lab * Tag)) (k i j1 j2 : Tag).
  Hypotheses (Hlc : last_common' t1 t2 r1 r2 (s, k))
             (Hpath1 : TPath (root, start_tag) (`q1', j1) t1)
             (Hpath2 : TPath (root, start_tag) (`q2', j2) t2)
             (Hexit1 : exit_edge (`h') (`q1') (`e1'))
             (Hexit2 : exit_edge (`h') (`q2') (`e2'))
             (Hextra : j1 = j2 -> exists π, CPath (` q2') (` h') (π >: `q2') /\ Disjoint (map fst r1) π)
             (Heq : eq_loop q1 (`q1')).

Lemma impl_lift
      (r1' := impl_tlist q1 r1)
      (r2' := impl_tlist q1 r2)
      (C' := local_impl_CFG C q1)
  : exists s' (t1' t2' : ne_list (local_impl_CFG_type C q1 * Tag)),
    impl_tlist q1 t1 = t1'
    /\ impl_tlist q1 t2 = t2'
    /\ last_common' t1' t2' r1' r2' (s',j1)
    /\ TPath (C:=C') (↓ purify_implode q1, start_tag) (q1', j1) t1'
    /\ TPath (C:=C') (↓ purify_implode q1, start_tag) (q2', j2) t2'
    /\ exit_edge (redCFG:=C') h' q1' e1'
    /\ exit_edge (redCFG:=C') h' q2' e2'
    /\ (j1 = j2 -> exists π, CPath q2' h' (π >: q2') /\ Disjoint (map fst r1') π)
    /\ depth (`s') = S (depth q1').
Admitted.

End lift.
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

Lemma last_common_app_eq1 (A : Type) `{EqDec A eq} (l1 l2 l1' l2' : list A) x
      (Hlc : last_common' l1 l2 l1' l2' x)
  : l1 = l1' ++ [x] ++ prefix_nincl x l1.
Admitted.

Lemma last_common_app_eq2 (A : Type) `{EqDec A eq} (l1 l2 l1' l2' : list A) x
      (Hlc : last_common' l1 l2 l1' l2' x)
  : l2 = l2' ++ [x] ++ prefix_nincl x l2.
Proof.
  eapply last_common'_sym in Hlc. eapply last_common_app_eq1;eauto.
Qed.

Lemma last_common_in1 (A : Type) `{EqDec A eq} (l1 l2 : list A) x
      (Hlc : last_common l1 l2 x)
  : x ∈ l1.
Admitted.

Lemma last_common_prefix (A : Type) `{EqDec A eq} (ll1 ll2 l1 l2 : list A)
      (l1' l2' : list A) (x : A)
      (Hlc : last_common' (l1 ++ [x] ++ ll1) (l2 ++ [x] ++ ll2) l1 l2 x)
      (Hpre1 : Prefix l1' l1)
      (Hpre2 : Prefix l2' l2)
  : last_common' (l1' ++ [x] ++ ll1) (l2' ++ [x] ++ ll2) l1' l2' x.
Proof.
Admitted. 

Lemma prefix_nincl_prefix' (A : Type) `{EqDec A eq} (l : list A) a
  : Prefix (prefix_nincl a l) l.
Proof.
  induction l;cbn;eauto.
  - econstructor.
  - destruct (a == a0).
    + econstructor. econstructor.
    + econstructor. eauto.
Qed.

Lemma ex_s_exit `(C : redCFG) (j i : Tag) (h q : Lab) (e' s' q' : local_impl_CFG_type C q)
      (t : ne_list (Lab * Tag)) (t' : ne_list (local_impl_CFG_type C q * Tag))
      (Hqeq : eq_loop q (` q'))
      (Hpath : TPath (root, start_tag) (` q', j) t)
      (Hexit : exit_edge h (` q') (` e'))
      (Hel : (s', i) ∈ t')
      (Ht' : impl_tlist q t = t')
      (Hdep' : depth (` s') = S (depth (C:=local_impl_CFG C q) q'))
      (qs' := fst (get_succ (s', i) (e', tl j) t'))
  : exited (` s') (` qs').
Proof.
Admitted.

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

Lemma get_succ_cons (A : eqType) (l : list A) (a b : A)
      (Hel : a ∈ l)
  : get_succ a b l ≻ a | b :: l.
Proof.
Admitted.

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
    eapply impl_lift in Hlc as Hlc';eauto.
    destruct Hlc' as
        [s' [t1' [t2' [Ht1' [Ht2' [Hlc' [Hpath1' [Hpath2' [Hexit1' [Hexit2' [Hextra' Hdep']]]]]]]]]]].
    assert ((s',j1) ∈ t1') as Hel1'.
    { eapply last_common_in1. eapply last_common'_iff. do 2 eexists;eauto. }
    assert ((s',j1) ∈ t2') as Hel2'.
    { eapply last_common_in1. eapply last_common_sym. eapply last_common'_iff. do 2 eexists;eauto. }
    eapply lc_disj_exits_lsplits_base in Hlc'. 2-8,12:solve [eauto].
    2,3: rewrite <-surjective_pairing;eapply get_succ_cons;eauto.
    2: admit. (* FIXME *)
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
