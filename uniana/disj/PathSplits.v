Require Export LiftShift LoopSplits CncLoop.

Lemma both_exit_or_teq `(C : redCFG) q1 q2 p j1 j2 i
      (Hedge1 : (q1,j1) -t> (p,i))
      (Hedge2 : (q2,j2) -t> (p,i))
  : exists h, exit_edge h q1 p /\ exit_edge h q2 p \/ j1 = j2 /\ deq_loop p q1.
Proof.
Admitted.

Lemma edge_edge_loop `(C : redCFG) q1 q2 p
      (Hedge1 : edge__P q1 p)
      (Hedge2 : edge__P q2 p)
  : eq_loop q1 q2.
Proof.
Admitted.

(** * Inhomogeneous joins, base case **)

Section disj.

  Context `(C : redCFG).
  Variables (q1 q2 s p qs1 qs2 : Lab)
            (i j k js1 js2 : Tag)
            (t1 t2 r1 r2 : list (@Coord Lab)).
  
  Variable (D : disjPaths C q1 q2 s t1 t2 r1 r2 j j k i i p p qs1 qs2 js1 js2).

  Lemma lc_join_split_base'
        (Heq : eq_loop q1 s)
    : (s,qs1,qs2) ∈ path_splits p.
  Admitted.
  
  Lemma lc_join_split_base
        (Heq : eq_loop q1 s)
    : (s,qs1,qs2) ∈ splits p.
  Proof.
    eapply splits_spec.
    left. eapply lc_join_split_base';auto.
  Qed.

End disj.
Section disj.

  Context `(C : redCFG).
  Variables (q1 q2 s p qs1 qs2 : Lab)
            (i j k js1 js2 : Tag)
            (t1 t2 r1 r2 : list (@Coord Lab)).
  
  Hypotheses (D : disjPaths C q1 q2 s t1 t2 r1 r2 j j k i i p p qs1 qs2 js1 js2)
             (Hpqdeq : deq_loop p q1).

  Lemma ps_non_contains
    : ~ loop_contains p s.
  Proof.
  Admitted.

  Lemma sep_pq_eq_p
    : forall h, loop_contains h p -> ~ loop_contains h q1 -> h = p.
  Admitted.

  Lemma ocnc_loop_pq s'
        (Hocnc : ocnc_loop s p s')
    : ocnc_loop s q1 s'.
  Proof.
  Admitted.

  Lemma deq_ps_deq_qs
        (Hdeq : deq_loop p s)
    : deq_loop q1 s.
  Proof.
    (* case destinction on the edge q->p:
     * if exit contradition bc. tags
     * if normal or back_edge then eq_loop
     * if entry then show that there must be an outer backedge to re-enter p 
     * which is a contradiction to the non-existence of outer backedges on disjoint paths
     *)
  Admitted.

  (** * Inhomogeneous joins, step case **)

  Theorem lc_join_split'
    : (s,qs1,qs2) ∈ splits p.
  Proof.
    assert (deq_loop s q1) as Hsdeq.
    { eapply s_deq_q;destruct D;eauto. }
    decide (deq_loop p s).
    - eapply deq_ps_deq_qs in d. eapply lc_join_split_base. eauto. split;eauto.
    - rename n into Hndeq.
      specialize (ex_impl_dP D Hndeq Hpqdeq) as I. destructH.
      specialize (lift_disjPaths (I:=I)) as Q.
      assert (e1' = e2') as Eeq.
      { eapply subtype_extensionality.
        rewrite <-He1. rewrite <-He2. reflexivity. }
      subst e2'.
      assert (eq_loop (C:=local_impl_CFG C p) q1' s') as Hqseq.
      { specialize (ocnc_loop_pq Hocnc) as Hq.
        split.
        - eapply ocnc_loop_exit in Hq. admit. (* bc. dep q1' = dep q1 & dep e = dep s' *)
        - unfold ocnc_loop,cnc_loop in Hq. admit.
      }
      eapply lc_join_split_base in Q as Hsplit. 2:auto.
      setoid_rewrite splits_spec.
      right. right.
      exists (`s'),(`qs1'),(`qs2').
      split.
      + specialize (@splits_path_splits__imp _ _ _ _ C p e1' s' qs1' qs2') as QQ.
        exploit QQ.
        * rewrite He1. reflexivity.
        * eapply lc_join_split_base';eauto.
        * destruct I. setoid_rewrite <-He1 in QQ. apply QQ. 
      + specialize (Nat.lt_trichotomy n1 n2) as [Nlt|[Neq|Nlt]];[left| |right].
        * eapply lc_disj_exits_lsplits'.
          -- eapply disjPathsE_shift_lt.
          -- cbn. reflexivity.
          -- cbn. clear - Nlt; omega.
          -- intro N. exfalso. inversion N. rewrite H0 in Nlt. clear - Nlt. omega.
        * specialize (disjPathsE_shift_eq Neq) as Dshift.
          eapply disj_latch_path_or in Dshift as Hπ. 2: clear - Neq;f_equal;eauto.
          destruct Hπ as [π [Hπ | Hπ]];[left|right].
          -- eapply lc_disj_exits_lsplits'. 1:eapply Dshift. 1,2:cbn;eauto.
             1:rewrite Neq;reflexivity.
             intro N. eexists;eauto.
          -- eapply splits'_sym.
             eapply lc_disj_exits_lsplits'. 1:eapply disjPathsE_sym;eapply Dshift. 1,2:cbn;eauto.
             1: rewrite Neq;reflexivity.
             intro N. eexists;eauto. 
        * eapply splits'_sym.
          eapply lc_disj_exits_lsplits'.
          -- eapply disjPathsE_sym. 
             eapply disjPathsE_shift_lt2.
          -- cbn. reflexivity.
          -- cbn. clear - Nlt; omega.
          -- intro N. exfalso. inversion N. rewrite H0 in Nlt. clear - Nlt. omega.
  Admitted.
    
End disj.

(** * Corollaries **)

Theorem lc_join_split `{C : redCFG} t1 t2 (p q1 q2 s : Lab) (i j1 j2 k : Tag)
        (* it is important to cons qj's in front of the t's *)
        (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
        (Hneq : q1 <> q2)
        (Hpath1 : TPath (root,start_tag) (p,i) ((p,i) :: (q1,j1) :: t1))
        (Hpath2 : TPath (root,start_tag) (p,i) ((p,i) :: (q2,j2) :: t2))
  : exists qq qq', (s,qq,qq') ∈ splits p.
Proof.
  inversion Hpath1. inversion Hpath2. subst.
  rename H0 into Hpath1'. rename H5 into Hpath2'.
  rename H3 into Hedge1. rename H8 into Hedge2.
  replace b with (q1,j1) in *. clear b.
  2: { eapply path_front in Hpath1'. auto. }
  replace b0 with (q2,j2) in *. clear b0.
  2: { eapply path_front in Hpath2'. auto. }
  specialize (both_exit_or_teq (C:=C)) as Hbet. specialize (Hbet q1 q2 p j1 j2 i).
  exploit Hbet.
  destructH.
  destruct Hbet.
  - destructH. eapply lc_disj_exit_lsplits in Hlc;eauto.
    destructH. do 2 eexists. eapply splits_spec. right. left. eexists. eauto.
  - destruct H. subst j2.
    rewrite last_common'_iff in Hlc. destructH.
    eexists;eexists.
    eapply lc_join_split'. 2:eauto.
    econstructor;eauto.
    2: eapply last_common'_sym in Hlc.
    1,2: rewrite <-surjective_pairing;eapply get_succ_cons.
    1,2: eapply last_common_in1;eapply last_common'_iff;do 2 eexists;eauto.
    eapply edge_edge_loop; unfold tcfg_edge in *; do 2 destructH; eauto.
Qed.
