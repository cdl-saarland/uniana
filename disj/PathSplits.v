Require Export LiftShift LoopSplits.

Section disj.

  Context `(C : redCFG).
(*  Variable (t1 t2 : list (Lab * Tag)) (r1 r2 : list (Lab * Tag)) (q1 q2 s : Lab) (j1 j2 k : Tag).
  Hypotheses (Hlc : last_common' t1 t2 r1 r2 (s,k))
             (Hpath1 : TPath (root,start_tag) (q1,j1) t1)
             (Hpath2 : TPath (root,start_tag) (q2,j2) t2).*)
(*             (Hloop : eq_loop q1 q2)
             (Htag : tl j1 = tl j2)
             (Htagleq : hd 0 j1 <= hd 0 j2). *)
  (*

  Hypotheses (Htag : tl j1 = tl j2)
             (Htagleq : hd 0 j1 <= hd 0 j2)
             (Hextra : j1 = j2 -> exists π, CPath q2 h (π :r: q2) /\ Disjoint (map fst r1) π).*) 

  Lemma both_exit_or_teq q1 q2 p j1 j2 i
        (Hedge1 : (q1,j1) -t> (p,i))
        (Hedge2 : (q2,j2) -t> (p,i))
    : exists h, exit_edge h q1 p /\ exit_edge h q2 p \/ j1 = j2.
  Proof.
  Admitted.
    
End disj.

Theorem lc_join_split `{C : redCFG} t1 t2 (p q1 q2 s : Lab) (i j1 j2 k : Tag)
        (* it is important to cons qj's in front of the t's *)
        (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
        (Hneq : q1 <> q2)
        (Hpath1 : TPath (root,start_tag) (p,i) ((p,i) :: (q1,j1) :: t1))
        (Hpath2 : TPath (root,start_tag) (p,i) ((p,i) :: (q2,j2) :: t2))
  : exists qq qq', (s,qq,qq') ∈ splits p.
Proof.
  specialize (both_exit_or_teq (C:=C)) as Hbet. specialize (Hbet q1 q2 p j1 j2 i).
  exploit Hbet.
  1: inversion Hpath1;subst;path_simpl' H0;eauto.
  1: inversion Hpath2;subst;path_simpl' H0;eauto.
  destructH.
  destruct Hbet.
  - destructH. eapply lc_disj_exit_lsplits in Hlc;eauto.
    destructH. do 2 eexists. eapply splits_spec. right. left. eexists. eauto.
  - decide (deq_loop p s).
    + admit.
    + admit.
  
Admitted.
