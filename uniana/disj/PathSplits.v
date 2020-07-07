Require Export LoopSplits CncLoop.

Notation "pi -t> qj" := (tcfg_edge pi qj) (at level 50).
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

(** * Corollaries **)

Theorem lc_join_split `{C : redCFG} t1 t2 (p q1 q2 s : Lab) (i j1 j2 k : Tag)
        (* it is important to cons qj's in front of the t's *)
        (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
        (Hneq : q1 <> q2)
        (Hpath1 : TPath (root,start_tag) (p,i) ((p,i) :: (q1,j1) :: t1))
        (Hpath2 : TPath (root,start_tag) (p,i) ((p,i) :: (q2,j2) :: t2))
  : s ∈ splitsT p.
Proof.
Admitted.
