Require Export LoopSplits.

Theorem lc_join_split `{redCFG} t1 t2 (p q1 q2 s : Lab) (i j1 j2 k : Tag)
        (* it is important to cons qj's in front of the t's *)
        (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
        (Hneq : q1 <> q2)
        (Hpath1 : TPath (root,start_tag) (p,i) ((p,i) :: (q1,j1) :: t1))
        (Hpath2 : TPath (root,start_tag) (p,i) ((p,i) :: (q2,j2) :: t2))
  : exists qq qq', (s,qq,qq') ∈ splits p.
Proof.
Admitted.
