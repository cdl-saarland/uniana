Require Export NinR.

Require Export DisjPaths.

Section disj.

  Load X_notations.
  Load X_vars.

  Lemma lc_eq_disj
        (Hdep : depth s = depth q1)
        (Hjeq : j1 = j2)
    : Disjoint (map fst r1) (map fst r2).
  Admitted.
  
  Lemma lc_neq_disj
        (Hdep : depth s = depth q1)
        (Hjneq : j1 <> j2)
    : exists r', Prefix ((get_innermost_loop' q1) :: r') (map fst r2)
            /\ Disjoint (map fst r1) r'.
  Admitted.

End disj.
