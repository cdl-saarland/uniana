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
