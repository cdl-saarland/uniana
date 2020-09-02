Require Export Tagged Disjoint.

Section disj.
  Context `{C : redCFG}.

  Infix "-->" := edge__P.
  Infix "-t>" := tcfg_edge (at level 70).
  Class DiamondPaths (s u1 u2 p1 p2 q1 q2 : Lab)
        (k i l1 l2 j1 j2 : Tag)
        (r1 r2 : list (Lab * Tag)) :=
    {
      Dsk1 : (s,k) -t> (u1,l1);
      Dsk2 : (s,k) -t> (u2,l2);
      Dpath1 : TPath (u1,l1) (p1,i) ((p1,i) :: r1);
      Dpath2 : TPath (u2,l2) (p2,i) ((p2,i) :: r2);
      Dqj1 : hd (s,k) r1 = (q1,j1);
      Dqj2 : hd (s,k) r2 = (q2,j2);
      Ddisj : Disjoint r1 r2;
      Dloop : eq_loop q1 q2
    }.

  Class TeqPaths (u1 u2 q1 q2 : Lab)
        (l1 l2 j1 j2 : Tag)
        (r1 r2 : list (Lab * Tag)) :=
    {
      Tpath1 : TPath (u1,l1) (q1,j1) ((q1,j1) :: r1);
      Tpath2 : TPath (u2,l2) (q2,j2) ((q2,j2) :: r2);
      Tdisj : Disjoint ((q1,j1) :: r1) ((q2,j2) :: r2);
      Tloop : eq_loop q1 q2;
      Ttl_eq : tl j1 = tl j2;
      Tlj_eq1 : l1 = j1 \/ l1 = 0 :: j1;
      Tlj_eq2 : l2 = j1 \/ l2 = 0 :: j1 \/ loop_contains u2 q1
    }.

  Context `(D : DiamondPaths).

  Lemma s_deq_q
    : deq_loop s q1.
  Proof.
  Admitted.

  Lemma r1_incl_head_q : forall x, x ∈ map fst r1 -> deq_loop x q1.
  Admitted.

  Lemma r2_incl_head_q : forall x, x ∈ map fst r2 -> deq_loop x q1.
  Admitted.

  Section disj_eqdep.
    Hypothesis (Hdeq : deq_loop q1 s).

    Lemma tl_eq
      : tl j1 = tl j2.
    Admitted.

    Lemma lj_eq1
      : l1 = j1 \/ l1 = 0 :: j1.
    Admitted.

    Lemma lj_eq2
      : l2 = j1 \/ l2 = 0 :: j1 \/ loop_contains u2 q1.
    Admitted.


  End disj_eqdep.

End disj.
