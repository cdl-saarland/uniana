Require Export NinR.

Require Export DisjPaths.

Section disj.
  Context `{C : redCFG}.
  
  Infix "⊴" := Tagle (at level 70).
  
  Notation "p '-a>b' q" := (a_edge p q) (at level 55).
  Notation "p '-a>' q" := (p -a>b q = true) (at level 55).
  Notation "p '-->b' q" := (edge p q) (at level 55).
  Notation "p '-->' q" := (p -->b q = true) (at level 55, right associativity).

  Load vars.

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

