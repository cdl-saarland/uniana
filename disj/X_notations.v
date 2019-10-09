
Context `{C : redCFG}.

Infix "⊴" := Tagle (at level 70).

Notation "p '-a>b' q" := (a_edge p q) (at level 55).
Notation "p '-a>' q" := (p -a>b q = true) (at level 55).
Notation "p '-->b' q" := (edge p q) (at level 55).
Notation "p '-->' q" := (p -->b q = true) (at level 55, right associativity).
