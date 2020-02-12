Require Export ListOrder.

Goal forall (A : Type) (a b c d : A) (l : list A), NoDup l -> splinter (a :: b :: d :: nil) l
                                              -> splinter (d :: c :: a :: nil) l -> False.
  intros.  splice_splinter.
Abort.

Goal forall (A : Type) (a b c : A) (l : list A), NoDup (c :: l) -> a ≻* b | c :: l -> b ≻* c | c :: l -> False.
  intros. splice_splinter.
Abort.

  