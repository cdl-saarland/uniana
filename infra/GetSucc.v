
Require Import ListOrder.

Fixpoint get_succ (A : eqType) (a e : A) (l : list A)
  := match l with
     | nil => e
     | b :: l => if decision (a = b) then e else get_succ a b l
     end.

Lemma get_succ_cons (A : eqType) (l : list A) (a b : A)
      (Hel : a ∈ l)
  : get_succ a b l ≻ a | b :: l.
Proof.
Admitted.
