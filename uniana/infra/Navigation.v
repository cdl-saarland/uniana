Require Export PreSuffix.

Section nav.
  Variable (A : Type).
  Hypothesis (A_dec : EqDec A eq).

  Fixpoint get_sat (P : decPred A) (l : list A)
    := match l with
       | nil => None
       | a :: l' => if decision (P a) then Some a else get_sat P l'
       end.

  Definition opt_sat (P : A -> Prop) (x : option A)
    := match x with
       | Some a => P a
       | None => False
       end.
    
  Lemma get_sat_sat P l a
        (Hgs : get_sat P l = Some a)
    : P a.
  Proof.
    induction l; cbn in *;[congruence|].
    decide (P a0).
    + inversion Hgs. subst. auto.
    + eauto.
  Qed.

  Lemma get_sat_spec_some P l a
    : get_sat P l = Some a <-> exists l1 l2, l = l1 ++ (a :: l2) /\ P a /\ forall b, b ∈ l1 -> ~ P b.

  Admitted.

  Lemma get_sat_spec_none P l
    : get_sat P l = None <-> forall b, b ∈ l -> ~ P b.
  Admitted.
    
        
End nav.

           
