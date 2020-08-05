
Require Import ListOrder.
Require Import Coq.Program.Equality.

Fixpoint get_pred (A : Type) `{EqDec A eq} (a e : A) (l : list A) : A :=
  match l with
  | [] => e
  | b :: l0 => if a == b then hd e l0 else get_pred a e l0
  end.

Fixpoint get_succ (A : Type) `{EqDec A eq} (a e : A) (l : list A)
  := match l with
     | nil => e
     | b :: l => if a == b then e else get_succ a b l
     end.

Lemma get_succ_cons (A : Type) `{EqDec A eq} (l : list A) (a b : A)
      (Hel : a ∈ l)
  : get_succ a b l ≻ a | b :: l.
Proof.
  dependent induction l.
  - inversion Hel.
  - simpl.
    destruct (equiv_dec a0 a).
    + rewrite e. econstructor. exists []. reflexivity.
    + destruct Hel; [subst; congruence |].
      eauto using succ_cons. 
Qed.

Lemma get_pred_cons (A : Type) `{EqDec A eq} (l : list A) (a b : A)
      (Hel : a ∈ l)
  : a ≻ get_pred a b l | l :r: b.
Proof.
  dependent induction l.
  - inversion Hel.
  - simpl.
    destruct (equiv_dec a0 a).
    + rewrite e. unfold succ_in.
      destruct l.
      * simpl. exists []. exists []. simpl. reflexivity.
      * simpl. exists (l :r: b). exists []. reflexivity.
    + destruct Hel; [subst; congruence |].
      eauto using succ_cons.
Qed.
