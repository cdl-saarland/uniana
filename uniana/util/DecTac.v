Require Import Coq.Classes.EquivDec.
Require Import Decidable List.

  Ltac decide' X :=
    let e := fresh "e" in
    let c := fresh "c" in
    lazymatch X with
    | ?a == ?b => destruct X as [e|c]; [destruct e|]
    | _ => lazymatch type of X with
          | ?a == ?b => destruct X as [e|c]; [destruct e|]
          | {_ === _} + {_ =/= _} => destruct X as [e|c]; [destruct e|]
          end
    end.

  Lemma In_dec (A : Type) `{EqDec A eq} a (l : list A) : decidable (In a l).
  Proof.
    unfold decidable.
    induction l.
    - right. tauto.
    - destruct IHl.
      + left; econstructor 2; eauto.
      + destruct (a == a0).
        * destruct e. left; econstructor. reflexivity.
        * right. contradict H0. inversion H0; eauto. subst a0. exfalso. apply c. reflexivity.
  Qed.