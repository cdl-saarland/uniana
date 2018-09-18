
Require Import List.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Utils.

Lemma list_emp_in : forall {A: Type} l, (forall (a: A), ~ List.In a l) -> l = nil.
Proof.
intros.
induction l.
- reflexivity.
- cut (forall a, ~ List.In a l).
    + intros.
    apply IHl in H0.
    subst. specialize (H a).
    exfalso. simpl in H. auto.
    + intros. specialize (H a0).
    simpl in H. auto.
Qed.


Fixpoint list_is_set {A : Type} (l : list A) : Prop := 
  match l with
  | x :: xs => list_is_set xs /\ ~ In x xs
  | nil => True
  end.

(* Some helpers to deal with booleans *)

Lemma beq_true {A : Type} `{EqDec A} (a c : A) :
  (a ==b c) = true <-> (a === c).
Proof.
  unfold equiv_decb; destruct (a == c); firstorder.
Qed.

Lemma beq_false {A : Type} `{EqDec A} (a b : A) :
  (a ==b b) = false <-> (a =/= b).
Proof.
  unfold equiv_decb; destruct (a == b); firstorder.
Qed.

Lemma bne_true {A : Type} `{EqDec A} (a c : A) :
  (a <>b c) = true <-> (a =/= c).
Proof.
  unfold nequiv_decb, equiv_decb. rewrite negb_true_iff. destruct (a == c); firstorder.
Qed.

Lemma bne_false {A : Type} `{EqDec A} (a b : A) :
  (a <>b b) = false <-> (a === b).
Proof.
  unfold nequiv_decb, equiv_decb. rewrite negb_false_iff. destruct (a == b); firstorder.
Qed.

Ltac conv_bool := repeat match goal with
                         | [ H: context[_ ==b _ = true] |- _ ] => rewrite beq_true in H
                         | [ H: context[_ ==b _ = false] |- _ ] => rewrite beq_false in H
                         | [ H: context[_ <>b _ = true] |- _ ] => rewrite bne_true in H
                         | [ H: context[_ <>b _ = false] |- _ ] => rewrite bne_false in H
                         | [ H: context[_ || _ = true] |- _ ] => rewrite orb_true_iff in H
                         | [ H: context[_ || _ = false] |- _ ] => rewrite orb_false_iff in H
                         | [ H: context[_ && _ = true] |- _ ] => rewrite andb_true_iff in H
                         | [ H: context[_ && _ = false] |- _ ] => rewrite andb_false_iff in H
                         end.

Instance : forall A, EqDec A _ -> EqDec (option A) _ :=
  {
    equiv_dec x y := match x, y with
                     | None, None => in_left
                     | Some a, Some b => if equiv_dec a b then in_left else in_right
                     | _, _ => in_right
                     end
                       
  }.
+ rewrite e0. reflexivity.
+ intro. eapply c. inversion H. reflexivity.
+ intro. inversion H.
+ intro. inversion H.
+ reflexivity.
Qed.

(** iter *)


  Fixpoint iter {X : Type} (f : X -> X) (l : X) (n : nat) : X
    := match n with
       | O => l
       | S n => iter f (f l) n
       end.