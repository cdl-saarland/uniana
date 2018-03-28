
Require Import List.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.EquivDec.

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
