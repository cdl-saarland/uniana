
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

  Definition join_andb (l : list bool) := fold_right andb true l.

  Lemma join_andb_true_iff {A : Type} : 
    forall f (l : list A), (join_andb (map f l) = true) -> (forall x, List.In x l -> f x = true).
  Proof.
    intros.
    unfold join_andb in H.
    induction l; inversion H0; simpl in H; apply andb_true_iff in H; try subst; destruct H; auto.
  Qed.

  Definition join_orb (l : list bool) := fold_right orb false l.

  Lemma join_orb_true_iff {A : Type} :
    forall f (l : list A), (join_orb (map f l) = true) -> (exists x, List.In x l /\ f x = true).
  Proof.
    intros.
    unfold join_orb in H.
    induction l; simpl in H.
    - inversion H.
    - conv_bool.
      inject H.
      * exists a. simpl. eauto.
      * eapply IHl in H0. destruct H0 as [x [Hin Hf]].
        exists x. simpl. eauto.
  Qed.

(** iter *)

  Fixpoint iter {X : Type} (f : X -> X) (l : X) (n : nat) : X
    := match n with
       | O => l
       | S n => iter f (f l) n
       end.

  
  Lemma incl_cons {A : Type} (l l' : list A) (a : A) :
    incl (a :: l) l' -> incl l l'.
  Proof.
    unfold incl. cbn. firstorder.
  Qed.

  Lemma eq_incl {A : Type} (l l':list A) :
    l = l' -> incl l l'.
  Proof.
    intros Heql; rewrite Heql;unfold incl; tauto.
  Qed.


  
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