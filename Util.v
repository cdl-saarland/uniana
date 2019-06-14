Global Set Nested Proofs Allowed.

Require Import List.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Utils.
Require Import Coq.Classes.EquivDec.


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

Lemma in_fst (* unused *){A B : Type} a (l : list (A * B)) :
  In a (map fst l)
  -> exists b, In (a,b) l.
Proof.
  intros.
  induction l;cbn in *;[contradiction|].
  destruct H.
  - exists (snd a0). left. rewrite <-H. eapply surjective_pairing.
  - eapply IHl in H. destruct H. exists x; right;eauto.
Qed.

Infix "∈" := In (at level 50).
Notation "a '∉' l" := (~ a ∈ l) (at level 50).

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

Lemma beq_false (* unused *){A : Type} `{EqDec A} (a b : A) :
  (a ==b b) = false <-> (a =/= b).
Proof.
  unfold equiv_decb; destruct (a == b); firstorder.
Qed.

Lemma bne_true {A : Type} `{EqDec A} (a c : A) :
  (a <>b c) = true <-> (a =/= c).
Proof.
  unfold nequiv_decb, equiv_decb. rewrite negb_true_iff. destruct (a == c); firstorder.
Qed.

Lemma bne_false (* unused *){A : Type} `{EqDec A} (a b : A) :
  (a <>b b) = false <-> (a === b).
Proof.
  unfold nequiv_decb, equiv_decb. rewrite negb_false_iff. destruct (a == b); firstorder.
Qed.

Definition to_bool {P Q : Prop} (x : {P} + {Q}) := if x then true else false.

Lemma to_bool_true (P : Prop) (x : {P} + {~ P}) : to_bool x = true <-> P.
Proof.
  destruct x; cbn; firstorder.
Qed.
    
Lemma to_bool_false (P : Prop) (x : {P} + {~P}) : to_bool x = false <-> ~ P.
Proof. 
  destruct x; cbn; firstorder.
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
                         | [ H: context[to_bool _ = true] |- _ ] => rewrite to_bool_true in H
                         | [ H: context[to_bool _ = false] |- _ ] => rewrite to_bool_false in H
                         | [ H: context[negb (_ && _)] |- _ ] => rewrite negb_andb in H
                         | [ H: context[negb (_ || _ )] |- _ ] => rewrite negb_orb in H
                         | [ |- context[_ ==b _ = true]] => rewrite beq_true
                         | [ |- context[_ ==b _ = false]] => rewrite beq_false
                         | [ |- context[_ <>b _ = true]] => rewrite bne_true
                         | [ |- context[_ <>b _ = false]] => rewrite bne_false
                         | [ |- context[_ || _ = true]] => rewrite orb_true_iff
                         | [ |- context[_ || _ = false]] => rewrite orb_false_iff
                         | [ |- context[_ && _ = true]] => rewrite andb_true_iff
                         | [ |- context[_ && _ = false]] => rewrite andb_false_iff
                         | [ |- context[to_bool _ = true]] => rewrite to_bool_true
                         | [ |- context[to_bool _ = false]] => rewrite to_bool_false
                         | [ |- context[negb (_ && _)]] => rewrite negb_andb
                         | [ |- context[negb (_ || _ )]] => rewrite negb_orb
                         end.

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

  Lemma eq_incl (* unused *){A : Type} (l l':list A) :
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

  
  Ltac solve_pair_eq :=
    repeat lazymatch goal with
           | [ H : ?a = (?b,?c) |- _ ] => destruct a; inversion H; clear H
           | _  => subst; eauto
           end.

  
  Ltac exploit' H :=
    let p := fresh "Q" in
    lazymatch type of H with
    | ?P -> ?Q => assert P as p; [eauto|specialize (H p); clear p]
    | forall (x : ?P), ?Q => lazymatch goal with
                       | [ p : P |- _ ] => specialize (H p)
                       end
    end.

  Ltac exploit H :=
    let p := fresh "Q" in
    lazymatch type of H with
    | ?P -> ?Q => assert P as p; [eauto|specialize (H p); clear p;try exploit H]
    | forall (x : ?P), ?Q => lazymatch goal with
                       | [ p : P |- _ ] => specialize (H p);try exploit H
                       end
    end.

  Goal forall (V X Y Z : Type) (x:X) (y:Y) (P : V -> Prop), (X -> Y -> V) -> (forall v:V, P v -> X -> Y -> Z) -> (forall v, P v) -> Z.
    intros V X Y Z x y P Hxy Hv HP. 
    exploit Hxy. exploit Hv. exact Hv.
  Qed.

  Goal forall (X : Type) (P : X -> Prop) (x:X), (forall x, P x) -> True.
    intros. exploit H. exact I.
  Qed.
  
  Definition option_fst (* unused *){A B : Type} (ab : option (A*B)) : option A :=
    match ab with
    | Some ab => Some (fst ab)
    | _ => None
    end.
  
  Definition option_prod (* unused *){A B : Type} (a : option A) (b : option B) : option (A*B) :=
    match a,b with
    | Some a, Some b => Some (a,b)
    | _,_ => None
    end.

  Infix "⊆" := incl (at level 50).
  
  Definition set_eq (* unused *){A : Type} (a b : list A) := a ⊆ b /\ b ⊆ a.
  
  Infix "='" := (set_eq) (at level 50).

  Ltac destructH' H :=
    lazymatch type of H with
    | ?P /\ ?Q => let H1 := fresh H in
                let H2 := fresh H in
                destruct H as [H1 H2]; destructH' H1; destructH' H2
    | exists x, ?P => let x0 := fresh x in
                destruct H as [x0 H]; destructH' H
    | _ => idtac
    end.

  Ltac destructH :=
    match goal with
    | [H : ?P /\ ?Q |- _ ] => let H1 := fresh H in
                           let H2 := fresh H in
                           destruct H as [H1 H2]; destructH' H1; destructH' H2
    | [H : exists x, ?P |- _ ] => let x0 := fresh x in
                           destruct H as [x0 H]; destructH' H
    end.

  
  Definition concat (* unused *){A B C : Type} (f : B -> C) (g : A -> B) := fun a => f (g a).
  
  Infix "∘" := Basics.compose (at level 70).

  
  Ltac copy H Q :=
    eapply id in H as Q.

  
  Ltac eapply2 H H1 H2 :=
    eapply H in H2; only 1: eapply H in H1.
  
  Ltac eapply2' H H1 H2 Q1 Q2 :=
    eapply H in H2 as Q2; only 1: eapply H in H1 as Q1.


  Ltac subst' :=
    repeat
      match goal with
      | [H:(_,_) = (_,_) |- _] => inversion H; subst; clear H
      | [H: _ = _ /\ _ = _ |- _]=> destruct H; subst
      end.
  
  (* TODO: tidy up this file *)