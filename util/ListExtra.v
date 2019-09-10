Require Export List.
Require Import Util.
Require Export Take.

Definition rcons {A : Type} l a : list A := l ++ (a :: nil).

Notation "l ':r:' a" := (rcons l a) (at level 50).

Lemma rev_cons {A : Type} (a : A) l : rev (a :: l) = (rev l) :r: a.
  induction l; cbn; eauto.
Qed.

Lemma cons_rcons_assoc {A : Type} (a b : A) l : (a :: l) :r: b = a :: (l :r: b).
  induction l; cbn; eauto.
Qed.

Lemma rev_rcons {A : Type} (a : A) l : rev (l :r: a) = a :: (rev l).
  induction l; cbn; eauto. unfold rcons in IHl. rewrite IHl; eauto using  cons_rcons_assoc.
Qed.

Lemma tl_rcons {A : Type} (a : A) l : length l > 0 -> tl (l :r: a) = tl l :r: a.
  induction l; intros; cbn in *; eauto. omega.
Qed.

Lemma hd_rcons {A : Type} (a x y : A) l : length l > 0 -> hd x (l :r: a) = hd y l.
  induction l; intros; cbn in *; eauto. omega.
Qed.

Lemma cons_rcons' {A : Type} (a : A) l :
  (a :: l) = (rev (tl (rev (a :: l))) :r: hd a (rev (a :: l))).
Proof.
  revert a; induction l; intros b; [ cbn in *; eauto|].
  rewrite rev_cons. rewrite tl_rcons.
  - rewrite rev_rcons. erewrite hd_rcons.
    + rewrite cons_rcons_assoc. f_equal. apply IHl.
    + rewrite rev_length; cbn; omega.
  - rewrite rev_length; cbn; omega.
Qed.

Lemma cons_rcons {A : Type} (a : A) l : exists a' l', (a :: l) = (l' :r: a').
Proof.
  exists (hd a (rev (a :: l))). exists (rev (tl (rev (a :: l)))).
  apply cons_rcons'.
Qed.

(*  Lemma rcons_cons {A : Type} (a : A) l : exists a' l', (l :r: a) = (a' :: l').
    remember (@cons_rcons A) as H.*)

Ltac rem_cons_rcons a l H :=
  let a' := fresh a in
  let l' := fresh l in
  specialize (cons_rcons a l) as [a' [l' H]].

Lemma rev_nil (* unused *){A : Type} (l : list A) : rev l = nil <-> l = nil.
Proof.
  split; induction l; cbn in *; eauto; intros.
  - exfalso. induction (rev l); cbn in *; congruence.
  - congruence.
Qed.

(*  Lemma rev_inj {A : Type} (l l': list A) : rev l = rev l' -> l = l'.*)

Lemma rcons_destruct {A : Type} (l : list A) : l = nil \/ exists a l', l = l' :r: a.
Proof.
  destruct l.
  - left. reflexivity.
  - right. apply cons_rcons.
Qed.

Lemma rcons_not_nil (* unused *){A : Type} (l : list A) a : l :r: a <> nil.
Proof.
  intro N. induction l; cbn in *; congruence.
Qed.

Lemma length_rcons {A : Type} l (a : A) : length (l :r: a) = S (length l).
Proof.
  induction l; cbn; eauto.
Qed.

Lemma rcons_length {A : Type} n (l l' : list A) a :
  S n = length l -> l = l' :r: a -> n = length l'.
Proof.
  revert l l'.
  induction n; intros; cbn in *; eauto; subst l; rewrite length_rcons in H; omega. 
Qed.

Lemma rcons_ind
  : forall (A : Type) (P : list A -> Prop),
    P nil -> (forall (a : A) (l : list A), P l -> P (l :r: a)) -> forall l : list A, P l.
Proof.
  intros.
  remember (length l) as n.
  revert l n Heqn.
  refine ((fix F (l : list A) (n : nat) {struct n} : n = length l -> P l :=
             match rcons_destruct l,n with
             | or_introl lnil,  O => (fun (Hnl : O = length l) => _)
             | or_intror (ex_intro _ a (ex_intro _ _ _)), S n => fun (Hnl : (S n) = length l) => _
             | _,_ => _
             end)).
  - subst l. eauto.
  - clear F. intros. subst l. eauto. 
  - clear F. intros. destruct l; eauto using rcons_not_nil. cbn in H1. congruence.
  - rewrite e1. apply H0. apply (F l0 n).
    eapply rcons_length; eauto.
Qed.

Lemma map_rcons {A B : Type} (f : A -> B) :
  forall a l, map f (l :r: a) = map f l :r: f a.
Proof.
  intros. induction l;cbn;eauto. unfold rcons in IHl. rewrite IHl. reflexivity.
Qed.

Lemma incl_cons_hd (* unused *)(A : Type) (a : A) l l'
      (Hincl : (a :: l) ⊆ l')
  : a ∈ l'.
Proof.
  induction l;cbn in *;unfold incl in Hincl;eauto;firstorder.
Qed.

Definition take_r (A : Type) (n : nat) (l : list A) := rev (take n (rev l)).

Lemma take_tl (A : Type) (n : nat) (l : list A)
      (Hn : S n = |l|)
  : take n l = rev (tl (rev l)).
Proof.
  revert dependent n.
  induction l;intros;cbn in *.
  - congruence.
  - destruct n;cbn.
    + inversion Hn;subst. symmetry in H0. rewrite length_zero_iff_nil in H0. subst l. cbn. reflexivity.
    + inversion Hn;subst. exploit IHl. rewrite IHl.
      fold (rev l :r: a). rewrite tl_rcons.
      * rewrite rev_rcons. reflexivity.
      * rewrite rev_length. omega.
Qed.

Lemma take_r_tl (A : Type) (n : nat) (l : list A)
      (Hn : S n = |l|)
  : take_r n l = tl l.
Proof.
  unfold take_r. rewrite take_tl; [|rewrite rev_length;eauto].
  do 2 rewrite rev_involutive. reflexivity.
Qed.