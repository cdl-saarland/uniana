Require Export ListExtra.

Definition Disjoint {A : Type} (l l' : list A) : Prop :=
  (forall a, In a l -> ~ In a l')
  /\ (forall a, In a l' -> ~ In a l).

Lemma disjoint_cons1 {A : Type} (a : A) l l' :
  Disjoint (a :: l) l' <-> ~ In a l' /\ Disjoint l l'.
Proof.
  split; revert l.
  - induction l'; intros l; firstorder.
  - intros l [nin disj]. split.
    + intros b in' N.
      destruct in'.
      * destruct H. contradiction.
      * destruct disj as [disj _]. specialize (disj _ H). contradiction.
    + intros b in' N.
      destruct N.
      * destruct H. contradiction.
      * destruct disj as [disj _]. specialize (disj _ H). contradiction.
Qed.

Lemma disjoint_cons2 {A : Type} (a : A) l l' :
  Disjoint l (a :: l') <-> ~ In a l /\ Disjoint l l'.
Proof.
  split; revert l.
  - induction l'; intros l; firstorder.
  - intros l [nin disj]. split.
    + intros b in' N.
      destruct N.
      * destruct H. contradiction.
      * destruct disj as [_ disj]. specialize (disj _ H). contradiction.
    + intros b in' N.
      destruct in'.
      * destruct H. contradiction.
      * destruct disj as [_ disj]. specialize (disj _ H). contradiction.
Qed.

Lemma disjoint_subset (A : Type) (l1 l1' l2 l2' : list A)
  : l1 ⊆ l1' -> l2 ⊆ l2' -> Disjoint l1' l2' -> Disjoint l1 l2.
Proof.
  intros Hsub1 Hsub2 Hdisj.
  unfold Disjoint in *. destructH. split;firstorder.
Qed.

Lemma Disjoint_sym {A : Type} (l l' : list A)
      (Hdisj : Disjoint l l')
  : Disjoint l' l.
Proof.
  unfold Disjoint in *.
  firstorder.
Qed.