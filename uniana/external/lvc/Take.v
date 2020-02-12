Require Import Coq.Lists.List Setoid Coq.Lists.SetoidList Omega.
Require Export Coq.Classes.EquivDec FinTypes.

Set Implicit Arguments.

Fixpoint take n X (L:list X) :=
  match n, L with
    | S n, x::L => x::take n L
    | _, _ => nil
  end.

Lemma take_nil (X:Type) n
  : @take n X nil = nil.
Proof.
  destruct n; eauto.
Qed.

Lemma take_length_le X (L:list X) n
  : n <= length L -> length (take n L) = n.
Proof.
  intros. revert dependent n;induction L;intros; destruct n; simpl in *; try omega; eauto.
  rewrite IHL; eauto; omega.
Qed.


Lemma take_length_ge X (L:list X) n
  : n >= length L -> length (take n L) = length L.
Proof.
  intros. revert dependent n; induction L;intros; destruct n; simpl in *; try omega; eauto.
  rewrite IHL; eauto; omega.
Qed.

Lemma take_length X (L:list X) n
  : length (take n L) = min (length L) n.
Proof.
  decide (n < length L). 
  - rewrite take_length_le; try omega.
    rewrite min_r; omega.
  - eapply not_lt in n0.
    rewrite min_l; try omega.
    eapply take_length_ge; eauto.
Qed.

 Lemma map_take X Y (f:X -> Y) (L:list X) n
  : map f (take n L) = take n (map f L).
Proof.
  revert dependent L; induction n;intros; simpl; eauto.
  destruct L; simpl ; eauto.
  f_equal; eauto.
Qed.

Lemma take_app_le n X (L L':list X)
  : n <= length L
    -> take n (L ++ L') = take n L.
Proof.
  intros. revert dependent L; induction n; intros ; simpl; eauto.
  destruct L; [cbn in H; omega| ] ; simpl.
  rewrite IHn; eauto. simpl in *; omega.
Qed.

Lemma take_app_ge n X (L L':list X)
  : n >= length L
    -> take n (L ++ L') = L ++ take (n - length L) L'.
Proof.
  intros. revert dependent L; induction n;intros; simpl; eauto.
  - destruct L; simpl in *; eauto. exfalso; omega.
  - destruct L; simpl in *; eauto.
    rewrite IHn; eauto. omega.
Qed.

Lemma take_eq_ge n X (L:list X)
  : n >= |L| -> take n L = L.
Proof.
  intros. revert dependent L; induction n;intros; destruct L; simpl in *; eauto.
  - exfalso; omega.
  - rewrite IHn; eauto. omega.
Qed.


Lemma take_app_eq n X (L L':list X)
  : n = length L
    -> take n (L ++ L') = L.
Proof.
  intros. subst. revert dependent L'; induction L;intros; simpl; eauto.
  f_equal; eauto.
Qed.

Lemma take_take_lt X (L:list X) n m
  : n < m
    -> take n L = take n (take m L).
Proof.
  intros. revert dependent L; revert dependent m;  induction n;intros; destruct L, m; simpl; eauto.
  - omega.
  - erewrite IHn; eauto. omega.
Qed.

Lemma take_one X (L:list X) x k
  : k > 0
    -> take k (x::L) = x :: take (k - 1) L.
Proof.
  intros; destruct k; simpl.
  - omega.
  - f_equal. f_equal. omega.
Qed.
