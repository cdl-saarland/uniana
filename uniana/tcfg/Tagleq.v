Require Import Program.Equality Lia SimplDec.
Require Export ListExtra PreSuffix ListOrder.

Definition Tag := list nat.

Inductive Taglt : Tag -> Tag -> Prop :=
| TagltS (n m : nat) (i : Tag) : n < m -> Taglt (n :: i) (m :: i)
| TagltCons (n m : nat) (i j : Tag) : Taglt i j -> Taglt (n :: i) (m :: j).

Definition Tagle (i j : Tag) : Prop := Taglt i j \/ i = j.

Infix "⊴" := Tagle (at level 70).
Infix "◁" := Taglt (at level 70).

Lemma Tagle_refl (i : Tag)
  : i ⊴ i.
Proof.
  right;auto.
Qed.

Lemma Taglt_irrefl
  : Irreflexive Taglt.
Proof.
  unfold Irreflexive, Reflexive, complement.
  intros x Hx.
  dependent induction Hx.
  - lia.
  - auto.
Qed.

Lemma Taglt_trans
  : Transitive Taglt.
Proof.
  intros x y z Hxy Hyz.
  revert dependent z.
  dependent induction Hxy;intros.
  - dependent destruction Hyz.
    + econstructor. lia.
    + econstructor. auto.
  - dependent destruction Hyz.
    + econstructor. auto.
    + econstructor. eauto.
Qed.

Hint Resolve Taglt_irrefl Taglt_trans : tagle.

Global Instance Taglt_StrictOrder : StrictOrder Taglt.
Proof.
  split; eauto with tagle.
Qed.

Global Instance Tagle_PreOrder : PreOrder Tagle.
Proof.
  eapply StrictOrder_PreOrder;eauto.
Qed.

Global Instance Tagle_PartialOrder : PartialOrder eq Tagle.
Proof.
  eapply StrictOrder_PartialOrder;eauto.
Qed.

Lemma Taglt_non_nil1 (i : Tag)
  : [] ◁ i -> False.
Proof.
  intro H. inversion H.
Qed.

Lemma Taglt_non_nil2 (i : Tag)
  : i ◁ [] -> False.
Proof.
  intro H. inversion H.
Qed.

Hint Immediate Taglt_non_nil1 Taglt_non_nil2 : tagle.

Lemma Taglt_len (i j : Tag)
      (Htaglt : i ◁ j)
  : | i | = | j |.
Proof.
  induction Htaglt;cbn;auto.
Qed.

Lemma Taglt_rcons_le (i j : Tag) (n m : nat)
      (Htaglt : i ++ [n] ◁ j ++ [m])
  : n <= m.
Proof.
  dependent induction Htaglt.
  - rewrite cons_rcons' in x0.
    rewrite cons_rcons' in x.
    eapply app_inj_tail in x0.
    eapply app_inj_tail in x.
    do 2 destructH. subst n m.
    cbn in *.
    rinduction i0; cbn in *.
    + lia.
    + rewrite rev_rcons. cbn. reflexivity.
  - destruct i0. inversion Htaglt.
    destruct j0. inversion Htaglt.
    eapply (IHHtaglt (tl i) (tl j));eauto.
    + destruct i;cbn in *;eauto. congruence. inversion x0. eauto.
    + destruct j;cbn in *;eauto. congruence. inversion x. eauto.
Qed.

Lemma Taglt_eq_rcons_lt (i : Tag) (n m : nat)
      (Htaglt : i ++ [n] ◁ i ++ [m])
  : n < m.
Proof.
  induction i;cbn in *.
  - inversion Htaglt;subst;auto. inversion H0.
  - eapply IHi. inversion Htaglt;subst.
    + lia.
    + auto.
Qed.

Hint Immediate Taglt_irrefl : tagle.

Lemma Taglt_eq_cons_lt (i : Tag) (n m : nat)
      (Htaglt : n :: i ◁ m :: i)
  : n < m.
Proof.
  inversion Htaglt;subst;eauto.
  exfalso. eapply Taglt_irrefl; eauto.
Qed.

Lemma Taglt_eq_rcons_Taglt (i j : Tag) (n : nat)
      (Htaglt : i ++ [n] ◁ j ++ [n])
  : i ◁ j.
Proof.
  eapply Taglt_len in Htaglt as Hlen.
  do 2 rewrite length_rcons in Hlen. eapply Nat.succ_inj in Hlen.
  destruct i;[|revert dependent i; revert dependent n0];induction j;cbn in *;intros.
  - exfalso. inversion Htaglt;subst. lia. eauto with tagle.
  - lia.
  - lia.
  - dependent destruction Htaglt.
    + eapply app_inj_tail in x; destruct x;subst.
      econstructor;eauto.
    + econstructor.
      destruct i,j; cbn in *.
      1: exfalso;eapply Taglt_irrefl;eauto.
      1,2: lia.
      eapply IHj;eauto.
Qed.

Lemma Taglt_le_rcons (n m : nat) (i j : Tag)
      (Htaglt : i ◁ j)
      (Hle : n <= m)
  : i ++ [n] ◁ j ++ [m].
Proof.
  induction Htaglt;cbn.
  - eapply le_lt_or_eq in Hle. destruct Hle.
    + econstructor;eauto. induction i; cbn; econstructor; eauto.
    + subst. econstructor;eauto.
  - econstructor;eauto.
Qed.

Lemma Taglt_lt_rcons (n m : nat) (i j : Tag)
      (Hlen : |i| = |j|)
      (Hlt : n < m)
  : i ++ [n] ◁ j ++ [m].
Proof.
  destruct i; intros.
  - destruct j; cbn in *.
    + econstructor; eauto.
    + lia.
  - revert n0 i Hlen.
    induction j; cbn in *; intros.
    + lia.
    + destruct i; cbn in *.
      * destruct j; cbn in *; [|lia].
        econstructor;econstructor;eauto.
      * econstructor.
        eapply IHj.
        lia.
Qed.

Lemma Taglt_ind_r
      (P : Tag -> Tag -> Prop)
      (Hbase : forall (n m : nat) (i j : Tag), |i| = |j| -> n < m -> P (i++[n]) (j++[m]))
      (Hstep : forall (n : nat) (i j : Tag), Taglt i j -> P i j -> P (i++[n]) (j++[n]))
      (i j : Tag)
      (Htaglt : Taglt i j)
  : P i j.
Proof.
  revert dependent j.
  rinduction i. 1: exfalso; eauto with tagle.
  revert dependent l. revert dependent a.
  rinduction j. 1: exfalso; eauto with tagle.
  eapply Taglt_len in Htaglt as Hlen.
  do 2 rewrite length_rcons in Hlen. eapply Nat.succ_inj in Hlen.
  eapply Taglt_rcons_le in Htaglt as Hle.
  eapply le_lt_or_eq in Hle.
  destruct Hle.
  - eapply Hbase;eauto.
  - subst a0.
    eapply Taglt_eq_rcons_Taglt in Htaglt.
    eapply Hstep;eauto.
Qed.

Lemma taglt_tagle_trans (i j k : Tag)
  : i ◁ j -> j ⊴ k -> i ◁ k.
Proof.
  intros.
  destruct H0.
  - transitivity j;eauto.
  - subst. auto.
Qed.

Lemma tagle_taglt_trans (i j k : Tag)
  : i ⊴ j -> j ◁ k -> i ◁ k.
Proof.
  intros.
  destruct H.
  - transitivity j;eauto.
  - subst. auto.
Qed.

Lemma le_cons_tagle n1 n2 i
      (Hlt : n1 <= n2)
  : n1 :: i ⊴ n2 :: i.
Proof.
  eapply le_lt_or_eq in Hlt. destruct Hlt.
  - econstructor. econstructor. assumption.
  - subst. reflexivity.
Qed.

Lemma lt_cons_ntagle n1 n2 i
      (Hlt : n2 < n1)
  : ~ n1 :: i ⊴ n2 :: i.
Proof.
  simpl_dec.
  split.
  - intro N.
    inv N.
    + lia.
    + eapply Taglt_irrefl;eauto.
  - intro N. inv N. lia.
Qed.

Lemma taglt_trichotomy i j
      (Hlen : |i| = |j|)
  : i ◁ j \/ i = j \/ j ◁ i.
Proof.
  remember (|i|) as n.
  revert i j Heqn Hlen.
  induction n;intros.
  - destruct i,j;cbn in *;try congruence. right. left. reflexivity.
  - destruct i,j;cbn in *;try congruence.
    specialize (IHn i j).
    exploit IHn.
    destruct IHn as [IHn|[IHn|IHn]];[left| |right;right].
    + econstructor;eauto.
    + subst.
      specialize (Nat.lt_trichotomy n0 n1) as Hcase.
      destruct Hcase as [Hcase|Hcase];[left|right];[|destruct Hcase as [Hcase|Hcase];[left|right]].
      * econstructor;eauto.
      * subst. reflexivity.
      * econstructor;eauto.
    + econstructor;eauto.
Qed.

Lemma tagle_or i j
      (Hlen : |i| = |j|)
  : i ⊴ j \/ j ⊴ i.
Proof.
  eapply taglt_trichotomy in Hlen.
  destruct Hlen as [Hlen|[Hlen|Hlen]];[left;left|left;right|right;left];eauto.
Qed.

Lemma Tagle_len: forall [i j : Tag], i ⊴ j -> | i | = | j |.
Proof.
  intros. destruct H.
  - eapply Taglt_len;eauto.
  - subst. reflexivity.
Qed.
