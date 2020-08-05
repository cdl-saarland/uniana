Require Import Program.Equality Lia.
Require Export ListExtra PreSuffix ListOrder.

Definition Tag := list nat.

(** * Tagle: relation that relates tags lexically *)

Inductive Tagle : Tag -> Tag -> Prop :=
| TgApp (i : Tag) : Tagle nil i
| TgEq  (n : nat) (i j : Tag) : Tagle i j -> Tagle (i :r: n) (j :r: n)
| TgLt (n m : nat) (i j : Tag) : n < m -> Tagle (i :r: n) (j :r: m).

Infix "⊴" := Tagle (at level 70).

Lemma Tagle_rcons (i j : Tag) (n m : nat)
      (H : i ⊴ j)
      (Hle : n <= m)
  : i :r: n ⊴ j :r: m.
Proof.
  eapply le_lt_or_eq in Hle. destruct Hle;subst;econstructor;eauto.
Qed.

Lemma Tagle_cons (i j : Tag) (n : nat)
      (H : i ⊴ j)
  : i ⊴ n :: j.
Proof.
  induction H.
  - econstructor.
  - rewrite <-cons_rcons_assoc. econstructor;eauto.
  - rewrite <-cons_rcons_assoc. econstructor;eauto.
Qed.

Lemma Tagle_refl (i : Tag)
  : i ⊴ i.
Proof.
  rinduction i.
  - econstructor.
  - econstructor;eauto.
Qed.

Lemma app_rcons_assoc (A : Type) (l l' : list A) (a : A)
  : l ++ l' :r: a = (l ++ l') :r: a.
Proof.
  eapply app_assoc.
Qed.

Lemma Tagle_app (i j : Tag)
  : j ⊴ i ++ j.
Proof.
  rinduction j.
  - econstructor.
  - rewrite app_rcons_assoc. econstructor. auto.
Qed.

Lemma Tagle_le (i j : Tag) (n m : nat)
      (H : i :r: n ⊴ j :r: m)
  : n <= m.
Proof.
  dependent induction H.
  - congruence'.
  - eapply rcons_eq2 in x0. eapply rcons_eq2 in x. subst. reflexivity.
  - eapply rcons_eq2 in x0. eapply rcons_eq2 in x. subst. lia.
Qed.

Hint Constructors Tagle : tagle.
Hint Immediate Tagle_app Tagle_le Tagle_refl Tagle_cons : tagle.

(** ** Preorder **)

Global Instance Tagle_PreOrder : PreOrder Tagle.
Proof.
  econstructor.
  - unfold Reflexive. eapply Tagle_refl.
  - unfold Transitive.
    intros x y z Hxy Hyz. revert dependent z.
    dependent induction Hxy;intros.
    + econstructor.
    + destr_r' z;subst.
      * inversion Hyz;try congruence'.
      * eapply Tagle_le in Hyz as Hle.
        eapply le_lt_or_eq in Hle. destruct Hle.
        -- econstructor;auto.
        -- subst.
           inversion Hyz;[congruence'| |].
           ++ eapply rcons_eq1 in H as Hj. subst.
              eapply rcons_eq2 in H. subst. econstructor.
              eapply rcons_eq1 in H0. subst. eapply IHHxy. auto.
           ++ eapply rcons_eq2 in H. subst. econstructor;auto.
    + destr_r' z;subst.
      * inversion Hyz;congruence'.
      * eapply Tagle_le in Hyz as Hle.
        eapply le_lt_or_eq in Hle. destruct Hle.
        -- econstructor;auto. lia.
        -- subst. econstructor. auto.
Qed.

(** ** Partialorder **)

Global Instance Tagle_PartialOrder : PartialOrder eq Tagle.
Proof.
  econstructor;intros.
  - subst. econstructor;unfold Basics.flip; eapply Tagle_refl.
  - inversion H. unfold Basics.flip in H1. clear H.
    revert dependent H1.
    induction H0;intros.
    + inversion H1;try congruence'. reflexivity.
    + inversion H1;[congruence' | |].
      * f_equal. eapply rcons_eq1 in H. eapply rcons_eq1 in H2.
        subst. eauto.
      * exfalso. eapply rcons_eq2 in H. eapply rcons_eq2 in H2. subst. lia.
    + inversion H1;[congruence' | |].
      * exfalso. eapply rcons_eq2 in H0. eapply rcons_eq2 in H2. subst. lia.
      * exfalso. eapply rcons_eq2 in H0. eapply rcons_eq2 in H2. subst. lia.
Qed.

Lemma prefix_tagle (i j : Tag)
      (Hpre : Prefix i j)
  : i ⊴ j.
Proof.
  induction Hpre;
    eauto with tagle.
Qed.

Lemma Tagle_app2 (i j k : Tag)
      (H : i ++ k ⊴ j ++ k)
  : i ⊴ j.
Proof.
  rinduction k.
  - do 2 rewrite app_nil_r in H. assumption.
  - eapply H.
    inversion H0.
    + destruct l;cbn in H2;congruence'.
    + rewrite app_rcons_assoc in H1. eapply rcons_eq1 in H1.
      rewrite app_rcons_assoc in H2. eapply rcons_eq1 in H2.
      subst. eauto.
    + rewrite app_rcons_assoc in H1. eapply rcons_eq2 in H1.
      rewrite app_rcons_assoc in H2. eapply rcons_eq2 in H2.
      subst. lia.
Qed.

Lemma Tagle_cons2 (i : Tag) (n m : nat)
      (Hle : n <= m)
  : n :: i ⊴ m :: i.
Proof.
  rinduction i.
  - fold (nil ++ [n]). fold ([] ++ [m]).
    fold ([] :r: n). fold ([] :r: m).
    eapply le_lt_or_eq in Hle.
    destruct Hle;subst;econstructor;eauto.
    reflexivity.
  - do 2 rewrite <-cons_rcons_assoc. econstructor;eauto.
Qed.

Lemma tagle_prefix_hd_le (n m : nat) (i j : Tag)
      (H2 : m :: i ⊴ j)
      (H1 : Prefix (n :: i) j)
  : m <= n.
Proof.
  eapply prefix_eq in H1.
  destructH.
  subst. rewrite app_cons_assoc in H2. fold ([m] ++ i) in H2. eapply Tagle_app2 in H2.
  fold (nil ++ [m]) in H2.
  fold ([] :r: m) in H2.
  eapply Tagle_le;eauto.
Qed.
