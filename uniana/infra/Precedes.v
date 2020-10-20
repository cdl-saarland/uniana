Require Import Program.Equality.

Require Export ListExtra PreSuffix.

Inductive Precedes {A B : Type} (f : A -> B) : list A -> A -> Prop :=
| Pr_in : forall (k : A) (l : list A), Precedes f (k :: l) k
| Pr_cont : forall c k l, f c <> f k -> Precedes f l k -> Precedes f (c :: l) k.

Lemma precedes_in {A B : Type} k t (f : A -> B) :
  Precedes f t k -> In k t.
Proof.
  intros H.
  dependent induction t.
  - inversion H.
  - inversion H; eauto using In; cbn; eauto.
Qed.

Lemma precedes_app_drop (A B : Type) (l l' : list (A * B)) (a : A * B)
      (Hin : fst a ∈ map fst l)
      (Hprec : Precedes fst (l ++ l') a)
  : Precedes fst l a.
Proof.
  induction l;intros;inversion Hprec;cbn in *.
  - contradiction.
  - contradiction.
  - subst. econstructor;eauto.
  - subst. econstructor;eauto. eapply IHl;eauto. destruct Hin;[contradiction|]. eauto.
Qed.

Lemma precedes_rcons (A B : Type) (l : list (A * B)) (a x : A * B)
      (Hprec : Precedes fst (l ++ [a]) a)
      (Hnd : NoDup (l ++ [a]))
      (Hin : x ∈ l)
  : fst x <> fst a.
Proof.
  revert x Hin.
  induction l;intros;inversion Hprec;cbn in *;subst;eauto.
  - clear - Hnd. exfalso. inversion Hnd;subst. eapply H1. eapply In_rcons. eauto.
  - intro N. destruct x, a, a0. cbn in *. subst.
    destruct Hin.
    + inv H. contradiction.
    + eapply IHl;eauto. inversion Hnd;eauto.
Qed.

Lemma postfix_precedes (A B : Type) (l l' : list (A * B)) x
  : Postfix l l' -> Precedes fst l x -> Precedes fst l' x.
Proof.
  intros. eapply postfix_eq in H. destructH. subst l'.
  revert H0. induction l;intros;inversion H0;cbn;subst.
  - econstructor.
  - econstructor;eauto.
Qed.

Lemma precedes_app_nin (A B : Type) (l l' : list (A * B)) a b
      (Hprec : Precedes fst l (a,b))
      (Hnin : a ∉ map fst l')
  : Precedes fst (l' ++ l) (a,b).
Proof.
  induction l'.
  - cbn. eassumption.
  - cbn. destruct a0. econstructor;eauto.
    + contradict Hnin. cbn in Hnin. subst a0. cbn. left. reflexivity.
    + eapply IHl'. contradict Hnin. cbn. right. assumption.
Qed.

Lemma precedes_app_nin2 (A B : Type) (l l' : list (A * B)) a b
      (Hprec : Precedes fst (l' ++ l) (a,b))
      (Hnin : (a,b) ∉ l')
  : Precedes fst l (a,b).
Proof.
  induction l'.
  - cbn in Hprec. eassumption.
  - cbn in Hprec. destruct a0. inv Hprec.
    + exfalso. eapply Hnin. cbn. left. auto.
    + eapply IHl';eauto.
Qed.

Lemma precedes_prefix_NoDup (A B : Type) (a : A) (b : B) l l'
      (Hprec : Precedes fst l' (a,b))
      (Hpre : Prefix l l')
      (Hnd : NoDup l')
      (Hin : (a,b) ∈ l)
  : Precedes fst l (a,b).
Proof.
  eapply prefix_eq in Hpre. destructH. subst l'.
  induction l2'.
  - cbn in *. eauto.
  - inv Hprec.
    + exfalso. eapply NoDup_app;eauto.
    + inv Hnd. exploit IHl2'. eauto.
Qed.
