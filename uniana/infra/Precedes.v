Require Import Program.Equality.

Require Export ListExtra.

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
