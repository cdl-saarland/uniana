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
