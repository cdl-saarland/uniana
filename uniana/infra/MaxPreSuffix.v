Require Export PreSuffix.

Fixpoint while' {A : Type} (P : decPred A) (l : list A) : list A
  := match l with
     | nil => nil
     | a :: l => if decision (P a) then a :: while' P l else nil
     end.

Definition while {A : Type} (P : decPred A) (l : list A) : list A
  := rev (while' P (rev l)).

Lemma while'_postfix {A : Type} (P : decPred A) (l l' : list A)
      (H : while' P l = l')
  : Postfix l' l.
Proof.
  revert dependent l'.
  induction l; intros; cbn in *; eauto.
  - subst. constructor.
  - decide (P a).
    + destruct l';[congruence|]. inversion H; subst.
      eapply postfix_cons. eapply IHl. reflexivity.
    + subst. eapply postfix_nil.
Qed.

Lemma while_prefix {A : Type} (P : decPred A) (l l' : list A)
      (H : while P l = l')
  : Prefix l' l.
Proof.
  eapply postfix_rev_prefix'.
  unfold while in H. rewrite <-H.
  rewrite rev_involutive.
  eapply while'_postfix;eauto.
Qed.
  
Lemma while'_Forall {A : Type} (P : decPred A) (l : list A)
  : Forall P (while' P l).
Proof.
  induction l;cbn;eauto.
  decide (P a).
  - econstructor;eauto.
  - econstructor.
Qed.
  
Lemma while_Forall {A : Type} (P : decPred A) (l : list A)
  : Forall P (while P l).
Proof.
  unfold while. rewrite Forall_forall. setoid_rewrite <-in_rev. rewrite <-Forall_forall.
  eapply while'_Forall.
Qed.

Lemma while'_app {A : Type} (P : decPred A) (l l' : list A)
      (H : Forall P l)
  : while' P (l ++ l') = l ++ while' P l'.
Proof.
  induction l;cbn;auto.
  inversion H;subst. exploit IHl.
  decide (P a);[|contradiction]. rewrite IHl. auto.
Qed.

Lemma while'_max {A : Type} (P : decPred A) (l l' : list A) a
      (Hpost : Postfix (l' :r: a) l)
      (Hw : while' P l = l')
  : ~ P a.
Proof.
  rewrite postfix_eq in Hpost.
  destructH.
  rewrite Hpost in Hw.
  intro N. rewrite while'_app in Hw.
  - clear - Hw. induction l';cbn in Hw;[congruence|]. eapply IHl'. inversion Hw. rewrite H0 at 1. reflexivity.
  - rewrite Forall_forall. setoid_rewrite In_rcons. intros. destruct H;subst;auto.
    eapply Forall_forall in H;eauto. rewrite <-Hw.
    eapply while'_Forall.
Qed.
    
  
Lemma while_max {A : Type} (P : decPred A) (l l' : list A) a
      (Hpre : Prefix (a :: l') l)
      (Hw : while P l = l')
  : ~ P a.
Proof.
  unfold while in Hw.
  rewrite <-rev_involutive in Hw. eapply rev_injective in Hw.
  eapply while'_max;eauto.
  rewrite <-rev_cons. eapply prefix_rev_postfix;eauto.
Qed.

Lemma while'_forall (A : Type) (P : decPred A) (l : list A) a
      (Hin : a ∈ while' P l)
  : P a.
Proof.
  eapply Forall_forall;[|eapply Hin]. eapply while'_Forall.
Qed.