
(** in_before, in_between & succ_in **)
Require Import Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.EquivDec.
Require Import Util NeList.

Definition in_before {A : Type} :=
  fun (l : list A) a b => exists l' : list A, Prefix (b :: l') l /\ a ∈ (b :: l').

Inductive inBefore {A : Type} : list A -> A -> A -> Prop :=
| ibRefl l (a : A) : a ∈ l -> inBefore l a a
| ibPred l (a b : A) : a ∈ l -> inBefore (b :: l) a b
| ibStep l (a b c : A) : inBefore l a b -> inBefore (c :: l) a b.

Notation "l ⊢ a ≺* b" := (in_before l a b) (at level 70).

Definition in_between {A : Type} l (a b c : A)
  := l ⊢ a ≺* b /\ l ⊢ b ≺* c.

Notation "l ⊢ a ≺* b ≺* c" := (in_between l a b c) (at level 70, b at next level).

Definition succ_in {A : Type} l (a b : A)
  := exists l1 l2, l = l2 ++ a :: b :: l1.

Notation "l ⊢ a ≻ b" := (succ_in l a b) (at level 70).

Ltac destr_inb H :=
  let H1 := fresh H in
  let H2 := fresh H in
  let H3 := fresh H in
  lazymatch type of H with
  | ?l ⊢ ?a ≺* ?b => let l' := fresh l in
                    destruct H as [l' [H1 [H2|H3]]]
  | ?l ⊢ ?a ≺* ?b ≺* ?c => destruct H as [H1 H2];
                          destr_inb H1; destr_inb H2
  end.

Section inBefore1.

  Context {A : Type} `{EqDec A eq}.

  Lemma inBefore_cons (a b c : A) l
        (Hin : inBefore l a b)
    : inBefore (c :: l) a b.
  Proof.
    revert c. induction Hin; econstructor; [firstorder|econstructor|econstructor];eauto.
  Qed.

  Lemma inBefore_prefix (a b : A) l l'
        (Hin : inBefore l a b)
        (Hpre : Prefix l l')
    : inBefore l' a b.
  Proof.
    induction Hpre; eauto.
    eapply inBefore_cons; eauto.
  Qed.

  Lemma in_before_refl (a : A) l
        (Hin : a ∈ l)
    : l ⊢ a ≺* a.
  Proof.
    induction l; cbn in *;[contradiction|].
    decide' (a == a0).
    - exists l. split;[econstructor|firstorder].
    - destruct Hin;[congruence|]. specialize (IHl H0). destruct IHl as [l' [IHl _]].
      exists l'. split;[|firstorder].
      econstructor;eauto.
  Qed.

  Lemma in_before_cons (a b c : A) l
        (Hin : l ⊢ a ≺* b)
    : c :: l ⊢ a ≺* b.
  Proof.
    destr_inb Hin; subst.
    - eapply in_before_refl. right. eapply prefix_incl;eauto. firstorder.
    - unfold in_before. exists l0. split;[|firstorder].
      econstructor;eauto.
  Qed.

End inBefore1.

Section inBefore2.

  Context {A : Type} `{EqDec A eq}.
  
  Lemma in_before_inBefore (a b : A) l
    : in_before l a b <-> inBefore l a b.
  Proof.
    split; intro Hin.
    - destr_inb Hin; subst.
      + eapply prefix_incl in Hin0. assert (a ∈ l) as Hin1 by (eapply Hin0;firstorder).
        clear Hin0. induction l; [cbn in *; contradiction|].
        decide' (a == a0).
        * econstructor;eauto.
        * eapply inBefore_cons;eapply IHl. destruct Hin1; [congruence|eauto].
      + eapply inBefore_prefix;eauto. econstructor;eauto.
    - induction Hin.
      + eapply in_before_refl;eauto.
      + exists l. split;[econstructor|firstorder].
      + eapply in_before_cons;eauto.
  Qed.

  Lemma in_before_trans (p q r : A) π
        (Hnd : NoDup π)
        (Hib__pq : π ⊢ p ≺* q)
        (Hib__qr : π ⊢ q ≺* r)
    : π ⊢ p ≺* r.
  Proof.
    unfold in_before in *. destruct Hib__pq as [l__pq Hib__pq]. destruct Hib__qr as [l__qr Hib__qr].
    do 2 destructH.
    exists l__qr. split.
    - eauto.
    - eapply prefix_incl;eauto.
      induction π.
      + inversion Hib__pq0.
      + decide' (r == a).
        * inversion Hib__qr0;subst;eauto.
          exfalso. inversion Hnd; subst. eapply H3. eapply prefix_incl;eauto. left. reflexivity.
        * inversion Hnd; subst. eapply IHπ;eauto.
          -- inversion Hib__pq0;subst;eauto.
             exfalso. eapply H2. inversion Hib__qr0;subst; [congruence|].
             eapply prefix_incl;eauto.
          -- inversion Hib__qr0;subst;eauto.
             congruence.
  Qed.

  Lemma in_between_in_before (p q r : A) π
        (Hnd : NoDup π)
        (Hib : π ⊢ p ≺* q ≺* r)
    : π ⊢ p ≺* r. 
  Proof.
    destruct Hib. eapply in_before_trans;eauto.
  Qed.

  Lemma in_before_prefix (p q : A) π ϕ
        (Hnd : NoDup π)
        (Hpre : Prefix ϕ π)
        (Hin : q ∈ ϕ)
    : in_before π p q <-> in_before ϕ p q.
  Proof.
    unfold in_before. split;intro Hib; destructH.
    - induction π;inversion Hpre;inversion Hib0;inversion Hnd; subst; eauto.
      exfalso. eapply H9. eapply prefix_incl;eauto.
    - eapply prefix_NoDup in Hnd;eauto.
      induction ϕ;inversion Hpre;inversion Hib0;inversion Hnd;subst;eauto.
      decide' (q == a).
      + exfalso. eapply H9. eapply prefix_incl;eauto. left. reflexivity.
      + eapply IHϕ;eauto.
        * econstructor. eapply prefix_cons;eauto.
        * eapply prefix_incl;eauto. left. reflexivity.
  Qed.

  Lemma in_fst' {B : Type} (a : A) (b : B) l
        (Hin : (a,b) ∈ l)
    : a ∈ map fst l.
  Proof.
    induction l; cbn in *; [contradiction|].
    destruct Hin;[subst;cbn;eauto|right;eauto].
  Qed.

End inBefore2.

Section inBefore3.
  Context {A : Type} `{EqDec A eq}.
  
  Lemma in_before_map {B : Type} `{EqDec B eq} (a1 a2 : A) (b1 b2 : B) l
        (Hin : l ⊢ (a1,b1) ≺* (a2,b2))
    : map fst l ⊢ a1 ≺* a2.
  Proof.
    eapply in_before_inBefore in Hin. eapply in_before_inBefore.
    dependent induction Hin;cbn;econstructor.
    1,2:eapply in_fst';eauto.
    eapply IHHin;eauto.
  Qed.
  
  Lemma in_between_in2 (x y z : A) l
        (Hib : l ⊢ x ≺* y ≺* z)
    : y ∈ l.
  Proof.
    unfold in_between,in_before in *. destructH. eapply prefix_incl;eauto.
  Qed.
End inBefore3.
Create HintDb in_before.
Hint Immediate in_before_trans in_between_in_before in_between_in2 in_before_prefix in_before_map
  : in_before.

Inductive splinter {A : Type} : list A -> list A -> Prop :=
| sl_nil : splinter nil nil
| sl_right l l' a : splinter l l' -> splinter l (a :: l')
| sl_left l l' a : splinter l (a :: l') -> splinter (a :: l) (a :: l'). (* it should be reflexive *)

(*Inductive segments {A : Type} : list (list A) -> list A -> Prop :=
| seg_nil : segments nil nil
| seg_cons L l a : segments L l -> segments L (a :: l)
| seg_app L l l' : segments L l -> segments (l' :: L) (l' ++ l).*)

Notation "l1 ⊴ l2" := (splinter l1 l2) (at level 70).

Section splinter.
  Context {A : Type} `{EqDec A eq}.

  Create HintDb splinter discriminated.
Lemma splinter_prefix (l l1 l2 : list A)
      (Hin : splinter l l1)
      (Hpre : Prefix l1 l2)
  : splinter l l2.
Proof.
  induction Hpre; eauto.
  econstructor; eauto.
Qed.

Lemma splinter_nil (l : list A)
  : splinter nil l.
Proof.
  induction l; econstructor;eauto.
Qed.

Lemma splinter_refl (a : A) l
      (Hin : a ∈ l)
  : splinter (a :: a :: nil) l.
Proof.
  induction l; cbn in *;[contradiction|].
  destruct Hin. subst. econstructor 3. econstructor 3. eapply splinter_nil.
  econstructor 2. eauto.
Qed.

Hint Immediate splinter_prefix splinter_nil : splinter.

Lemma post_pre_nincl_NoDup (l : list A) (a : A)
      (Hin : a ∈ l)
  : l = postfix_nincl a l ++ a :: prefix_nincl a l.
Proof.
  induction l; cbn in *;[contradiction|].
  decide' (a == a0);subst;cbn;eauto.
  destruct Hin;[congruence|]. 
  f_equal. eauto.
Qed.

Lemma splinter_app (l1 l2 l1' l2' : list A)
      (Hleft : splinter l1' l1)
      (Hright : splinter l2' l2)
  : splinter (l1' ++ l2') (l1 ++ l2).
Proof.
  induction Hleft; cbn in *;eauto.
  - econstructor;eauto.
  - econstructor 3. eauto.
Qed.

Lemma splinter_in (a : A) l l'
      (Hsp : splinter (a :: l) l')
  : a ∈ l'.
Proof.
  dependent induction Hsp;[|firstorder].
  do 2 exploit' IHHsp. 
  specialize (IHHsp a l eq_refl).
  firstorder.
Qed.

Lemma splinter_cons (a : A) l l'
      (Hsp : splinter (a :: l) l')
  : splinter l l'.
Proof.
  dependent induction Hsp; do 2 exploit' IHHsp.
  - specialize (IHHsp a l eq_refl). econstructor;eauto.
  - eauto.
Qed.

Lemma splinter_incl (l l' : list A)
      (Hsp : splinter l l')
  : l ⊆ l'.
Proof.
  induction l; cbn; [firstorder|].
  unfold incl. intros a0 Ha0. destruct Ha0;subst.
  - eapply splinter_in; eauto.
  - eapply IHl;eauto. eapply splinter_cons. eauto.
Qed.

Lemma splinter_lr l l' (a : A)
      (Hsp : splinter l l')
  : splinter (a :: l) (a :: l').
Proof.
  econstructor;econstructor;eauto.
Qed.

Hint Immediate splinter_app splinter_in splinter_cons splinter_incl splinter_lr : splinter.

Lemma splinter_rcons_nin (a : A) l l'
      (Hnin : a ∉ l)
      (Hsp : splinter (l :r: a) l')
  : splinter l (postfix_nincl a l').
Admitted.

Lemma splinter_cons_nin (a : A) l l'
      (Hnin : a ∉ l)
      (Hsp : splinter (a :: l) l')
  : splinter l (prefix_nincl a l').
Admitted.

Lemma splinter_trans (l1 l2 l3 : list A)
      (H12 : splinter l1 l2)
      (H23 : splinter l2 l3)
  : splinter l1 l3.
Proof.
  revert dependent l1;induction H23;intros;eauto.
  - econstructor;eauto.
  - dependent induction H12; do 2 exploit' IHsplinter0; intros.
    + eapply IHsplinter; eauto. 
    + econstructor 3. eapply IHsplinter0;eauto.
Qed.

Lemma splinter_double (l1 l2 l' : list A) a
      (Hsp : splinter (l1 ++ a :: l2) l')
  : splinter (l1 ++ a :: a :: l2) l'.
Proof.
  dependent induction Hsp;cbn in *.
  - congruence'.
  - econstructor. eapply IHHsp; eauto.
  - destruct l1; inversion x; subst; cbn in *.
    + do 2 econstructor 3;eauto.
    + econstructor 3. eapply IHHsp; eauto.
Qed.

Lemma splinter_remove (l1 l2 l' : list A) a
      (Hsp : splinter (l1 ++ a :: l2) l')
  : splinter (l1 ++ l2) l'.
Proof.
  dependent induction Hsp; cbn in *; subst.
  - congruence'.
  - econstructor. eapply IHHsp;eauto.
  - destruct l1; inversion x; subst; cbn in *; eauto.
    econstructor 3. eapply IHHsp; eauto.
Qed.

Lemma splinter_remove_dup (l1 l2 l' : list A) a
      (Hsp : splinter l' (l1 ++ a :: a :: l2))
  : splinter l' (l1 ++ a :: l2). 
Proof.
  dependent induction Hsp; cbn in *; subst.
  - congruence'.
  - destruct l1; cbn in *.
    + inversion x; subst; eauto.
    + econstructor. eapply IHHsp; eauto. inversion x; subst; eauto.
  - destruct l1; cbn in *.
    + inversion x; subst. econstructor 3. specialize (IHHsp H nil). cbn in IHHsp.
      eapply IHHsp. reflexivity.
    + inversion x; subst. econstructor 3. rewrite app_comm_cons. eapply IHHsp;eauto.
Qed.  

Lemma app_cons_assoc (a : A) l l'
  : l ++ a :: l' = l :r: a ++ l'.
Proof.
  induction l; cbn; eauto.
  f_equal. rewrite IHl. reflexivity.
Qed.

Lemma splinter_app_l (a : A) l0 l l'
      (Hnd : NoDup l0)
      (Hleft : splinter (l :r: a) l0)
      (Hright : splinter (a :: l') l0)
  : splinter (l ++ a :: l') l0.
Proof.
  rewrite (post_pre_nincl_NoDup l0 a);[|eapply splinter_incl;eauto;firstorder].
  eapply splinter_remove_dup. setoid_rewrite app_cons_assoc at 2.
  eapply splinter_app;[clear Hright|clear Hleft; econstructor 3].
  - admit.
  - admit.
Admitted.
  
