(**  non-empty lists 
    - this module includes the definition and basic facts about non-empty lists
**)

Require Import Lia.
Require Import Coq.Program.Equality.
Import Decidable.
Require Import Coq.Classes.Morphisms Relation_Definitions.

Require Export ListExtra.
Require Export DecTac.

(**  Definition of non-empty lists, basic functionality and notations **)

Inductive ne_list (A : Type) : Type :=
| ne_single : A -> ne_list A
| ne_cons : A -> ne_list A -> ne_list A.

Arguments ne_single {_} _.
Arguments ne_cons {_} _ _.

Infix ":<:" := ne_cons (at level 70,right associativity).

Fixpoint ne_conc (A : Type) (l l' : ne_list A) : ne_list A :=
  match l with
  | ne_single a => a :<: l'
  | ne_cons a l => a :<: ne_conc l l'
  end.

Infix ":+:" := ne_conc (at level 50).

Definition ne_rcons (A : Type) l a : ne_list A := l :+: ne_single a.

Infix ":>:" := ne_rcons (at level 50).

Section NeList.
  Variables (A : Type).
  
  Fixpoint ne_front (l : ne_list A) : A
    := match l with
       | ne_single a => a
       | ne_cons a _ => a
       end.

  Fixpoint ne_back (l : ne_list A) : A
    := match l with
       | ne_single a => a
       | ne_cons _ l => ne_back l
       end.

  Fixpoint ne_to_list (l : ne_list A) : list A
    := match l with
       | ne_single a => a :: nil
       | a :<: l => a :: ne_to_list l
       end.
End NeList.
  
Coercion ne_to_list : ne_list >-> list.

Fixpoint ne_tl (A : Type) (l : ne_list A) : list A
  := match l with
     | ne_single _ => nil
     | _ :<: l => l
     end.

Ltac congruence' ::=
  lazymatch goal with
  | [ H : ?l ++ (?a :: ?l') = nil |- _ ] => destruct l; cbn in H; congruence
  | [ H : (?l ++ ?l') :: ?a :: ?l'' = nil |- _ ] => destruct l; cbn in H; congruence
  | [ H : ?l :r: ?a = nil |- _ ] => eapply rcons_not_nil in H; contradiction
  | [ H : ne_to_list ?l = nil |- _ ] => destruct l; cbn in H; congruence
  | [ H : nil = ?l ++ (?a :: ?l') |- _ ] => destruct l; cbn in H; congruence
  | [ H : nil = (?l ++ ?l') :: ?a :: ?l'' |- _ ] => destruct l; cbn in H; congruence
  | [ H : nil = ?l :r: ?a |- _ ] => symmetry in H; eapply rcons_not_nil in H; contradiction
  | [ H : nil = ne_to_list ?l |- _ ] => destruct l; cbn in H; congruence
  end.

Fixpoint nlcons (A : Type) (a : A) l :=
  match l with
  | nil => ne_single a
  | b :: l => a :<: (nlcons b l)
  end.

Infix ":<" := nlcons (at level 50).

Definition nl_conc (A : Type) (l : ne_list A) (ll : list A) : ne_list A :=
  match ll with
  | nil => l
  | a :: ll => l :+: (a :< ll)
  end.

Infix ":+" := nl_conc (at level 50).

Fixpoint nl_rcons (A : Type) l (a : A) : ne_list A :=
  match l with
  | nil =>  ne_single a
  | b :: l => (b :<: (nl_rcons l a))
  end.

Infix ">:" := nl_rcons (at level 50).

Section NeList.
  Variables (A B : Type).
  
  Lemma nlcons_to_list (a : A) l :
    a :: l = nlcons a l.
  Proof.
    revert a. induction l; cbn; eauto. rewrite IHl. reflexivity.
  Qed.

  Lemma nlconc_to_list (l : ne_list A) (l' : list A)
    : l ++ l' = l :+ l'.
  Proof.
    destruct l';cbn.
    - eauto using app_nil_end.
    - induction l;cbn;[rewrite <-nlcons_to_list|];eauto.
      rewrite IHl. reflexivity.
  Qed.

  Lemma nlcons_front (a : A) l :
    ne_front (nlcons a l) = a.
  Proof.
    induction l; cbn; eauto.
  Qed.    

  Lemma nlcons_necons l :
    forall (a : A), (a :<: l) = nlcons a l.
  Proof.
    induction l; cbn; eauto. rewrite IHl. reflexivity.
  Qed.

  Lemma nlconc_neconc (l : ne_list A) l' :
    (l :+: l') = l :+ l'.
  Proof.
    intros. destruct l';cbn;eauto. rewrite nlcons_necons. reflexivity.
  Qed.

  Fixpoint ne_map (f : A -> B) (l : ne_list A) : ne_list B :=
    match l with
    | ne_single a => ne_single (f a)
    | a :<: l => (f a) :<: ne_map f l
    end.

  Lemma ne_map_nlcons (f : A -> B) (a : A) l :
    ne_map f (nlcons a l) = nlcons (f a) (map f l).
  Proof.
    revert a. induction l;intros b;cbn;firstorder.
    f_equal. eauto.
  Qed.

  Lemma nl_rcons_back (a : A) l :
    ne_back (l >: a) = a.
  Proof.
    induction l; cbn; eauto.
  Qed.

  Lemma ne_rcons_back (a : A) l :
    ne_back (l :>: a) = a.
  Proof.
    induction l; cbn; eauto.
  Qed.

  Lemma to_list_ne_map (f : A -> B) (l : ne_list A) :
    map f l = ne_map f l.
  Proof.
    intros. induction l;cbn;eauto. rewrite IHl. reflexivity.
  Qed.

  Lemma ne_back_map (f : A -> B) l :
    ne_back (ne_map f l) = f (ne_back l).
  Proof.
    induction l; firstorder.
  Qed.

  Lemma ne_to_list_inj (l l' : ne_list A) :
    ne_to_list l = ne_to_list l' -> l = l'.
  Proof.
    Set Printing Coercions.
    revert l'. induction l; induction l'; intros Heq; inversion Heq; cbn in *.
    - reflexivity.
    - exfalso. destruct l'; cbn in H1; congruence.
    - exfalso. destruct l; cbn in H1; congruence.
    - apply IHl in H1. subst l. econstructor.
      Unset Printing Coercions.
  Qed.
  
  Lemma ne_map_in (f:A->B) a (l:ne_list A) :
    In a l -> In (f a) (ne_map f l).
  Proof.
    intro Hin. induction l;cbn.
    - inversion Hin;[subst;tauto|contradiction].
    - cbn in Hin. destruct Hin;subst.
      + left. reflexivity.
      + right. eauto.
  Qed.

  Lemma ne_map_nl_rcons  (l : list A) a (f : A -> B)
    : ne_map f (l >: a) = (map f l) >: (f a).
  Proof.
    induction l;cbn;eauto. rewrite IHl. reflexivity.
  Qed.

  Lemma rcons_nl_rcons l (a:A) :
    l :r: a = nl_rcons l a.
  Proof.
    induction l; eauto. rewrite cons_rcons_assoc. rewrite IHl. cbn. reflexivity.
  Qed.

  Lemma ne_to_list_not_nil (l : ne_list A) :
    nil <> l.
  Proof.
    intro N. induction l; cbn in *; congruence.
  Qed.

  Lemma nercons_nlrcons l (a : A)
    : l :>: a = l >: a.
  Proof.
    induction l;cbn;eauto. rewrite <-IHl. destruct l;eauto.
  Qed.

  Lemma rcons_necons l (a : A)
    : (ne_to_list l) :r: a = l :>: a.
  Proof.
    induction l;cbn;eauto. rewrite IHl. reflexivity.
  Qed.

  Lemma ne_list_nlcons (l : ne_list A)
    : exists a l', l = a :< l'.
  Proof.
    destruct l as [a | a l'];exists a;[exists nil|exists l'];cbn;[|rewrite <-nlcons_necons];reflexivity.
  Qed.

  Lemma ne_list_nlrcons: forall (A : Type) (l : ne_list A), exists (a : A) (l' : list A), l = l' >: a.
  Proof.
    induction l.
    - exists a, nil. eauto.
    - destructH. rewrite IHl. exists a0, (a :: l'). cbn. reflexivity.
  Qed.
  
  Lemma neconc_app (l l' : ne_list A)
    : l ++ l' = l :+: l'.
  Proof.
    induction l;cbn;eauto.
    rewrite IHl. reflexivity.
  Qed.
  
  Lemma nl_cons_lr_shift (a b : A) (l : list A)
    : (a :<: (l >: b)) = ((a :< l) :>: b).
  Proof.
    revert a.
    induction l; intros; cbn ; eauto.
    fold ((ne_rcons (a :< l) b)). rewrite IHl. reflexivity.
  Qed.
  
  Lemma in_nlcons (l : list A) (a b : A)
    : a ∈ (b :< l) <-> a = b \/ a ∈ l.
  Proof.
    split; intro Q.
    - revert dependent b. induction l; cbn in *;intros b Q;[firstorder|].
      destruct Q;[firstorder|].
      right. specialize (IHl a0 H). firstorder.
    - revert dependent b. induction l; cbn in *;intros b Q;[firstorder|].
      destruct Q;[firstorder|].
      right. eapply IHl. firstorder.
  Qed.

  Lemma in_ne_conc (l l' : ne_list A)
    : forall a, a ∈ (l :+: l') <-> a ∈ l \/ a ∈ l'.
  Proof.
    split; revert a; induction l;intros b Q; cbn in *; firstorder 0.
  Qed.

  Lemma in_nl_conc (l : ne_list A) l' (a : A)
    : a ∈ (l :+ l') <-> a ∈ l \/ a ∈ l'.
  Proof.
    split;revert a;induction l'; intros b Q; cbn in *; [firstorder| |firstorder|].
    - eapply in_ne_conc in Q. repeat destruct Q; eauto. eapply in_nlcons in H. destruct H;eauto.
    - eapply in_ne_conc. repeat destruct Q; eauto. right. eapply in_nlcons. firstorder.
  Qed.

End NeList.

Lemma nin_tl_iff (A : Type) `{EqDec A eq} (a : A) (l : ne_list A)
  : a ∉ tl (rev l) -> a ∉ l \/ a = ne_back l.
Proof.
  intros.
  decide' (a == ne_back l);eauto.
  left. contradict H0. induction l;cbn in *;eauto.
  - destruct H0;eauto. congruence.
  - fold ((rev l) :r: a0).
    rewrite tl_rcons;[eapply In_rcons;eauto|destruct l;cbn;eauto;erewrite app_length;cbn;lia].
    destruct H0.
    + subst. eauto.
    + right. eapply IHl;eauto.
Qed.

Lemma find_some' (A : Type) (f : A -> bool) (l : list A) (x : A)
      (Hl : x ∈ l)
      (Hf : f x = true)
  : exists y, Some y = find f l.
Proof.
  induction l;cbn;[contradiction|].
  destruct Hl;subst.
  - rewrite Hf. eauto.
  - destruct (f a);eauto.
Qed.

