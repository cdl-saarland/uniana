
(** in_before, in_between & succ_in **)
Require Import Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.EquivDec.
Require Import Util NeList.



Local Definition prefix_nincl' {A : Type} `{EqDec A eq} (a : A) l
  := rev (postfix_nincl a (rev l)).

Section aux.

  Context {A : Type} `{EqDec A eq}.

  Lemma app_cons_assoc (a : A) l l'
  : l ++ a :: l' = l :r: a ++ l'.
  Proof.
    induction l; cbn; eauto.
    f_equal. rewrite IHl. reflexivity.
  Qed.
  
  Lemma postfix_nincl_rcons_a (a : A) (l : list A)
    : postfix_nincl a (l :r: a) = postfix_nincl a l.
  Proof.
    induction l; cbn; eauto.
    - decide' (a == a);[eauto|congruence].
    - decide' (a == a0);eauto.
      rewrite <-IHl. reflexivity.
  Qed.

  Hint Resolve postfix_nincl_rcons_a.

  Lemma postfix_nincl_app_in (a : A) (l l' : list A)
        (Hin : a ∈ l)
    : postfix_nincl a (l ++ l') = postfix_nincl a l.
  Proof.
    induction l; cbn; eauto.
    - contradiction.
    - destruct Hin; subst.
      + decide' (a == a); eauto. congruence.
      + decide' (a == a0);eauto.
        rewrite IHl;eauto.
  Qed.

  Hint Resolve postfix_nincl_app_in.
  
  Lemma post_pre_nincl_NoDup (l : list A) (a : A)
        (Hnd : NoDup l)
        (Hin : a ∈ l)
    : l = postfix_nincl a l ++ a :: prefix_nincl' a l.
  Proof.
    induction l; cbn in *;[contradiction|].
    destruct Hin;subst.
    - decide' (a == a); [|congruence]. cbn.
      f_equal.
      fold (rcons (rev l) a). rewrite postfix_nincl_rcons_a.
      rewrite postfix_nincl_invariant; eauto using rev_involutive.
      rewrite <-in_rev. inversion Hnd; eauto.
    - decide' (a == a0);[inversion Hnd;subst;contradiction|cbn].
      f_equal. rewrite postfix_nincl_app_in. eapply IHl; inversion Hnd; eauto.
      rewrite <-in_rev; eauto.
  Qed.
  
  Lemma rev_rev_eq (l l' : list A)
    : l = l' <-> rev l = rev l'.
  Proof.
    revert l l'.
    enough (forall (l l' : list A), l = l' -> rev l = rev l').
    { split;eauto. intros. rewrite <-rev_involutive. rewrite <-rev_involutive at 1. eauto. }
    intros ? ? Hll.
    subst. reflexivity.
  Qed.

  Lemma postfix_nincl_rev_prefix_nincl' (a : A) l
    : rev (postfix_nincl a l) = prefix_nincl' a (rev l).
  Proof.
    unfold prefix_nincl'. rewrite rev_involutive. reflexivity.
  Qed.

  Lemma NoDup_rcons (l : list A) a
        (Hnd : NoDup l)
        (Hnin : a ∉ l)
    : NoDup (l :r: a).
  Proof.
    induction l; cbn; eauto.
    - econstructor;eauto.
    - econstructor.
      + contradict Hnin.
        eapply In_rcons in Hnin. destruct Hnin;[left;eauto|inversion Hnd;contradiction].
      + eapply IHl; inversion Hnd;subst; eauto. firstorder.
  Qed.

  Lemma NoDup_rev (l : list A)
    : NoDup l -> NoDup (rev l).
  Proof.
    intros Hnd; induction Hnd; cbn;eauto.
    econstructor.
    eapply NoDup_rcons;eauto. rewrite <-in_rev;eauto.
  Qed.

End aux.

Inductive splinter {A : Type} : list A -> list A -> Prop :=
| sl_nil : splinter nil nil
| sl_copy l l' a : splinter l (a :: l') -> splinter (a :: l) (a :: l')
| sl_skip l l' a : splinter l l' -> splinter l (a :: l').

(*Inductive splinter_strict {A : Type} : list A -> list A -> Prop :=
| sls_nil : splinter_strict nil nil
| sls_sim l l' a : splinter_strict l l' -> splinter_strict (a :: l) (a :: l')
| sls_skip l l' a : splinter_strict l l' -> splinter_strict l (a :: l').  *)

Notation "l1 ⊴ l2" := (splinter l1 l2) (at level 70).

(* Read: a succeeds b in l modulo reflexivity and transitivity *)
Notation "a ≻* b | l" := (splinter (a :: b :: nil) l) (at level 70, b at next level).
Notation "a ≻* b ≻* c | l" := (splinter (a :: b :: c :: nil) l) (at level 70,
                                                                 b at next level,
                                                                c at next level).
Notation "a ≻* b ≻* c ≻* d | l" := (splinter (a :: b :: c :: d :: nil) l) (at level 70,
                                                                           b at next level,
                                                                           c at next level,
                                                                           d at next level).
Notation "a ≻* b ≻* c ≻* d ≻* e | l" := (splinter (a :: b :: c :: d :: e :: nil) l) (at level 70,
                                                                                     b at next level,
                                                                                     c at next level,
                                                                                     d at next level).

Definition succ_in {A : Type} l (a b : A)
  := exists l1 l2, l = l2 ++ a :: b :: l1.

Notation "a ≻ b | l" := (succ_in l a b) (at level 70).

Module SplinterAux.

  Section splinter_aux.

    Context {A : Type} `{EqDec A eq}.
    
    Lemma splinter_double (l1 l2 l' : list A) a
          (Hsp : splinter (l1 ++ a :: l2) l')
      : splinter (l1 ++ a :: a :: l2) l'.
    Proof.
      dependent induction Hsp;cbn in *.
      - congruence'.
      - destruct l1; inversion x; subst; cbn in *.
        + do 2 econstructor;eauto.
        + econstructor. eapply IHHsp; eauto.
      - econstructor. eapply IHHsp; eauto.
    Qed.

    Hint Resolve splinter_double.

    Lemma splinter_remove (l1 l2 l' : list A) a
          (Hsp : splinter (l1 ++ a :: l2) l')
      : splinter (l1 ++ l2) l'.
    Proof.
      dependent induction Hsp; cbn in *; subst.
      - congruence'.
      - destruct l1; inversion x; subst; cbn in *; eauto.
        econstructor. eapply IHHsp; eauto.
      - econstructor. eapply IHHsp;eauto.
    Qed.

    Hint Resolve splinter_remove.

    Lemma splinter_remove_dup (l1 l2 l' : list A) a
          (Hsp : splinter l' (l1 ++ a :: a :: l2))
      : splinter l' (l1 ++ a :: l2). 
    Proof.
      dependent induction Hsp; cbn in *; subst.
      - congruence'.
      - destruct l1; cbn in *.
        + inversion x; subst. econstructor. specialize (IHHsp H nil). cbn in IHHsp.
          eapply IHHsp. reflexivity.
        + inversion x; subst. econstructor. rewrite app_comm_cons. eapply IHHsp;eauto.
      - destruct l1; cbn in *.
        + inversion x; subst; eauto.
        + econstructor. eapply IHHsp; eauto. inversion x; subst; eauto.
    Qed.

    Hint Resolve splinter_remove_dup.

    Lemma splinter_rcons_right (a : A) l l'
          (Hsp : splinter l l')
      : splinter l (l' :r: a).
    Proof.
      induction Hsp; cbn in *; econstructor;eauto.
      econstructor.
    Qed.

    Hint Resolve splinter_rcons_right.

    Hint Constructors splinter.

    Lemma splinter_rcons_left (a : A) l l'
          (Hsp : splinter l (l' :r: a))
      : splinter (l :r: a) (l' :r: a).
    Proof.
      dependent induction Hsp; cbn in *.
      - congruence'.
      - rewrite <-x. econstructor. rewrite x. eauto.
      - rewrite <-x. destruct l'; cbn in *.
        + inversion x; subst. inversion Hsp; subst; cbn; eauto.
        + econstructor. inversion x; subst. eapply IHHsp; eauto.
    Qed.
    
  End splinter_aux.

End SplinterAux.

Import SplinterAux.

Hint Resolve
     splinter_double
     splinter_remove
     splinter_remove_dup
     splinter_rcons_left
     splinter_rcons_right : splinter.
     

Section splinter.
  Context {A : Type} `{EqDec A eq}.

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

  Hint Constructors splinter.
  
  Lemma splinter_refl (l : list A)
    : splinter l l.
  Proof.
    induction l; eauto with splinter.
  Qed.
  
  Lemma splinter_app (l1 l2 l1' l2' : list A)
        (Hleft : splinter l1' l1)
        (Hright : splinter l2' l2)
    : splinter (l1' ++ l2') (l1 ++ l2).
  Proof.
    induction Hleft; cbn in *;eauto.
  Qed.

  Lemma splinter_in (a : A) l l'
        (Hsp : splinter (a :: l) l')
    : a ∈ l'.
  Proof.
    dependent induction Hsp;[firstorder|].
    do 2 exploit' IHHsp. 
    specialize (IHHsp a l eq_refl).
    firstorder.
  Qed.

  Lemma splinter_cons (a : A) l l'
        (Hsp : splinter (a :: l) l')
    : splinter l l'.
  Proof.
    dependent induction Hsp; do 2 exploit' IHHsp.
    - eauto.
    - specialize (IHHsp a l eq_refl). econstructor;eauto.
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
  
  Hint Resolve splinter_nil splinter_in splinter_incl : splinter.

  Lemma splinter_single (a : A) l
    : splinter (a :: nil) l <-> a ∈ l.
  Proof.
    split; intro Hsp; [eapply splinter_in;eauto|].
    induction l;[contradiction|].
    destruct Hsp;subst; repeat (econstructor;eauto with splinter).
  Qed.

  Lemma splinter_lr l l' (a : A)
        (Hsp : splinter l l')
    : splinter (a :: l) (a :: l').
  Proof.
    econstructor;econstructor;eauto.
  Qed.

  Lemma splinter_trans (l1 l2 l3 : list A)
        (H12 : splinter l1 l2)
        (H23 : splinter l2 l3)
    : splinter l1 l3.
  Proof.
    revert dependent l1;induction H23;intros;eauto.
    - dependent induction H12; do 2 exploit' IHsplinter0; intros.
      + econstructor. eapply IHsplinter0;eauto.
      + eapply IHsplinter; eauto. 
  Qed.

  Hint Constructors splinter.
  Hint Unfold rcons.

  Lemma splinter_rev (l l' : list A)
    : splinter l l' <-> splinter (rev l) (rev l').
  Proof.
    revert l l'.
    enough (forall (l l' : list A), splinter l l' -> splinter (rev l) (rev l')).
    {
      split;eauto. intros Hrev. rewrite <-rev_involutive. rewrite <- rev_involutive at 1.
      eapply H0; eauto.
    }
    intros ? ? Hsp.
    induction Hsp; cbn in *; eauto;
      fold (rcons (rev l) a); fold  (rcons (rev l') a);eauto with splinter.
  Qed.

  Lemma splinter_app_l (a : A) l0 l l'
        (Hnd : NoDup l0)
        (Hleft : splinter (l :r: a) l0)
        (Hright : splinter (a :: l') l0)
    : splinter (l ++ a :: l') l0.
  Proof.
    rewrite (post_pre_nincl_NoDup l0 a);eauto; [|eapply splinter_incl;eauto;firstorder].
    eapply splinter_remove_dup. setoid_rewrite app_cons_assoc at 2.
    assert (forall (l' l0 : list A),
               NoDup l0
               -> splinter (a :: l') l0
               -> splinter l' (a :: prefix_nincl' a l0)).
    {
      clear. intros ? ? Hnd Hsp.
      assert (a ∈ l0) as Hin by (eauto with splinter).
      rewrite (post_pre_nincl_NoDup l0 a) in Hsp;eauto.
      set (l1 := postfix_nincl a l0) in *.
      assert (a ∉ l1) by eapply postfix_nincl_nincl.
      induction l1;cbn in *.
      + eapply splinter_cons;eauto.
      + assert (a0 <> a /\ a ∉ l1) as [Hneq Hnin] by firstorder. clear H0.
        eapply IHl1;eauto.
        inversion Hsp;subst;eauto.
        contradiction.
    }
    eapply splinter_app;[clear Hright|clear Hleft; econstructor; eauto].
    - eapply splinter_rev in Hleft.  rewrite rev_rcons in Hleft.
      eapply splinter_rev. rewrite rev_rcons.
      erewrite postfix_nincl_rev_prefix_nincl'. eapply H0; eauto.
      eauto using NoDup_rev.
  Qed.

  Ltac anthithesis H :=
    lazymatch type of H with
    | Postfix (_ :: _) nil => exfalso; eapply postfix_nil_nil in H; congruence
    end.
  
  Lemma splinter_postfix (l l' l'' : list A)
        (Hpost : Postfix l l')
        (Hsp : splinter l'' l)
    : splinter l'' l'.
  Proof with (eauto with splinter).
    induction Hpost...
  Qed.
  
End splinter.

Hint Constructors splinter : splinter.
Hint Resolve splinter_nil splinter_in splinter_incl : splinter.


Ltac splice_splinter :=
  match goal with
  | [H : splinter ?l1 ?l,
     Q : splinter ?l2 ?l |- _ ]
    => lazymatch l2 with
      | ?a :: _
        => lazymatch l1 with
          | context C [a :: nil]
            => fold_rcons H; eapply (splinter_app_l a l) in H;[|eauto|eapply Q];
              clear Q; cbn in H
          end
      end
  end.

Section succ_rt.
  Context {A : Type} `{EqDec A eq}.

  Lemma succ_rt_prefix (a b : A) l
        (Hsp : a ≻* b | l)
    : exists l', Prefix (a :: l') l /\ b ∈ (a :: l').
  Proof.
    dependent induction Hsp; do 2 exploit' IHHsp.
    - exists l'. split; [econstructor| eauto with splinter].
    - specialize (IHHsp _ _ eq_refl). destructH. eexists. split; [ econstructor|]; eauto.
  Qed.
  
  Lemma succ_rt_refl (a : A) l
        (Hin : a ∈ l)
    : a ≻* a | l.
  Proof.
    induction l; cbn in *;[contradiction|].
    destruct Hin. subst. econstructor. econstructor. eapply splinter_nil.
    econstructor. eauto.
  Qed.

  Hint Resolve succ_rt_refl : succ_rt.

  Lemma succ_rt_trans (a b c : A) l
        (Hnd : NoDup l)
        (Hsucc1 : b ≻* a | l)
        (Hsucc2 : c ≻* b | l)
    : c ≻* a | l.
  Proof.
    induction l; inversion Hsucc1; inversion Hsucc2; inversion Hnd; subst.
    - (* copy-copy *) eauto.
    - (* copy-skip -> contradiction *)
      exfalso. eapply H11. eapply splinter_incl;eauto. firstorder.
    - (* skip-copy *)
      econstructor. eapply splinter_incl in H2.
      eapply splinter_single;eauto. firstorder 1.
    - (* skip-skip *)
      econstructor;eauto.
  Qed.

  Lemma succ_rt_combine (a b c : A) l
        (Hnd : NoDup l)
        (Hsucc1 : b ≻* a | l)
        (Hsucc2 : c ≻* b | l)
    : c ≻* b ≻* a | l.
  Proof.
    splice_splinter;eauto.
  Qed.

  Ltac find_in_succ_rt := eapply splinter_incl; eauto; firstorder.
  
  Lemma postfix_succ_in (a b : A) l l'
        (Hpost : Postfix l l')
        (Hsucc : a ≻ b | l)
    : a ≻ b | l'.
  Proof.
    induction Hpost;eauto.
    eapply IHHpost in Hsucc.
    unfold succ_in in Hsucc. destructH. exists (l1 :r: a0), l2. rewrite Hsucc.
    rewrite <- cons_rcons_assoc. unfold rcons. rewrite <-app_assoc.
    rewrite app_comm_cons. reflexivity.
  Qed.
  
  Lemma succ_in_cons_cons (a b : A) l
    : a ≻ b | a :: b :: l.
  Proof.
    exists l, nil. cbn. reflexivity.
  Qed.
  
  Lemma succ_cons (a b c : A) l
        (Hsucc : b ≻ c | l)
    : b ≻ c | a :: l.
  Proof.
    revert a;destruct l;intros a0.
    - unfold succ_in in *;cbn in *;eauto. destructH. destruct l2;cbn in *;congruence.
    - unfold succ_in in Hsucc. destructH. unfold succ_in. exists l1, (a0 :: l2).  cbn.
      rewrite Hsucc. reflexivity.
  Qed.

  Lemma in_succ_in2 (a b c : A) l
        (Hsucc : a ≻ b | c :: l)
    : b ∈ l.
  Proof.
    unfold succ_in in Hsucc. destructH. 
    destruct l2;cbn in *; inversion Hsucc;subst; [|eapply in_or_app]; firstorder.
  Qed.

  Lemma in_succ_in1 (a b : A) l
        (Hsucc : a ≻ b | l)
    : a ∈ l.
  Proof.
    unfold succ_in in Hsucc. destructH.
    destruct l.
    - congruence'.
    - symmetry in Hsucc. eapply eq_incl in Hsucc. eapply Hsucc.
      clear Hsucc. induction l2;cbn;firstorder.
  Qed.

End succ_rt.

Ltac find_in_splinter :=
  match goal with
    [ H : context C [splinter ?b ?l] |- ?a ∈ ?l]
    => lazymatch b with
        context C' [a] => clear - H; eapply splinter_incl;eauto;firstorder
      end
  end.

Ltac find_succ_rel :=
  match goal with
  | [H : splinter ?l1 ?l |- ?a ≻* ?b | ?l]
    => match l1 with
      | context C [?a']
        => unify a a';
          match l1 with
          | context C [?b']
            => unify b b';
              eapply (splinter_trans _ l1);
              [|apply H]; solve [repeat (econstructor;eauto)]
          end
      end
  end.

Ltac resolve_succ_rt :=
  lazymatch goal with
  | [ Ha : context Ca [?a :: ?c :: _],
           Hb : context Cb [?b] |- ?a ≻* ?b | ?l ]
    => try find_succ_rel; eapply (succ_rt_trans _ c _);
      [eauto|find_succ_rel|find_succ_rel]
  | [ |- ?a ≻* ?b ≻* ?c | ?l ] => eapply succ_rt_combine;resolve_succ_rt
  end.


Goal forall (A : Type) (a b c d : A) (l : list A), NoDup l -> splinter (a :: b :: d :: nil) l
                                              -> splinter (d :: c :: a :: nil) l -> False.
  intros.  splice_splinter.
Abort.

Goal forall (A : Type) (a b c : A) (l : list A), NoDup (c :: l) -> a ≻* b | c :: l -> b ≻* c | c :: l -> False.
  intros. splice_splinter.
Abort.

  