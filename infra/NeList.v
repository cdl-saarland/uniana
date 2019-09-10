Require Import Lists.List.
Require Import Omega.
Require Import Coq.Program.Equality.
Import Decidable.
Require Import Coq.Classes.Morphisms Relation_Definitions.

Require Import Util PreSuffix.
Require Export DecTac.


Inductive ne_list (A : Type) : Type :=
| ne_single : A -> ne_list A
| ne_cons : A -> ne_list A -> ne_list A.

Arguments ne_single {_} _.
Arguments ne_cons {_} _ _.

Infix ":<:" := ne_cons (at level 70,right associativity).

Fixpoint ne_conc {A : Type} (l l' : ne_list A) : ne_list A :=
  match l with
  | ne_single a => a :<: l'
  | ne_cons a l => a :<: ne_conc l l'
  end.

Infix ":+:" := ne_conc (at level 50).

Definition ne_rcons {A : Type} l a : ne_list A := l :+: ne_single a.

Infix ":>:" := ne_rcons (at level 50).

Fixpoint ne_front {A : Type} (l : ne_list A) : A
  := match l with
     | ne_single a => a
     | ne_cons a _ => a
     end.

Fixpoint ne_back {A : Type} (l : ne_list A) : A
  := match l with
     | ne_single a => a
     | ne_cons _ l => ne_back l
     end.

Fixpoint ne_to_list {A : Type} (l : ne_list A) : list A
  := match l with
     | ne_single a => a :: nil
     | a :<: l => a :: ne_to_list l
     end.

Coercion ne_to_list : ne_list >-> list.

Fixpoint ne_tl {A : Type} (l : ne_list A) : list A
  := match l with
     | ne_single _ => nil
     | _ :<: l => l
     end.

Ltac prove_not_In H Q b :=
  (contradict H; inversion H; eauto; subst b; exfalso; apply Q; reflexivity).

Lemma ne_back_E_rcons {A : Type} `{EqDec A} (l : ne_list A) a
  : ne_back l = a -> exists l', l' :r: a = l.
Proof.
  intro Hback. induction l; cbn in *.
  - exists nil. subst a0. cbn. reflexivity.
  - apply IHl in Hback. destruct Hback as [ l' Hback]. exists (a0 :: l'). rewrite <-Hback.
    apply cons_rcons_assoc.
Qed.

Lemma ne_back_cons {A : Type} (l : ne_list A) a : ne_back (a :<: l) = ne_back l.
Proof.
  induction l; cbn; eauto.
Qed.

Lemma In_dec {A : Type} `{EqDec A eq} a (l : list A) : decidable (In a l).
Proof.
  unfold decidable.
  induction l.
  - right. tauto.
  - destruct IHl.
    + left; econstructor 2; eauto.
    + destruct (a == a0).
      * destruct e. left; econstructor. reflexivity.
      * right. contradict H0. inversion H0; eauto. subst a0. exfalso. apply c. reflexivity.
Qed.

Ltac split_conj :=
  lazymatch goal with
  | [ |- _ /\ _ ] => split; split_conj
  | [ |- _ <-> _ ] => split; split_conj
  | _ => idtac
  end.

Ltac enrich H :=
  (let h1 := fresh "post" in
   let h2 := fresh "post" in
   eapply postfix_rcons_nil_eq in H as [h1 h2];
   lazymatch type of h1 with
   | ?a = ?b => subst a
   end;
   lazymatch type of h2 with
   | ?a = ?b => subst a
   end).

Ltac prove_last_common' :=
  lazymatch goal with
  | [ |- Postfix ?l ?l] => econstructor
  | [ H : ?a === ?b |- Postfix (nil :r: ?c) (?d :: ?l)] => cbn; rewrite <-H; prove_last_common'
  | [ |- Postfix ?l ?l'] => eauto using postfix_cons, postfix_nil, cons_rcons_assoc
  | [ |- Disjoint ?l ?l'] => unfold Disjoint; firstorder
  | [ |- ~ False] => tauto
  | [ |- ~ In ?a nil] => eauto
  | [H : ~ In ?a ?l, Q : ?a =/= ?b |- ~ In ?a (?b :: ?l)] => prove_not_In H Q b
  | [H : ~ In ?a ?l, Q : ?b =/= ?a |- ~ In ?a (?b :: ?l)] => prove_not_In H Q b
  | [H : ~ In ?b ?l, Q : ?a =/= ?b |- ~ In ?a (?b :: ?l)] => prove_not_In H Q b
  | [H : ~ In ?b ?l, Q : ?b =/= ?a |- ~ In ?a (?b :: ?l)] => prove_not_In H Q b
  | [ |- _ ] => idtac
  end.

Ltac prove_last_common :=
  lazymatch goal with
  | [ H : Postfix (?l :r: ?a) (?b :: nil) |- _ ] => enrich H
  | [ H : Postfix ?a ?b |- _ ] => cbn in H
  | [ |- _ ] => idtac
  end; split_conj; prove_last_common'.


Ltac congruence' :=
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

Lemma rcons_eq (* unused *){A : Type} (a a' : A) l l' :
  a = a' /\ l = l' <-> l :r: a = l' :r: a'.
Proof.
  split.
  - destruct (rcons_destruct l); intros; destruct H0; subst; reflexivity.
  - intros. revert dependent l'.
    induction l; induction l'; intros Heq; inversion Heq.
    + split; reflexivity.
    + congruence'.
    + congruence'.
    + unfold rcons in IHl. specialize (IHl l' H1) as [aeq leq].
      split; subst; reflexivity.
Qed.  

Lemma postfix_first_occ_eq {A : Type} `{EqDec A eq} (l1 l2 l3 : list A) (a : A) :
  ~ In a l1 -> ~ In a l2 -> Postfix (l1 :r: a) l3 -> Postfix (l2 :r: a) l3
  -> l1 = l2.
Proof.
  intros in1 in2. intros.
  assert (Postfix l1 (l2 :r: a)) as po1.
  {
    eapply postfix_order; eauto.
    - cbn. apply In_rcons. left. reflexivity.
    - eapply postfix_step_left; eauto.
  }
  assert (Postfix l2 (l1 :r: a)) as po2.
  {
    eapply postfix_order; eauto.
    - cbn. apply In_rcons. left. reflexivity.
    - eapply postfix_step_left; eauto.
  }
  revert dependent l2.
  revert dependent l3. 
  induction l1; intros l3 post1 l2 in2 post2 po1 po2.
  - cbn in post1.
    apply postfix_incl in po2. clear - in2 po2.
    destruct l2; eauto. specialize (po2 a0).
    assert (In a0 (a :: nil)) as po' by (apply po2; econstructor; eauto).
    inversion po'.
    + subst a. exfalso. apply in2. econstructor; eauto.
    + inversion H.
  - destruct l2.
    + cbn in post2.
      apply postfix_incl in po1. clear - in1 po1.
      specialize (po1 a0).
      assert (In a0 (a :: nil)) as po' by (apply po1; econstructor; eauto).
      inversion po'.
      * subst a. exfalso. apply in1. econstructor; eauto.
      * inversion H.
    + rewrite cons_rcons_assoc in post1, post2.
      eapply postfix_hd_eq in po1 as hd_eq1. subst a0.
      assert (exists l3', l3 = a1 :: l3') as [l3' leq3].
      {
        destruct l3.
        - cbn in post2. eapply postfix_nil_nil in post2. cbn in post2. congruence.
        - exists l3. apply postfix_hd_eq in post1. subst a1. reflexivity.
      }
      subst l3.
      erewrite IHl1 with (l2:=l2); eauto.
      (* contradict in1. right. eauto.*)
      * eapply cons_postfix; eauto.
      (* contradict in2. right. eauto.*)
      * eapply cons_postfix; eauto.
      * rewrite cons_rcons_assoc in po1. eapply cons_postfix; eauto.
      * rewrite cons_rcons_assoc in po1. eapply cons_postfix; eauto.
Qed.


Definition last_common {A : Type} `{EqDec A eq} (l1 l2 : list A) (s : A) :=
  exists l1' l2', Postfix (l1' :r: s) l1 /\ Postfix (l2' :r: s) l2
             /\ Disjoint l1' l2'
             /\ ~ In s l1' /\ ~ In s l2'.

Lemma ne_last_common {A : Type} `{EqDec A eq} (l1 l2 : ne_list A) :
  ne_back l1 = ne_back l2
  -> exists s, last_common l1 l2 s.
Proof.
  unfold last_common.
  revert l2.
  induction l1; intros l2 beq; induction l2; cbn in *.
  - subst a0. exists a; exists nil; exists nil; cbn.
    prove_last_common.
  - exists a. exists nil. specialize (IHl2 beq).
    destruct IHl2 as [s [l1' [l2' [post [post' [disj [in1 in2]]]]]]]. cbn.
    destruct (a == a0). 
    + destruct e. exists nil. prove_last_common.
    + exists (a0 :: l2'). prove_last_common.
  - exists a0. specialize (IHl1 (ne_single a0) beq).
    destruct IHl1 as [s [l1' [l2' [post [post' [disj [in1 in2]]]]]]].
    destruct (a == a0).
    + destruct e. exists nil. exists nil. prove_last_common.
    + exists ((a :: l1')). exists nil. cbn in post'. prove_last_common.
  - specialize (IHl2 beq).
    erewrite <-ne_back_cons with (l:=l2) in beq.
    specialize (IHl1 (a0 :<: l2) beq).
    
    destruct IHl1 as [s1 [l11 [l12 [post11 [post12 [disj1 [in11 in12]]]]]]].
    destruct IHl2 as [s2 [l21 [l22 [post21 [post22 [disj2 [in21 in22]]]]]]].

    destruct (s1 == a0). 
    + destruct e. exists s1. destruct (a == s1).
      * destruct e. exists nil. exists nil. prove_last_common.
      * exists ((a :: l11)). exists nil. prove_last_common.
    + destruct (s2 == a).
      * destruct e. exists s2, nil. destruct (s2 == a0).
        -- destruct e. exists nil. prove_last_common.
        -- exists ((a0 :: l22)). prove_last_common.
      * destruct (a == a0).
        -- destruct e. exists a, nil, nil. prove_last_common.
        -- destruct (In_dec s1 l22).
           ++ exists s1, (a :: l11), l12.
              split_conj.
              ** prove_last_common.
              ** prove_last_common.
              ** apply disjoint_cons1. split; eauto. 
                 assert (Postfix l12 (a0 :: l22)).
                 {
                   eapply postfix_order with (a1:=s1); eauto.
                   (*- econstructor 2; eauto.*)
                   - eapply postfix_step_left; eauto.
                   - cbn. apply postfix_cons. eapply postfix_step_left; eauto.
                 }
                 apply postfix_incl in H1. apply id in disj2 as disj2'.
                 destruct disj2' as [disj2' _].
                 unfold incl in H1. intro In12. apply H1 in In12. cbn in In12.
                 destruct In12 as [In12|In12]; [subst a; apply c1; reflexivity|].
                 destruct disj2 as [_ disj2]. specialize (disj2 _ In12).
                 apply disj2. apply postfix_elem in post21; eauto.
                 --- eapply In_rcons in post21.
                     destruct post21; [subst a; exfalso; apply c0; reflexivity|assumption].
                 --- destruct l21; cbn. omega. rewrite app_length. omega.
                     
              ** assert (s1 =/= a) as sa.
                 {
                   intro N. destruct N. apply postfix_elem in post21.
                   apply In_rcons in post21.
                   - destruct post21; [subst s1; apply c0; reflexivity|].
                     clear - disj2 H0 H1. firstorder.
                   - destruct l21; cbn. omega. rewrite app_length. omega.
                 }                     
                 prove_last_common.
              ** assumption.
           ++ destruct (s1 == s2) as [seq|sneq].
              {
                destruct seq.
                assert (l21 = a :: l11 /\ l12 = a0 :: l22) as [lleq1 lleq2].
                {
                  split.
                  - eapply postfix_first_occ_eq; eauto.
                    + contradict in11. inversion in11.
                      * subst a; exfalso; apply c0; reflexivity.
                      * eauto.
                    + rewrite cons_rcons_assoc. apply postfix_cons. eauto.
                  - eapply postfix_first_occ_eq; eauto.
                    + contradict in22. inversion in22.
                      * subst a0; exfalso; apply c; reflexivity.
                      * eauto.
                    + rewrite cons_rcons_assoc. apply postfix_cons. eauto.
                }
                subst l12 l21.
                exists s1, (a :: l11), (a0 :: l22).
                split_conj.
                - prove_last_common.
                - prove_last_common.
                - eapply disjoint_cons1. split; eauto. destruct (disj2) as [disj2' _].
                  cbn in disj2'. specialize (disj2' _ (or_introl eq_refl)).
                  contradict disj2'. cbn in disj2'.
                  destruct disj2'; [subst a0; exfalso; apply c1; reflexivity|eauto].
                - eauto.
                - eauto.
              }
              destruct (In_dec a0 (l21 :r: s2)) as [in_a0|nin_a0].
              {
                exists a0, (postfix_nincl a0 l21), nil.
                split_conj.
                - 
                  apply In_rcons in in_a0. destruct in_a0.
                  + subst a0.
                    apply postfix_nincl_invariant in in21. rewrite in21. eauto.
                  + eapply postfix_nincl_spec in H1.
                    eapply postfix_trans; eauto. eapply postfix_step_left; eauto.
                - prove_last_common.
                - prove_last_common.
                - apply postfix_nincl_nincl.
                - tauto.
              }
              exists s2, l21, (a0 :: l22).
              assert (In s2 l12) as Hin11.
              {
                assert (~ In s1 (a0 :: l22 :r: s2)).
                { contradict H0. inversion H0;eauto. subst. exfalso; apply c; reflexivity.
                  apply In_rcons in H1.
                  destruct H1; [subst s1; exfalso; apply sneq; reflexivity|eauto].
                }
                eapply postfix_order with (l':=a0 :: l2) (l4:=l12 :r: s1) in H1; eauto.
                - apply postfix_incl in H1.
                  clear - sneq H1.
                  specialize (H1 s2). apply In_rcons in H1.
                  * destruct H1;[subst s2; exfalso; apply sneq; reflexivity|eauto].
                  * rewrite <-cons_rcons_assoc. apply In_rcons. left. reflexivity.
                - apply In_rcons. left. reflexivity.
                - apply postfix_cons; eauto.
              } 
              split_conj.
              ** prove_last_common.
              ** prove_last_common.
              ** apply disjoint_cons2. split; eauto.
                 contradict nin_a0. apply In_rcons. right. eauto.
              ** assumption.
              ** assert (s2 =/= a0) as sa.
                 {                       
                   intro N. destruct N. apply nin_a0.
                   apply In_rcons. left. reflexivity.
                 }
                 prove_last_common.
Qed.

Lemma last_common_sym {A : Type} `{EqDec A eq} (l l' : list A) a
      (Hlc : last_common l l' a)
  : last_common l' l a.
Proof.
  unfold last_common in *; firstorder.
Qed.

Fixpoint nlcons {A : Type} (a : A) l :=
  match l with
  | nil => ne_single a
  | b :: l => a :<: (nlcons b l)
  end.

Infix ":<" := nlcons (at level 50).

Definition nl_conc {A : Type} (l : ne_list A) (ll : list A) : ne_list A :=
  match ll with
  | nil => l
  | a :: ll => l :+: (a :< ll)
  end.

Infix ":+" := nl_conc (at level 50).

Lemma nlcons_to_list {A : Type} (a : A) l :
  a :: l = nlcons a l.
Proof.
  revert a. induction l; cbn; eauto. rewrite IHl. reflexivity.
Qed.

Lemma nlconc_to_list (A : Type) (l : ne_list A) (l' : list A)
  : l ++ l' = l :+ l'.
Proof.
  destruct l';cbn.
  - eauto using app_nil_end.
  - induction l;cbn;[rewrite <-nlcons_to_list|];eauto.
    rewrite IHl. reflexivity.
Qed.

Lemma nlcons_front {A : Type} (a : A) l :
  ne_front (nlcons a l) = a.
Proof.
  induction l; cbn; eauto.
Qed.    

Lemma nlcons_necons {A : Type} l :
  forall (a : A), (a :<: l) = nlcons a l.
Proof.
  induction l; cbn; eauto. rewrite IHl. reflexivity.
Qed.

Lemma nlconc_neconc {A : Type} (l : ne_list A) l' :
  (l :+: l') = l :+ l'.
Proof.
  intros. destruct l';cbn;eauto. rewrite nlcons_necons. reflexivity.
Qed.

Fixpoint ne_map {A B : Type} (f : A -> B) (l : ne_list A) : ne_list B :=
  match l with
  | ne_single a => ne_single (f a)
  | a :<: l => (f a) :<: ne_map f l
  end.

Lemma ne_map_nlcons {A B : Type} (f : A -> B) (a : A) l :
  ne_map f (nlcons a l) = nlcons (f a) (map f l).
Proof.
  revert a. induction l;intros b;cbn;firstorder.
  f_equal. eauto.
Qed.

Fixpoint nl_rcons {A : Type} l (a : A) : ne_list A :=
  match l with
  | nil =>  ne_single a
  | b :: l => (b :<: (nl_rcons l a))
  end.

Infix ">:" := nl_rcons (at level 50).

Lemma nl_rcons_back {A : Type} (a : A) l :
  ne_back (l >: a) = a.
Proof.
  induction l; cbn; eauto.
Qed.

Lemma ne_rcons_back (* unused *){A : Type} (a : A) l :
  ne_back (l :>: a) = a.
Proof.
  induction l; cbn; eauto.
Qed.

Lemma postfix_map (* unused *){A B : Type} (f : A -> B) :
  forall l l', Postfix l l' -> Postfix (map f l) (map f l').
Proof.
  intros ? ? Hpost.
  induction Hpost;[econstructor|rewrite map_rcons;econstructor;assumption].
Qed.

Lemma to_list_ne_map {A B : Type} (f : A -> B) (l : ne_list A) :
  map f l = ne_map f l.
Proof.
  intros. induction l;cbn;eauto. rewrite IHl. reflexivity.
Qed.

Lemma ne_back_map {A B : Type} (f : A -> B) l :
  ne_back (ne_map f l) = f (ne_back l).
Proof.
  induction l; firstorder.
Qed.

Lemma ne_to_list_inj {A : Type} (l l' : ne_list A) :
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


Lemma ne_map_in {A B : Type} (f:A->B) a (l:ne_list A) :
  In a l -> In (f a) (ne_map f l).
Proof.
  intro Hin. induction l;cbn.
  - inversion Hin;[subst;tauto|contradiction].
  - cbn in Hin. destruct Hin;subst.
    + left. reflexivity.
    + right. eauto.
Qed.

Lemma ne_map_nl_rcons (* unused *){A B : Type} (l : list A) a (f : A -> B)
  : ne_map f (l >: a) = (map f l) >: (f a).
Proof.
  induction l;cbn;eauto. rewrite IHl. reflexivity.
Qed.

Lemma disjoint_subset {A : Type} (l1 l1' l2 l2' : list A)
  : l1 ⊆ l1' -> l2 ⊆ l2' -> Disjoint l1' l2' -> Disjoint l1 l2.
Proof.
  intros Hsub1 Hsub2 Hdisj.
  unfold Disjoint in *. destructH. split;firstorder.
Qed.

Lemma rcons_nl_rcons {A : Type} l (a:A) :
  l :r: a = nl_rcons l a.
Proof.
  induction l; eauto. rewrite cons_rcons_assoc. rewrite IHl. cbn. reflexivity.
Qed.

Lemma ne_to_list_not_nil {A:Type} (l : ne_list A) :
  nil <> l.
Proof.
  intro N. induction l; cbn in *; congruence.
Qed.

Lemma nercons_nlrcons (* unused *){A : Type} l (a : A)
  : l :>: a = l >: a.
Proof.
  induction l;cbn;eauto. rewrite <-IHl. destruct l;eauto.
Qed.

Lemma rcons_necons (A : Type) l (a : A)
  : (ne_to_list l) :r: a = l :>: a.
Proof.
  induction l;cbn;eauto. unfold rcons in IHl. rewrite IHl. reflexivity.
Qed.

Ltac simpl_nl :=
  repeat lazymatch goal with
         | [ |- ne_to_list _ = ne_to_list _] => f_equal
         | [ |- context[ne_front (nlcons ?a ?l)]] => rewrite nlcons_front
         | [ |- context[ne_back (?l >: ?a)]] => rewrite nl_rcons_back
         | [ |- context[ne_back (?l :>: ?a)]] => rewrite ne_rcons_back
         | [ |- context[(_ :< ne_to_list _)]] => rewrite <-nlcons_necons
         | [ |- context[(ne_to_list _ >: _)]] => rewrite <-nercons_nlrcons
         | [ |- context[ne_to_list (_ :< _)]] => rewrite <-nlcons_to_list
         | [ |- context[ne_to_list (_ >: _)]] => rewrite <-rcons_nl_rcons
         | [ |- context[ne_map ?f (_ :< _)]] => rewrite ne_map_nlcons
         | [ |- context[ne_to_list (_ :>: _)]] => rewrite <-rcons_necons
         end.

Goal forall (A:Type) (a : A) (l :ne_list A) , ne_to_list l = ne_to_list l. intros. simpl_nl. Qed.
Set Printing Coercions.

Ltac simpl_nl' H := 
  repeat lazymatch type of H with
         | ne_to_list _ = ne_to_list _ => eapply ne_to_list_inj in H
         | ne_to_list ?l = ?a :: nil => rewrite nlcons_to_list in H; apply ne_to_list_inj in H
         | ?a :: nil = ne_to_list ?l => rewrite nlcons_to_list in H; apply ne_to_list_inj in H
         | ne_to_list ?l = nil => symmetry in H; apply ne_to_list_not_nil in H
         | nil = ne_to_list ?l => apply ne_to_list_not_nil in H
         | context[ne_front (nlcons ?a ?l)] => rewrite nlcons_front in H
         | context[ne_back (?l >: ?a)] => rewrite nl_rcons_back in H
         | context[ne_back (?l :>: ?a)] => rewrite ne_rcons_back in H
         | context[(_ :< ne_to_list _)] => rewrite <-nlcons_necons in H
         | context[(ne_to_list _ >:  _)] => rewrite <-nercons_nlrcons in H
         | context[ne_to_list (nlcons _ _)] => rewrite <-nlcons_to_list in H
         | context[ne_to_list (nl_rcons _ _)] => rewrite <-rcons_nl_rcons in H
         | context[ne_map ?f (_ :< _)] => rewrite ne_map_nlcons in H
         | context[ne_to_list (_ :>: _)] => rewrite <-rcons_necons in H
         end.

Ltac cbn_nl :=
  repeat (cbn; simpl_nl).

Ltac cbn_nl' H :=
  repeat (cbn in H; simpl_nl' H).

Lemma prefix_nlcons: forall (A : Type) (l l' : list A) (a : A),
    Prefix (a :< l) l' -> Prefix l l'.
Proof.
  destruct l;[intros;eapply prefix_nil|
              cbn;intros;eapply prefix_cons;setoid_rewrite nlcons_to_list at 2;eauto].
Qed.



Lemma last_common_singleton1 (* unused *){A : Type} `{EqDec A eq} (s a : A) l
      (Hlc : last_common (a :: nil) l s)
  : a = s.
Proof.
  unfold last_common in Hlc. destructH. eapply postfix_rcons_nil_eq in Hlc0. firstorder.
Qed.

Lemma last_common_singleton2 (* unused *){A : Type} `{EqDec A eq} (s a : A) l
      (Hlc : last_common l (a :: nil) s)
  : a = s.
Proof.
  unfold last_common in Hlc. destructH. eapply postfix_rcons_nil_eq in Hlc2. firstorder.
Qed.

Lemma ne_list_nlcons (* unused *)(A : Type) (l : ne_list A)
  : exists a l', l = a :< l'.
Proof.
  destruct l as [a | a l'];exists a;[exists nil|exists l'];cbn;simpl_nl;reflexivity.
Qed.



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


Lemma prefix_eq:
  forall (A : Type) (l1 l2 : list A), Prefix l1 l2 <-> (exists l2' : list A, l2 = l2' ++ l1).
Proof.
  intros.
  split;intros.
  - induction H.
    + exists nil; cbn; eauto.
    + destructH. exists (a :: l2'). cbn. f_equal;eauto.
  - destructH. rewrite H.
    revert dependent l2.
    induction l2'; intros;cbn;econstructor;eauto.
Qed.

Lemma prefix_length {A : Type} `{EqDec A eq} (l1 l2 : list A)
      (Hpre : Prefix l1 l2)
      (Hlen : length l1 = length l2)
  : l1 = l2.
Proof.
  eapply prefix_eq in Hpre. destructH. subst l2.
  destruct l2';cbn in *; eauto.
  exfalso.
  rewrite app_length in Hlen. omega.
Qed.

Lemma prefix_rev_postfix (A : Type) (l l' : list A)
      (Hpre : Prefix l l')
  : Postfix (rev l) (rev l').
Proof.
  induction Hpre.
  - econstructor.
  - rewrite rev_cons. econstructor;eauto.
Qed.

Lemma prefix_rev_postfix' (A : Type) (l l' : list A)
      (Hpre : Prefix (rev l) (rev l'))
  : Postfix l l'.
Proof.
  rewrite <-(rev_involutive l).
  rewrite <-(rev_involutive l').
  eapply prefix_rev_postfix;eauto.
Qed.
  
Lemma postfix_rev_prefix (A : Type) (l l' : list A)
      (Hpost : Postfix l l')
  : Prefix (rev l) (rev l').
Proof.
  induction Hpost.
  - econstructor.
  - rewrite rev_rcons. econstructor;eauto.
Qed.
  
Lemma postfix_rev_prefix' (A : Type) (l l' : list A)
      (Hpost : Postfix (rev l) (rev l'))
  : Prefix l l'.
Proof.
  rewrite <-(rev_involutive l).
  rewrite <-(rev_involutive l').
  eapply postfix_rev_prefix;eauto.
Qed.

Lemma prefix_order_destruct (A : Type)
  : forall l3 l4 l5 : list A, Prefix l3 l5 -> Prefix l4 l5 -> Prefix l3 l4 \/ Prefix l4 l3.
Proof.
  intros.
  eapply prefix_rev_postfix in H. eapply prefix_rev_postfix in H0.
  eapply postfix_order_destruct in H;eauto.
  destruct H;[right|left]; eapply postfix_rev_prefix';eauto.
Qed.

Lemma prefix_length_eq (* unused *){A : Type} `{EqDec A eq} (l1 l2 l : list A)
      (Hlen : length l1 = length l2)
      (Hpre1 : Prefix l1 l)
      (Hpre2 : Prefix l2 l)
  : l1 = l2.
Proof.
  eapply prefix_order_destruct in Hpre1 as Hor;eauto.
  destruct Hor as [Hor|Hor]; eapply prefix_length in Hor; eauto; symmetry; eauto.
Qed.

Lemma first_diff' {A : Type} `{EqDec A eq} (l1 l2 : list A)
      (Hneq : l1 <> l2)
      (Hlen : length l1 = length l2)
      (Hnnil1 : l1 <> nil)
      (Hnnil2 : l2 <> nil)
  : exists a1 a2 l' l1' l2', a1 <> a2 /\ l1 = l' ++ a1 :: l1' /\ l2 = l' ++ a2 :: l2'.
Proof.
  assert (forall (l : list A), l <> nil -> length l > 0) as Hlengt.
  { clear. intros. destruct l;cbn;[congruence|omega]. }
  eapply Hlengt in Hnnil1; eapply Hlengt in Hnnil2. clear Hlengt.
  revert dependent l2. induction l1; intros; destruct l2; cbn in *.
  1: congruence. 1-2: omega.
  destruct l1,l2; cbn in *; only 2,3: congruence.
  - exists a, a0, nil, nil, nil. split_conj; cbn; eauto. contradict Hneq. subst; eauto.
  - decide' (a == a0).
    + exploit' IHl1;[omega|]. specialize (IHl1 (a2 :: l2)). exploit IHl1.
      * contradict Hneq. f_equal;eauto.
      * cbn; omega.
      * destructH. exists a0, a3, (a :: l'), l1', l2'. split_conj; eauto.
        1,2: cbn; f_equal; eauto.
    + exists a, a0, nil, (a1 :: l1), (a2 :: l2). split_conj; eauto.
Qed.

Ltac fold_rcons H :=
  match type of H with
  | context C [?a :: ?b :: nil] => fold (app (a :: nil) (b :: nil)) in H;
                                  fold (rcons (a :: nil) b) in H;
                                  repeat rewrite <-cons_rcons_assoc in H
  | context C [?l ++ ?a :: nil] => fold (rcons l a) in H
  end.


Lemma rcons_eq1 {A : Type} (l l' : list A) (a a' : A)
  : l :r: a = l' :r: a' -> l = l'.
Proof.
  revert l'; induction l; intros; destruct l'; cbn in *; inversion H; eauto; try congruence'.
  f_equal. eapply IHl. repeat fold_rcons H2. auto.
Qed.
Lemma rcons_eq2 {A : Type} (l l' : list A) (a a' : A)
  : l :r: a = l' :r: a' -> a = a'.
Proof.
  revert l'; induction l; intros; destruct l'; cbn in *; inversion H; eauto; congruence'.
Qed.
    
Lemma rev_injective {A : Type} (l l' : list A)
  : rev l = rev l' -> l = l'.
Proof.
  revert l. induction l'; intros; cbn in *.
  - destruct l;[reflexivity|cbn in *;congruence'].
  - destruct l;cbn in *;[congruence'|].
    repeat fold_rcons H. 
    f_equal;[eapply rcons_eq2;eauto|apply IHl';eapply rcons_eq1;eauto].
Qed.

Lemma first_diff (* unused *){A : Type} `{EqDec A eq} (l1 l2 : list A)
      (Hneq : l1 <> l2)
      (Hlen : length l1 = length l2)
      (Hnnil1 : l1 <> nil)
      (Hnnil2 : l2 <> nil)
  : exists a1 a2 l' l1' l2', a1 <> a2 /\ l1 = l1' ++ a1 :: l' /\ l2 = l2' ++ a2 :: l'.
Proof.
  specialize (@first_diff' _ _ _ (rev l1) (rev l2)) as Hfi.
  exploit Hfi; cycle -1.
  - destructH.
    rewrite <-rev_involutive in Hfi2. eapply rev_injective in Hfi2.
    rewrite rev_app_distr in Hfi2. rewrite rev_cons in Hfi2.
    rewrite <-rev_involutive in Hfi3. eapply rev_injective in Hfi3.
    rewrite rev_app_distr in Hfi3. rewrite rev_cons in Hfi3.
    exists a1, a2, (rev l'), (rev l1'), (rev l2').
    unfold rcons in Hfi2,Hfi3.
    rewrite <-app_assoc in Hfi2,Hfi3. cbn in *. firstorder.
  - contradict Hneq. eapply rev_injective; eauto.
  - rewrite !rev_length; eauto.
  - contradict Hnnil1. destruct l1;cbn in *;[auto|congruence'].
  - contradict Hnnil2. destruct l2;cbn in *;[auto|congruence'].
Qed.

(* TODO : tidy up this file *)
(*
Instance ne_list_eq_dec (A : Type) : eq_dec A -> eq_dec (ne_list A).
Proof.
  intros H l.
  induction l; intro l'; induction l'.
  - decide (a = a0); subst;[left|right];eauto. contradict n. inversion n;eauto.
  - right. intro N; inversion N.
  - right. intro N; inversion N.
  - decide (a = a0).
    + subst. destruct (IHl l').
      * subst. left. reflexivity.
      * right. intro N; inversion N. congruence.
    + right. intro N; inversion N. congruence.
Qed.
 *)

Lemma nin_tl_iff (A : Type) `{EqDec A eq} (a : A) (l : ne_list A)
  : a ∉ tl (rev l) -> a ∉ l \/ a = ne_back l.
Proof.
  intros.
  decide' (a == ne_back l);eauto.
  left. contradict H0. induction l;cbn in *;eauto.
  - destruct H0;eauto. congruence.
  - fold (rcons (rev l) a0).
    rewrite tl_rcons;[eapply In_rcons;eauto|destruct l;cbn;eauto;erewrite app_length;cbn;omega].
    destruct H0.
    + subst. eauto.
    + right. eapply IHl;eauto.
Qed.

Lemma tl_incl (A : Type) (l : list A)
  : tl l ⊆ l.
  induction l;cbn;firstorder.
Qed.

Lemma prefix_induction (* unused *){A : Type} {P : list A -> Prop}
  : P nil
    -> (forall (a : A) (l : list A) (l' : list A), P l' -> Prefix (a :: l') l -> P l)
    -> forall l : list A, P l.
Proof.
  intros Hbase Hstep l. induction l;eauto.
  eapply Hstep;eauto. econstructor.
Qed.



Lemma find_some' (* unused *)(A : Type) (f : A -> bool) (l : list A) (x : A)
      (Hl : x ∈ l)
      (Hf : f x = true)
  : exists y, Some y = find f l.
Proof.
  induction l;cbn;[contradiction|].
  destruct Hl;subst.
  - rewrite Hf. eauto.
  - destruct (f a);eauto.
Qed.
