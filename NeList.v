Require Import Coq.Classes.EquivDec.
Require Import Lists.List.

Require Import Coq.Classes.Morphisms Relation_Definitions.

Module NeList.

  Import EquivDec.
  
  Import Decidable.

  Inductive ne_list (A : Type) : Type :=
  | ne_single : A -> ne_list A
  | ne_cons : A -> ne_list A -> ne_list A.

  Arguments ne_single {_} _.
  Arguments ne_cons {_} _ _.
  
  Infix ":<:" := ne_cons (at level 70).

  Fixpoint ne_conc {A : Type} (l l' : ne_list A) : ne_list A :=
    match l with
    | ne_single a => a :<: l'
    | ne_cons a l => a :<: ne_conc l l'
    end.

  Infix ":+:" := ne_conc (at level 50).

  Definition ne_rcons {A : Type} l a : ne_list A := l :+: ne_single a.

  Infix ":>:" := ne_rcons (at level 50).
  
  Definition rcons {A : Type} l a : list A := l ++ (a :: nil).

  Notation "l ':r:' a" := (rcons l a) (at level 50).

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

  Fixpoint eq_list {A : Type} `{EqDec A} (l l' : list A) : Prop :=
    match l, l' with
    | nil, nil => True
    | a :: l, a'::l' => R a a' /\ eq_list l l'
    | _,_ => False
    end.
  
  Program Instance equiv_list {A : Type} `{EqDec A} : Equivalence eq_list.
  Next Obligation.
    unfold Reflexive.
    intros x. induction x; cbn; eauto.
    split. reflexivity. assumption.
  Qed.
  Next Obligation.
    unfold Symmetric.
    induction x; intros y Heq; induction y; inversion Heq.
    - assumption.
    - cbn. split.
      + symmetry. eauto.
      + apply IHx. assumption.
  Qed.
  Next Obligation.
    unfold Transitive.
    induction x; induction y; induction z; intros Hxy Hyz; cbn in *; eauto; try contradiction.
    split.
    - destruct Hxy as [Hxy _]. destruct Hyz as [Hyz _]. eapply transitivity; eauto.
    - firstorder.
  Qed.

  Program Instance proper_cons {A : Type} `{EqDec A}
    : Proper (R ==> eq_list ==> eq_list) cons.
  Next Obligation.
    unfold respectful.
    intros x y Rxy lx ly Hl. cbn. split; eauto.
  Qed.
          
  Inductive Prefix {A : Type} : list A -> list A -> Prop :=
  | PreSame l : Prefix l l
  | PreStep {a l l'} : Prefix l l' -> Prefix l (a :: l').
  
  Inductive Postfix {A : Type} `{EqDec A} : list A -> list A -> Prop :=
  | PostSame l l' : l === l' -> Postfix l l'
  | PostStep {a l l'} : Postfix l l' -> Postfix l (l' :r: a).
  
  Inductive neSub {A : Type} : ne_list A -> ne_list A -> Prop :=
  | SubSame l : neSub l l
  | SubPre {a l l'} : neSub l l' -> neSub l (a :<: l')
  | SubPost {a l l'} : neSub l l' -> neSub l (l' :>: a).

  Definition Disjoint {A : Type} (l l' : list A) : Prop :=
    forall a, (In a l -> ~ In a l')
         /\ (In a l' -> ~ In a l).

  Fixpoint postfix_nincl {A : Type} `{EqDec A} (a : A) (l : list A) : list A :=
    match l with
    | nil => nil
    | b :: l => if a == b then nil else b :: postfix_nincl a l
    end.

  Lemma postfix_nil {A : Type} `{EqDec A} (l : list A) : Postfix nil l.
    induction l; [econstructor|].
    admit.
  Admitted.
  
  Lemma postfix_cons {A : Type} `{EqDec A} a (l l': list A) :
    Postfix l l' -> Postfix (a :: l) (a :: l').
  Proof.
  Admitted.

  Lemma rev_cons {A : Type} (a : A) l : rev (a :: l) = (rev l) :r: a.
    induction l; cbn; eauto.
  Qed.

  Lemma cons_rcons_assoc {A : Type} (a b : A) l : (a :: l) :r: b = a :: (l :r: b).
    induction l; cbn; eauto.
  Qed.

  Lemma rev_rcons {A : Type} (a : A) l : rev (l :r: a) = a :: (rev l).
    induction l; cbn; eauto. unfold rcons in IHl. rewrite IHl; eauto using  cons_rcons_assoc.
  Qed.

  Require Import Omega.
  Lemma tl_rcons {A : Type} (a : A) l : length l > 0 -> tl (l :r: a) = tl l :r: a.
    induction l; intros; cbn in *; eauto. omega.
  Qed.

  Lemma hd_rcons {A : Type} (a x y : A) l : length l > 0 -> hd x (l :r: a) = hd y l.
    induction l; intros; cbn in *; eauto. omega.
  Qed.

  Lemma cons_rcons {A : Type} (a : A) l : exists a' l', (a :: l) = (l' :r: a').
  Proof.
    exists (hd a (rev (a :: l))). exists (rev (tl (rev (a :: l)))).
    revert a; induction l; intros b; [ cbn in *; eauto|].
    rewrite rev_cons. rewrite tl_rcons.
    - rewrite rev_rcons. erewrite hd_rcons.
      + rewrite cons_rcons_assoc. f_equal. apply IHl.
      + rewrite rev_length; cbn; omega.
    - rewrite rev_length; cbn; omega.
  Qed.

  Lemma rcons_cons {A : Type} (a : A) l : exists a' l', (l :r: a) = (a' :: l').
    Admitted.
    
  Program Instance proper_rcons {A : Type} `{EqDec A}
    : Proper (eq_list ==> R ==> eq_list) rcons.
  Next Obligation.
    unfold respectful.
    intros lx ly Rlxy x y Rxy. revert dependent x. revert dependent y. revert dependent ly.
    induction lx; induction ly; intros Rlxy y x Rxy; firstorder.
  Qed.     

  Program Instance postfix_proper {A : Type} `{EqDec A}
    : Proper (eq_list ==> eq_list ==> iff) Postfix.
  Next Obligation.
    unfold respectful.
    intros x y Heq x' y' Heq'. split; intros impl.
    - revert dependent x'. revert dependent y'.
      induction x; intros y' x' Heq' impl; inversion_clear impl.
      + econstructor. rewrite <-Heq, <-Heq'. assumption.
      + induction y'.
        * econstructor. rewrite Heq. reflexivity.
        * admit.
      + rewrite Heq in H0. rewrite Heq' in H0. econstructor; eauto.
      + eapply IHx; eauto. admit. admit.
        
      Admit Obligations.

  Lemma postfix_dec {A : Type} `{EqDec A} (l l' : list A) : decidable (Postfix l l').
  Proof.
    unfold decidable. revert l'.
    induction l.
    - left. apply postfix_nil.
    - induction l'.
      + right. intro N. inversion N. inversion H0. admit. (*easy*)
      + specialize (IHl (a :: l)). destruct IHl. 
        * destruct (a == a0).
          -- left. setoid_rewrite <-e. apply postfix_cons. admit.
          -- admit.
        * admit.
  Admitted.

  Lemma postfix_nincl_postfix {A : Type} `{EqDec A} a l : Postfix (postfix_nincl a l) l.
  Proof.
    induction l; cbn; [econstructor; reflexivity|].
    destruct (a == a0); cbn; eauto using postfix_nil, postfix_cons.
  Qed.

  Lemma postfix_rcons_nil_eq {A : Type} `{EqDec A} l (a b : A) :
    Postfix (l :r: a) (b :: nil) -> a = b /\ l = nil.
  Admitted.

  Ltac prove_not_In H Q b :=
    (contradict H; inversion H; eauto; subst b; exfalso; apply Q; reflexivity).

  Ltac prove_last_common :=
    lazymatch goal with
    | [ |- ?H /\ ?Q] => split; prove_last_common
    | [ |- Postfix ?l ?l] => econstructor; reflexivity
    | [ H : ?a === ?b |- Postfix (nil :r: ?c) (?d :: ?l)] => cbn; rewrite <-H; prove_last_common
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
      
  Lemma ne_last_common {A : Type} `{EqDec A} (l1 l2 : ne_list A) :
    ne_back l1 = ne_back l2
    -> exists s l1' l2', Postfix (l1' :r: s) l1 /\ Postfix (l2' :r: s) l2
                   /\ Disjoint l1' l2'
                   /\ ~ In s l1' /\ ~ In s l2'.
  Proof.
    revert l2.
    induction l1; intros l2 beq; induction l2; cbn in *.
    - subst a0. exists a; exists nil; exists nil; cbn.
      prove_last_common.
(*      split. ; [econstructor; reflexivity | split]; [econstructor;reflexivity|]. firstorder.*)
    - exists a. exists nil. specialize (IHl2 beq).
      destruct IHl2 as [s [l1' [l2' [post [post' [disj [in1 in2]]]]]]]. cbn.
      destruct (a == a0).
      + exists nil. prove_last_common.
      + exists (a0 :: l2'). 
        eapply postfix_rcons_nil_eq in post as [post1 post2]. subst s.
        prove_last_common.
        
(*      split; [econstructor;reflexivity| split]; [| split;[|split]].
      + eauto using postfix_cons. 
      + unfold Disjoint. firstorder.
      + tauto.
      + intro N. destruct disj as [_ [_ disj]]. apply disj. inversion N; eauto.*)
        
    - exists a0. specialize (IHl1 (ne_single a0) beq).
      destruct IHl1 as [s [l1' [l2' [post [post' [disj [in1 in2]]]]]]].
      destruct (a == a0).
      + exists nil. exists nil. prove_last_common.
      + exists ((a :: l1')). exists nil.
        eapply postfix_rcons_nil_eq in post' as [post'1 post'2]. subst s. eauto using postfix_cons.
        prove_last_common.
    - specialize (IHl2 beq).
      erewrite <-ne_back_cons with (l:=l2) in beq.
      specialize (IHl1 (a0 :<: l2) beq).
        
      destruct IHl1 as [s1 [l11 [l12 [post11 [post12 [disj1 [in11 in12]]]]]]].
      destruct IHl2 as [s2 [l21 [l22 [post21 [post22 [disj2 [in21 in22]]]]]]].

      destruct (s1 == a0).
      + exists a0. destruct (a == a0).
        * exists nil. exists nil. prove_last_common.
        * exists ((a :: l11)). exists nil. prove_last_common.
          -- rewrite cons_rcons_assoc. apply postfix_cons. 
             change (l11 :r: a0) with (rcons l11 a0). rewrite <-e. assumption.
          -- contradict in11. inversion in11. subst a. exfalso; apply Q; reflexivity).
             
          eapply postfix_rcons_nil_eq in post as [post'1 post'2]. subst s. eauto using postfix_cons.
          prove_last_common.
          prove_last_common.
      assert (s1 =/= a0 -> In s1 l22) by admit.
      assert (s2 =/= a  -> In s2 l11) by admit.
      assert (s1 === a0 -> 
        
      exists s; exists (a :: l1'). ; exists (l2'); split; [|split]; eauto.
      * rewrite cons_rcons_assoc. apply postfix_cons; eauto.
      * 
        specialize (cons_rcons a0 l2) as CR.
        destruct CR as [a' [l' CR]]. rewrite CR. econstructor 2. rewrite <-CR.
       



      destruct (a == a0).
      + exists a; exists nil; exists nil. cbn.
        split; [eauto using postfix_cons, postfix_nil|split]; [|unfold Disjoint; firstorder].
        rewrite e.
        apply postfix_cons, postfix_nil.
      + 
        

End NeList.