Require Import Program.Equality.
Require Export ListExtra PreSuffix ListOrder.

Definition Tag := list nat.
  
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
  unfold rcons. eapply app_assoc.
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
  - eapply rcons_eq2 in x0. eapply rcons_eq2 in x. subst. omega.
Qed.
    
Hint Constructors Tagle : tagle.
Hint Immediate Tagle_app : tagle.

Ltac destr_r' l :=
  let H := fresh "Hl" in
  let x := fresh "x" in
  let l' := fresh "l" in
  let Hlx := fresh "Hx" in
  specialize (rcons_destruct l) as H;
  destruct H as [H|[x [l' Hlx]]].

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
        -- econstructor;auto. omega.
        -- subst. econstructor. auto.
Qed.

  (** tagging order **)

  Fixpoint tagle' (i j : Tag)
    := match i,j with
       | nil,_ => True
       | _ :: _, nil => False
       | n :: i, m :: j => if decision (n < m)
                        then True
                        else if decision (n = m)
                             then tagle' i j
                             else False
       end.
  
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
        * exfalso. eapply rcons_eq2 in H. eapply rcons_eq2 in H2. subst. omega.
      + inversion H1;[congruence' | |].
        * exfalso. eapply rcons_eq2 in H0. eapply rcons_eq2 in H2. subst. omega.
        * exfalso. eapply rcons_eq2 in H0. eapply rcons_eq2 in H2. subst. omega.
  Qed.
(*      
      

  (* the tags have to be reversed bc. the head is least significant *)
  Definition tagle (i j : Tag) := tagle' (rev i) (rev j).


  Global Instance tagle'_PreOrder : PreOrder tagle'.
  econstructor.
  - unfold Reflexive. intros x. induction x;cbn;auto.
    decide (a < a);[omega|].
    decide (a = a);[auto|omega].
  - intros x. induction x; intros y z Hxy Hyz;cbn in *;auto.
    destruct y;[contradiction|];cbn in *.
    destruct z;[contradiction|];cbn in *.
    decide (a < n0);[auto|].
    decide (a < n); decide (n < n0).
    + exfalso. omega.
    + exfalso. assert (n0 < n) by omega. decide (n = n0);[omega|contradiction].
    + exfalso. assert (n < a) by omega. decide (a = n);[omega|contradiction].
    + decide (a = n); decide (n = n0). 2-4: contradiction.
      subst a. decide (n = n0);[|contradiction].
      eapply IHx;eauto.
  Qed.

  Global Instance tagle'_PartialOrder : PartialOrder eq tagle'.
  econstructor;intros.
  - subst. econstructor. 2: unfold Basics.flip. all: eapply tagle'_PreOrder.
  - inversion H. clear H. unfold Basics.flip in H1.
    revert dependent x. induction x0;intros;cbn in *.
    + destruct x; cbn in *;[auto|contradiction].
    + destruct x; cbn in *;[contradiction|].
      decide (n = a).
      * decide (a = n);[|omega]. decide (n < a); decide (a < n). 1-3:omega. subst.
        f_equal. eapply IHx0;eauto.
      * decide (n < a);[|contradiction].
        decide (a < n);[omega|].
        decide (a = n);[omega|contradiction].
  Qed.

  Global Instance tagle_Preorder : PreOrder tagle.
  econstructor.
  - unfold Reflexive. intros x. unfold tagle. eapply tagle'_PreOrder.
  - unfold Transitive, tagle. intros. eapply tagle'_PreOrder;eauto.
  Qed.

  Global Instance tagle_PartialOrder : PartialOrder eq tagle.
  econstructor;intros.
  - subst. econstructor. 2: unfold Basics.flip. all: eapply tagle'_PreOrder.
  - inversion H. unfold tagle,Basics.flip in *.
    eapply rev_rev_eq.
    apply (partial_order_antisym tagle'_PartialOrder (rev x) (rev x0));eauto.
  Qed.
 *)
