Require Export ListExtra PreSuffix ListOrder.

Definition Tag := list nat.
  
Inductive Tagle' : Tag -> Tag -> Prop :=
| TgApp' (i j : Tag) : Tagle' j (i ++ j)
| TgLt' (n m : nat) (i j : Tag) : n < m -> Tagle' (i :r: n) (j :r: m).

Inductive Tagle : Tag -> Tag -> Prop :=
| TgEq (i : Tag) : Tagle i i
| TgCons (n : nat) (i j : Tag) : Tagle i j -> Tagle i (n :: j)
| TgLt (n m : nat) (i j : Tag) : |i| = |j| -> n < m -> Tagle (i :r: n) (j :r: m).

(*Definition Tagle (i j : Tag) := exists j', Prefix j' j /\ Tagle' i j'.*)


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

  (* the tags have to be reversed bc. the head is least significant *)
  Definition tagle (i j : Tag) := tagle' (rev i) (rev j).

Infix "⊴" := tagle (at level 70).


(*
Global Instance Tagle'_PreOrder : PreOrder Tagle'.
Proof.
  econstructor.
  - unfold Reflexive. intros x. induction x;econstructor;eauto.
  - unfold Transitive. intros x y z Hxy. revert z.
    induction Hxy;intros z Hyz;eauto.
    destruct z.
    + inversion Hyz.
    + decide (n <= n0).
      * econstructor;eauto. eapply IHHxy.
        inversion Hyz;subst. auto.
      * inversion Hyz;subst. omega.
Qed.

Global Instance Tagle_PreOrder : PreOrder Tagle.
Proof.
  econstructor.
  - unfold Reflexive. intros. exists x. split;[econstructor|].
    eapply Tagle'_PreOrder.
  - unfold Transitive. intros x y z Hxy Hyz.
    unfold Tagle in *. destructH. destructH.
    
  *)  

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
