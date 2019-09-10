Require Import Program.Equality.

Require Export ListExtra.

Notation "x ⊆ y" := (incl x y) (at level 50).

Inductive Prefix {A : Type} : list A -> list A -> Prop :=
| PreSame l : Prefix l l
| PreStep {a l l'} : Prefix l l' -> Prefix l (a :: l').

Lemma prefix_cons_in {A : Type} `{EqDec A eq} (a : A) l l' : Prefix (a :: l) l' -> In a l'.
Proof.
  intro Q. revert dependent l. induction l'; cbn in *; intros l Q.
  - inversion Q.
  - destruct (a == a0).
    + auto.
    + inversion Q; subst.
      * exfalso; apply c; reflexivity.
      * eauto.
Qed.

Inductive Postfix {A : Type} : list A -> list A -> Prop :=
| PostSame l : Postfix l l
| PostStep {a l l'} : Postfix l l' -> Postfix l (l' :r: a).

Fixpoint prefix_nincl {A : Type} `{EqDec A eq} (a : A) (l : list A) : list A :=
  match l with
  | nil => nil
  | b :: l => if a == b then l else prefix_nincl a l
  end.

Lemma prefix_nincl_prefix {A : Type} `{EqDec A eq} (a : A) l :
  In a l -> Prefix (a :: prefix_nincl a l) l.
Proof.
  intros Q.
  induction l; cbn;
    inversion Q.
  - subst a0. destruct (a == a); [|exfalso; apply c; reflexivity].
    econstructor.
  - destruct (a == a0).
    + destruct e. econstructor.
    + econstructor. eauto. 
Qed.

Lemma prefix_cons {A : Type} (l l' : list A) :
  forall a, Prefix (a :: l) l' -> Prefix l l'.
Proof.
  intros a H. dependent induction H.
  - econstructor. econstructor.
  - econstructor. eapply IHPrefix; eauto.
Qed.

Lemma prefix_trans {A : Type} (l1 l2 l3 : list A) :
  Prefix l1 l2 -> Prefix l2 l3 -> Prefix l1 l3.
Proof.
  revert l1 l3. induction l2; intros l1 l3 pre1 pre2; inversion pre1; inversion pre2; subst; eauto.
  econstructor. eapply IHl2; eauto. eapply prefix_cons; eauto.
Qed.

Lemma prefix_cons_cons {A : Type} (a a' : A) l l' :
  Prefix (a :: l) (a' :: l') -> Prefix l l'.
Proof.
  intros H. dependent induction H; cbn.
  - econstructor.
  - destruct l'.
    + inversion H.
    + econstructor. eapply IHPrefix; eauto.
Qed.

Lemma in_prefix_in {A : Type} `{EqDec A eq} (a : A) l l' :
  In a l -> Prefix l l' -> In a l'.
Proof.
  intros Hin Hpre. induction l. 
  - inversion Hin.
  - destruct (a == a0).
    + destruct e. eapply prefix_cons_in; eauto.
    + eapply IHl; eauto.
      * destruct Hin; [exfalso; subst; apply c; reflexivity|assumption].
      * eapply prefix_cons; eauto.
Qed. 

Fixpoint postfix_nincl {A : Type} `{EqDec A eq} (a : A) (l : list A) : list A :=
  match l with
  | nil => nil
  | b :: l => if a == b then nil else b :: postfix_nincl a l
  end.

Lemma postfix_nil {A : Type} (l : list A) : Postfix nil l.
  apply rcons_ind; [econstructor|].
  intros. econstructor; eauto.
Qed.

Ltac rinduction L := revert dependent L; intro L; eapply rcons_ind with (l:=L); intros.

Lemma postfix_cons {A : Type} a (l l': list A) :
  Postfix l l' -> Postfix (a :: l) (a :: l').
Proof.
  intros post.
  - induction post.
    + econstructor.
    + rewrite <-cons_rcons_assoc. econstructor. assumption.
Qed.

Lemma postfix_eq {A : Type} (l1 l2 : list A) :
  Postfix l1 l2 <-> exists l2',  l2 = l1 ++ l2'.
Proof.
  split.
  - intro post. induction post.
    + exists nil. apply app_nil_end.
    + destruct IHpost as [l2' IH].
      exists (l2' :r: a). rewrite IH. unfold rcons. rewrite app_assoc. reflexivity.
  - intros [l2' H]. subst l2.
    rinduction l2'.
    + rewrite <-app_nil_end. econstructor.
    + unfold rcons. rewrite app_assoc. econstructor. eauto.
Qed.

Lemma cons_postfix {A : Type} a b (l l': list A) :
  Postfix (a :: l) (b :: l') -> Postfix l l'.
Proof.
  intros post. apply postfix_eq. apply postfix_eq in post as [l1' leq].
  exists l1'. inversion leq. reflexivity.
Qed.

Lemma postfix_app (* unused *){A : Type} (l1 l2 l' : list A) :
  Postfix (l' ++ l1) (l' ++ l2) -> Postfix l1 l2.
  revert l1 l2. induction l'; intros; cbn; eauto.
  apply IHl'. cbn in H. inversion H. 
  - rewrite H2. econstructor.
  - eapply cons_postfix; eauto.
Qed.

Lemma postfix_nincl_postfix (* unused *){A : Type} `{EqDec A eq} a l : Postfix (postfix_nincl a l) l.
Proof.
  induction l; cbn; [econstructor; reflexivity|].
  destruct (a == a0); cbn; eauto using postfix_nil, postfix_cons.
Qed.

Lemma postfix_nil_nil {A : Type} (l : list A) :
  Postfix l nil -> l = nil.
Proof.
  intro H. inversion H; eauto. destruct l'; cbn in H0; congruence.
Qed.

Lemma prefix_nil_nil (* unused *){A : Type} (l : list A) :
  Prefix l nil -> l = nil.
Proof.
  intro H. inversion H; eauto. 
Qed.  

Lemma postfix_rcons_nil_eq {A : Type} l (a b : A) :
  Postfix (l :r: a) (b :: nil) -> a = b /\ l = nil.
Proof.
  
  intros post. apply postfix_eq in post as [l2' post]. destruct l; cbn in *; eauto.
  - inversion post; eauto.
  - inversion post. destruct l; cbn in H1; congruence.
Qed.

Lemma postfix_nincl_spec {A : Type} `{EqDec A eq} (a : A) l :
  In a l -> Postfix (postfix_nincl a l :r: a) l.
Proof.
  intros ina.
  induction l; inversion ina.
  - subst a0. cbn. destruct equiv_dec;[|exfalso; apply c; reflexivity].
    cbn. apply postfix_cons, postfix_nil.
  - cbn. destruct equiv_dec; cbn.
    + destruct e; apply postfix_cons, postfix_nil.
    + apply postfix_cons. fold (rcons (postfix_nincl a l) a). eauto.
Qed.

Lemma postfix_nincl_invariant {A : Type} `{EqDec A eq} (a : A) l :
  ~ In a l -> postfix_nincl a l = l.
Proof.
  intros nin.
  induction l; cbn; eauto.
  destruct equiv_dec.
  - destruct e. exfalso. apply nin. econstructor; eauto.
  - rewrite IHl; eauto. (*contradict nin. econstructor 2; eauto.*)
Qed.

Lemma postfix_incl {A : Type} (l l' : list A) : Postfix l l' -> incl l l'.
  intros post. induction post.
  - apply incl_refl.
  - apply incl_appl; eauto.
Qed.

Lemma postfix_hd_eq (A : Type) (a b : A) l l' :
  Postfix (a :: l) (b :: l') -> a = b.
Proof.
  intro post. eapply postfix_eq in post as [l2' pst].
  cbn in pst. inversion pst. eauto.
Qed.

Lemma postfix_order_destruct' {A : Type} (l1 l2 l3 : list A) :
  Postfix l1 l3 -> Postfix l2 l3 -> length l1 <= length l2 -> Postfix l1 l2.
Proof.
  revert l1 l3. induction l2; intros l1 l3 post1 post2 len; cbn in *.
  - destruct l1; cbn in len; [econstructor|omega].
  - destruct l1; [eapply postfix_nil|].
    destruct l3; [eapply postfix_nil_nil in post1; congruence|].
    eapply postfix_hd_eq in post1 as aeq. destruct aeq.
    eapply postfix_hd_eq in post2 as aeq. destruct aeq.
    eapply postfix_cons, IHl2. 1,2: eapply cons_postfix; eauto. cbn in len. omega.
Qed.      

Lemma postfix_order_destruct {A : Type} (l1 l2 l3 : list A) :
  Postfix l1 l3 -> Postfix l2 l3 -> Postfix l1 l2 \/ Postfix l2 l1.
Proof.
  intros post1 post2.
  destruct (Nat.ltb (length l1) (length l2)) eqn:H.
  - left. eapply postfix_order_destruct'; eauto. eapply Nat.ltb_lt in H. omega.
  - right. eapply postfix_order_destruct'; eauto. eapply Nat.ltb_nlt in H. omega.
Qed.

Lemma postfix_step_left {A : Type} (l l' : list A) a :
  Postfix (l :r: a) l' -> Postfix l l'.
  intros.
  remember (l :r: a) as l0.
  induction H. subst l0.
  - econstructor. econstructor.
  - econstructor; eauto.
Qed.

Lemma postfix_length {A : Type} (l l' : list A) :
  Postfix l l' -> length l <= length l'.
Proof.
  intros post. induction post.
  - reflexivity.
  - rewrite length_rcons. rewrite IHpost. omega.
Qed.

Lemma postfix_order {A : Type} (l1 l2 l' : list A) (a : A) :
  ~ In a l1 -> In a l2 -> Postfix l1 l'  -> Postfix l2 l' -> Postfix l1 l2.
Proof.
  intros nin1 in2 pst1 pst2. eapply postfix_order_destruct'; eauto.
  eapply postfix_order_destruct in pst1; eauto. clear pst2.
  destruct pst1.
  { exfalso. apply postfix_incl in H. firstorder. }
  apply postfix_length; eauto.
Qed.

Lemma postfix_elem {A : Type} `{EqDec A eq} (a:A) l l':
  length l > 0 -> Postfix l (a :: l') -> In a l.
Proof.
  intros len post.
  destruct l.
  { cbn in len; omega. }
  eapply postfix_hd_eq in post.
  subst a0. econstructor; eauto.
Qed.


Lemma postfix_trans {A : Type} (l l' l'': list A) :
  Postfix l l' -> Postfix l' l'' -> Postfix l l''.
Proof.
  intros post1; revert l''.
  induction post1; intros l'' post2.
  - induction post2; econstructor; eauto.
  - apply IHpost1. eapply postfix_step_left; eauto.
Qed.

Lemma postfix_nincl_nincl {A : Type} `{EqDec A eq} (a : A) l :
  ~ In a (postfix_nincl a l).
Proof.
  induction l; cbn; eauto. destruct (a == a0).
  - tauto.
  - contradict IHl. inversion IHl.
    + subst a0. exfalso; apply c; reflexivity.
    + assumption.
Qed.

Definition prefix_incl : forall (A : Type) (l l' : list A), Prefix l l' -> l ⊆ l'
  := fun (A : Type) (l l' : list A) (post : Prefix l l') =>
       @Prefix_ind A (fun l0 l'0 : list A => l0 ⊆ l'0) (fun l0 : list A => incl_refl l0)
                  (fun (a : A) (l0 l'0 : list A) (_ : Prefix l0 l'0) (IHpost : l0 ⊆ l'0) =>
                     incl_appr (a :: nil) IHpost) l l' post.      


Lemma prefix_in_list {A : Type} l (a:A) :
  In a l
  -> exists l', Prefix (a :: l') l.
Proof.
  intro Hin.
  induction l.
  - inversion Hin. 
  - destruct Hin;[subst;exists l; cbn;econstructor|].
    eapply IHl in H. destruct H as [l' H]. exists l'. cbn; econstructor; assumption.
Qed.

Lemma prefix_nil {A : Type} (l : list A) : Prefix nil l.
Proof.
  induction l; econstructor; firstorder.
Qed.

Lemma prefix_NoDup (* unused *){A : Type} (l l' : list A) : Prefix l l' -> NoDup l' -> NoDup l.
Proof.
  intros Hpre Hnd. induction Hpre; eauto.
  inversion Hnd; subst; eauto.
Qed.

Section Pre.
  Variable A : Type.

  Lemma prefix_eq :
    forall (l1 l2 : list A), Prefix l1 l2 <-> (exists l2' : list A, l2 = l2' ++ l1).
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

  Lemma prefix_length `{EqDec A eq} (l1 l2 : list A)
        (Hpre : Prefix l1 l2)
        (Hlen : length l1 = length l2)
    : l1 = l2.
  Proof.
    eapply prefix_eq in Hpre. destructH. subst l2.
    destruct l2';cbn in *; eauto.
    exfalso.
    rewrite app_length in Hlen. omega.
  Qed.

  Lemma prefix_rev_postfix (l l' : list A)
        (Hpre : Prefix l l')
    : Postfix (rev l) (rev l').
  Proof.
    induction Hpre.
    - econstructor.
    - rewrite rev_cons. econstructor;eauto.
  Qed.

  Lemma prefix_rev_postfix' (l l' : list A)
        (Hpre : Prefix (rev l) (rev l'))
    : Postfix l l'.
  Proof.
    rewrite <-(rev_involutive l).
    rewrite <-(rev_involutive l').
    eapply prefix_rev_postfix;eauto.
  Qed.
  
  Lemma postfix_rev_prefix (l l' : list A)
        (Hpost : Postfix l l')
    : Prefix (rev l) (rev l').
  Proof.
    induction Hpost.
    - econstructor.
    - rewrite rev_rcons. econstructor;eauto.
  Qed.
  
  Lemma postfix_rev_prefix' (l l' : list A)
        (Hpost : Postfix (rev l) (rev l'))
    : Prefix l l'.
  Proof.
    rewrite <-(rev_involutive l).
    rewrite <-(rev_involutive l').
    eapply postfix_rev_prefix;eauto.
  Qed.

  Lemma prefix_order_destruct
    : forall l3 l4 l5 : list A, Prefix l3 l5 -> Prefix l4 l5 -> Prefix l3 l4 \/ Prefix l4 l3.
  Proof.
    intros.
    eapply prefix_rev_postfix in H. eapply prefix_rev_postfix in H0.
    eapply postfix_order_destruct in H;eauto.
    destruct H;[right|left]; eapply postfix_rev_prefix';eauto.
  Qed.

  Lemma prefix_length_eq (* unused *)`{EqDec A eq} (l1 l2 l : list A)
        (Hlen : length l1 = length l2)
        (Hpre1 : Prefix l1 l)
        (Hpre2 : Prefix l2 l)
    : l1 = l2.
  Proof.
    eapply prefix_order_destruct in Hpre1 as Hor;eauto.
    destruct Hor as [Hor|Hor]; eapply prefix_length in Hor; eauto; symmetry; eauto.
  Qed.

  Lemma prefix_induction (* unused *){P : list A -> Prop}
    : P nil
      -> (forall (a : A) (l : list A) (l' : list A), P l' -> Prefix (a :: l') l -> P l)
      -> forall l : list A, P l.
  Proof.
    intros Hbase Hstep l. induction l;eauto.
    eapply Hstep;eauto. econstructor.
  Qed.

End Pre.