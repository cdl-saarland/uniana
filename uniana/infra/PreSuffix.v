Require Import Program.Equality Lia.

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

Global Instance Prefix_Transitive (A : Type) : Transitive (@Prefix A).
Proof.
  unfold Transitive.
  eapply prefix_trans.
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
      exists (l2' :r: a). rewrite IH. rewrite app_assoc. reflexivity.
  - intros [l2' H]. subst l2.
    rinduction l2'.
    + rewrite <-app_nil_end. econstructor.
    + rewrite app_assoc. econstructor. eauto.
Qed.

Lemma cons_postfix {A : Type} a b (l l': list A) :
  Postfix (a :: l) (b :: l') -> Postfix l l'.
Proof.
  intros post. apply postfix_eq. apply postfix_eq in post as [l1' leq].
  exists l1'. inversion leq. reflexivity.
Qed.

Lemma postfix_app {A : Type} (l1 l2 l' : list A) :
  Postfix (l' ++ l1) (l' ++ l2) -> Postfix l1 l2.
Proof.
  revert l1 l2. induction l'; intros; cbn; eauto.
  apply IHl'. cbn in H. inversion H.
  - rewrite H2. econstructor.
  - eapply cons_postfix; eauto.
Qed.

Lemma postfix_nincl_postfix {A : Type} `{EqDec A eq} a l : Postfix (postfix_nincl a l) l.
Proof.
  induction l; cbn; [econstructor; reflexivity|].
  destruct (a == a0); cbn; eauto using postfix_nil, postfix_cons.
Qed.

Lemma postfix_nil_nil {A : Type} (l : list A) :
  Postfix l nil -> l = nil.
Proof.
  intro H. inversion H; eauto. destruct l'; cbn in H0; congruence.
Qed.

Lemma prefix_nil_nil {A : Type} (l : list A) :
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
    + apply postfix_cons. eauto.
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
Proof.
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
  - destruct l1; cbn in len; [econstructor|lia].
  - destruct l1; [eapply postfix_nil|].
    destruct l3; [eapply postfix_nil_nil in post1; congruence|].
    eapply postfix_hd_eq in post1 as aeq. destruct aeq.
    eapply postfix_hd_eq in post2 as aeq. destruct aeq.
    eapply postfix_cons, IHl2. 1,2: eapply cons_postfix; eauto. cbn in len. lia.
Qed.

Lemma postfix_order_destruct {A : Type} (l1 l2 l3 : list A) :
  Postfix l1 l3 -> Postfix l2 l3 -> Postfix l1 l2 \/ Postfix l2 l1.
Proof.
  intros post1 post2.
  destruct (Nat.ltb (length l1) (length l2)) eqn:H.
  - left. eapply postfix_order_destruct'; eauto. eapply Nat.ltb_lt in H. lia.
  - right. eapply postfix_order_destruct'; eauto. eapply Nat.ltb_nlt in H. lia.
Qed.

Lemma postfix_step_left {A : Type} (l l' : list A) a :
  Postfix (l :r: a) l' -> Postfix l l'.
Proof.
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
  - rewrite length_rcons. rewrite IHpost. lia.
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
  { cbn in len; lia. }
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

Lemma prefix_NoDup {A : Type} (l l' : list A) : Prefix l l' -> NoDup l' -> NoDup l.
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
    rewrite app_length in Hlen. lia.
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

  Lemma prefix_length_eq `{EqDec A eq} (l1 l2 l : list A)
        (Hlen : length l1 = length l2)
        (Hpre1 : Prefix l1 l)
        (Hpre2 : Prefix l2 l)
    : l1 = l2.
  Proof.
    eapply prefix_order_destruct in Hpre1 as Hor;eauto.
    destruct Hor as [Hor|Hor]; eapply prefix_length in Hor; eauto; symmetry; eauto.
  Qed.

  Lemma prefix_induction {P : list A -> Prop}
    : P nil
      -> (forall (a : A) (l : list A) (l' : list A), P l' -> Prefix (a :: l') l -> P l)
      -> forall l : list A, P l.
  Proof.
    intros Hbase Hstep l. induction l;eauto.
    eapply Hstep;eauto. econstructor.
  Qed.

  Lemma prefix_ex_cons (l l' : list A) (a : A)
    : Prefix l l' -> exists a', Prefix (a' :: l) (a :: l').
  Proof.
    intros Hpre. revert a. induction Hpre; intros b.
    - exists b. econstructor.
    - specialize (IHHpre a). destructH. eexists. econstructor. eauto.
  Qed.

  Lemma postfix_ex_cons
    : forall (l l' : list A) (a : A), Postfix l l' -> exists a' : A, Postfix (l :r: a') (l' :r: a).
  Proof.
    intros. eapply postfix_rev_prefix in H. eapply prefix_ex_cons in H. destructH.
    exists a'. eapply prefix_rev_postfix'. do 2 rewrite rev_rcons. eauto.
  Qed.

  Lemma rcons_inj (l l' : list A) (a b : A)
    : l ++ [a] = l' ++ [b] -> l = l' /\ a = b.
  Proof.
    revert dependent l'.
    induction l;intros.
    - cbn in H. destruct l';cbn in *;eauto.
      + split;inversion H;eauto.
      + inversion H. congruence'.
    - destruct l';cbn in *.
      + inversion H. congruence'.
      + inversion H. subst. split;[f_equal|];eapply IHl;eauto.
  Qed.

  Lemma postfix_rcons_rcons (l l' : list A) (a a' : A)
    : Postfix (l ++ [a]) (l' ++ [a']) -> Postfix l l'.
  Proof.
    intros Hpost.
    eapply postfix_eq in Hpost. destructH.
    revert dependent a. revert a' l.
    induction l2';intros.
    - rewrite app_nil_r in Hpost. eapply rcons_inj in Hpost. destructH. subst. constructor.
    - eapply postfix_step_left. eapply IHl2'. rewrite <-app_cons_assoc. eauto.
  Qed.

  Lemma tl_prefix (l : list A)
    : Prefix (tl l) l.
  Proof.
    induction l;cbn;econstructor;eauto. econstructor.
  Qed.

  Lemma prefix_tl (l l' : list A) (a : A)
    : Prefix (a :: l) l' -> Prefix l (tl l').
  Proof.
    clear. intros. inversion H;subst;cbn.
    - econstructor.
    - eapply prefix_cons;eauto.
  Qed.

  Lemma prefix_rcons (l l' : list A) (a : A)
        (Hpref : Prefix l l')
    : Prefix (l :r: a) (l' :r: a).
  Proof.
    clear - Hpref.
    revert dependent l.
    induction l';intros l Hpref;cbn.
    - destruct l;cbn.
      + econstructor.
      + inversion Hpref.
    - inversion Hpref;subst.
      + cbn. econstructor.
      + econstructor. eapply IHl';eauto.
  Qed.

  Lemma postfix_take (l l' : list A)
    : take ( |l'| ) l = l' <-> Postfix l' l.
  Proof.
    split; intro H.
    - rewrite <-H.
      remember (|l'|) as n. clear.
      revert l. induction n.
      + cbn. eapply postfix_nil.
      + intros l. destruct l.
        * cbn. econstructor;auto.
        * cbn. eapply postfix_cons;eauto.
    - revert dependent l. induction l';intros;cbn;auto.
      destruct l. 1: inversion H;congruence'.
      f_equal.
      + symmetry;eapply postfix_hd_eq;eauto.
      + eapply IHl'. eapply cons_postfix;eauto.
  Qed.

  Lemma prefix_take_r (l l' : list A)
    : take_r ( |l'| ) l = l' <-> Prefix l' l.
  Proof.
    split; intro H.
    - eapply postfix_rev_prefix'.
      eapply postfix_take.
      eapply rev_rev_eq.
      rewrite rev_involutive.
      rewrite rev_length.
      unfold take_r in H.
      assumption.
    - eapply prefix_rev_postfix in H.
      eapply postfix_take in H.
      eapply rev_rev_eq in H.
      rewrite rev_involutive in H.
      rewrite rev_length in H.
      unfold take_r.
      assumption.
  Qed.

  Global Instance Prefix_Reflexive : Reflexive (@Prefix A).
  Proof.
    econstructor.
  Qed.

  Global Instance Postfix_Reflexive : Reflexive (@Postfix A).
  Proof.
    econstructor.
  Qed.

  Global Instance Prefix_dec (B : eqType)(l l' : list B) : dec (Prefix l l').
  Proof.
    clear.
    revert l;induction l';intros l.
    - destruct l;[left; eapply prefix_nil|]. right. intro N. inversion N.
    - destruct (IHl' l).
      + left. econstructor;eauto.
      + decide (l = a :: l').
        * left. subst. econstructor.
        * right. contradict n. inversion n;subst;[contradiction|].
          eauto.
  Qed.

  Lemma prefix_antisym (l l' : list A)
        (H : Prefix l l')
        (Q : Prefix l' l)
    : l = l'.
  Proof.
    eapply prefix_eq in H.
    eapply prefix_eq in Q.
    do 2 destructH.
    rewrite Q in H.
    rewrite app_assoc in H.
    induction (l2'0 ++ l2') eqn:E.
    - destruct l2'0.
      + cbn in E. rewrite E in Q. cbn in Q. eauto.
      + cbn in E. congruence.
    - exfalso. cbn in H. clear - H.
      revert dependent a. revert l0. induction l';intros.
      + congruence.
      + destruct l0;cbn in H.
        * inversion H. subst. eapply IHl'. instantiate (1:=nil). cbn. eapply H2.
        * inversion H. subst. eapply IHl'. rewrite app_cons_assoc in H2.
          eapply H2.
  Qed.

  Lemma prefix_cons_cons (a a' : A) l l' :
    Prefix (a :: l) (a' :: l') -> Prefix l l'.
  Proof.
    intros H. dependent induction H; cbn.
    - econstructor.
    - destruct l'.
      + inversion H.
      + econstructor. eapply IHPrefix; eauto.
  Qed.

  Lemma prefix_nincl_prefix' `{EqDec A eq} (l : list A) a
    : Prefix (prefix_nincl a l) l.
  Proof.
    induction l;cbn;eauto.
    - econstructor.
    - destruct (a == a0).
      + econstructor. econstructor.
      + econstructor. eauto.
  Qed.

End Pre.

Lemma postfix_map {A B : Type} (f : A -> B) :
  forall l l', Postfix l l' -> Postfix (map f l) (map f l').
Proof.
  intros ? ? Hpost.
  induction Hpost;[econstructor|rewrite map_rcons;econstructor;assumption].
Qed.

Lemma prefix_map_fst (A B : Type) (l l' : list (A * B))
      (Hpre: Prefix l l')
  : Prefix (map fst l) (map fst l').
Proof.
  induction Hpre.
  - econstructor.
  - destruct a. cbn. econstructor;eauto.
Qed.

Lemma postfix_map_fst (A B : Type) (l l' : list (A * B))
      (Hpre: Postfix l l')
  : Postfix (map fst l) (map fst l').
Proof.
  eapply prefix_rev_postfix'.
  do 2 rewrite <-map_rev.
  eapply prefix_map_fst.
  eapply postfix_rev_prefix;eauto.
Qed.

Lemma prefix_len_leq (A : Type) (l l' : list A)
      (Hpre : Prefix l l')
  : | l | <= | l' |.
Proof.
  induction Hpre;cbn;eauto.
Qed.

Lemma in_postfix_in {A : Type} l l' (a : A)
  :  a ∈ l -> Postfix l l' -> a ∈ l'.
Proof.
  intros Hin Hpost.
  revert dependent l.
  induction l'.
  - intros. eapply postfix_nil_nil in Hpost. subst. inv Hin.
  - intros.
    destruct l as [| b  l].
    + inv Hin.
    + simpl in Hin.
      destruct Hin.
      * left. symmetry. rewrite H in Hpost. eauto using postfix_hd_eq.
      * right. eauto using cons_postfix.
Qed.

Lemma prefix_fst_prefix {S T : Type} (a b : list (S * T))
      (Hprefix: Prefix a b)
  : Prefix (map fst a) (map fst b).
Proof.
  induction Hprefix.
  - econstructor.
  - simpl. econstructor. eauto.
Qed.

Lemma prefix_cycle (A : Type) (l : list A) a
  : Prefix (a :: l) l -> False.
Proof.
  revert a.
  induction l;cbn;intros.
  - inv H.
  - inv H.
    + exfalso;eapply list_cycle;eauto.
    + eapply prefix_cons in H2. eauto.
Qed.

(** StrictPrefix **)

Section StrictPre.

  Variable (A : Type).

  Definition StrictPrefix' :=
    fun (l l' : list A) => exists a : A, Prefix (a :: l) l'.

  Lemma prefix_strictPrefix:
    forall (e : A) (x ϕ : list A), Prefix ϕ x -> StrictPrefix' ϕ (e :: x).
  Proof.
    intros e x ϕ Hϕ1.
    unfold StrictPrefix'. cbn.
    revert dependent e.
    induction Hϕ1; intros.
    - exists e; econstructor.
    - specialize(IHHϕ1 a). destructH. exists a0. econstructor. auto.
  Qed.

  Lemma StrictPrefix_well_founded : well_founded (StrictPrefix').
  Proof.
    unfold well_founded.
    intros.
    induction a.
    - econstructor. intros. unfold StrictPrefix' in *. destructH. inversion H.
    - constructor. intros.
      unfold StrictPrefix' in H.
      destructH. cbn in *. inversion H;subst.
      + subst. auto.
      + eapply IHa. unfold StrictPrefix'. exists a1. cbn. auto.
  Qed.

End StrictPre.
