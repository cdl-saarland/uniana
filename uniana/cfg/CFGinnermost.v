Require Import Lia.
Require Export CFGloop.

Section cfg.
  Context `{C : redCFG}.

  Notation "p '-a>b' q" := (a_edge p q) (at level 55).
  Notation "p '-a>' q" := (p -a>b q = true) (at level 55).
  Notation "p '-->b' q" := (edge p q) (at level 55).
  Notation "p '-->' q" := (p -->b q = true) (at level 55, right associativity).

  (** * Loop ordering **)

  (** ** Loop ordering by relative depth **)

  Definition deq_loop q p : Prop :=
    forall h, loop_contains h p -> loop_contains h q.

  Global Instance deq_loop_dec h p : dec (deq_loop h p).
  eauto.
  Qed.

  (** ** Preorder properties of deq_loop **)

  (** Reflexivity **)

  Lemma deq_loop_refl l :
    deq_loop l l.
  Proof.
    unfold deq_loop;firstorder.
  Qed.

  Global Instance deq_loop_Reflexive : Reflexive deq_loop.
  Proof.
    unfold Reflexive. intros. eapply deq_loop_refl.
  Qed.

  (** ** Transitivity **)

  Lemma deq_loop_trans p q r
        (H1 : deq_loop p q)
        (H2 : deq_loop q r)
    : deq_loop p r.
  Proof.
    unfold deq_loop in *. intros. eapply H1,H2;eauto.
  Qed.

  Global Instance deq_loop_Transitive : Transitive deq_loop.
  Proof.
    unfold Transitive; eapply deq_loop_trans.
  Qed.

  Program Instance deq_loop_PreOrder : PreOrder deq_loop.

  (** ** deq_loop facts **)

  Lemma loop_contains_deq_loop h p
        (Hloop : loop_contains h p)
    : deq_loop p h.
  Proof.
    unfold deq_loop. intros. eapply loop_contains_trans;eauto.
  Qed.

  Lemma deq_loop_root p
    : deq_loop p root.
  Proof.
    unfold deq_loop.
    intros.
    exfalso.
    eapply root_loop_root in H as H'. subst.
    unfold loop_contains in H. destructH.
    eapply back_edge_incl in H0. eapply root_no_pred;eauto.
  Qed.

  Lemma exit_not_deq h p q
        (Hexit : exit_edge h p q)
        (Hdeq : deq_loop q h)
    : False.
  Proof.
    unfold exit_edge in Hexit. destructH.
    apply Hexit2.
    eapply Hdeq.
    eapply loop_contains_self. eapply loop_contains_loop_head;eauto.
  Qed.

  Lemma deq_loop_head_loop_contains p h
        (Hdeq : deq_loop p h)
        (Hhead : loop_head h)
    : loop_contains h p.
  Proof.
    eapply Hdeq.
    eapply loop_contains_self.
    eauto.
  Qed.

  Lemma deq_loop_depth p q
        (Hdeq : deq_loop p q)
    : depth q <= depth p.
  Proof.
    unfold depth.
    eapply NoDup_incl_length.
    - eapply NoDup_iff_dupfree.
      eapply dupfree_filter.
      eapply dupfree_elements.
    - intros x Hx.
      eapply in_filter_iff in Hx. cbn in Hx.
      eapply in_filter_iff. cbn. destruct Hx. split;auto.
  Qed.

  Lemma deq_loop_depth_leq p q
        (Hdeq : deq_loop p q)
        (Hdep : depth p <= depth q)
    : deq_loop q p.
  Proof.
    unfold depth in Hdep.
    eapply NoDup_length_incl in Hdep.
    - unfold incl in Hdep. setoid_rewrite in_filter_iff in Hdep. cbn in Hdep.
      intros a Ha. eapply Hdep;eauto.
    - eapply NoDup_iff_dupfree. eapply dupfree_filter. eapply dupfree_elements.
    - unfold incl. setoid_rewrite in_filter_iff. intros.
      cbn in *. destructH. eapply Hdeq in H1. eauto.
  Qed.

  Lemma deq_loop_depth_eq p q
        (Hdeq : deq_loop p q)
        (Hdep : depth q = depth p)
    : deq_loop q p.
  Proof.
    eapply deq_loop_depth_leq;eauto.
    lia.
  Qed.

  Lemma depth_zero_iff q
    : depth q = 0 <-> forall h, loop_contains h q -> False.
  Proof.
    unfold depth.
    rewrite length_zero_iff_nil.
    split;intros.
    - eapply filter_nil;eauto.
    - eapply list_emp_in. intros. intro N. eapply H.
      eapply in_filter_iff in N. destructH. cbn in N1. eauto.
  Qed.

  (** ** Equivalence relation eq_loop **)

  Definition eq_loop q p : Prop :=
    deq_loop q p /\ deq_loop p q.

  Lemma eq_loop1  p p' q
    : eq_loop p p' -> deq_loop p q -> deq_loop p' q.
  Proof.
    intros. destruct H.
    eapply deq_loop_trans;eauto.
  Qed.

  Lemma eq_loop2 p q q'
    : eq_loop q q' -> deq_loop p q -> deq_loop p q'.
  Proof.
    intros. destruct H.
    eapply deq_loop_trans;eauto.
  Qed.


  Global Instance eq_loop_Eq : Equivalence eq_loop.
  Proof.
    econstructor.
  - econstructor;apply deq_loop_refl.
  - econstructor; destruct H;eauto.
  - econstructor; destruct H,H0; eapply deq_loop_trans;eauto.
  Qed.

  Global Instance eq_loop_proper_deq_loop1 (p : Lab)
    : Proper (eq_loop ==> Basics.impl) ((Basics.flip deq_loop) p).
  Proof.
    unfold Proper, respectful, Basics.impl.
    intros. eapply eq_loop1; eauto.
  Qed.

  Global Instance eq_loop_proper_deq_loop2 (p : Lab) : Proper (eq_loop ==> Basics.impl) (deq_loop p).
  Proof.
    unfold Proper. unfold respectful. unfold Basics.impl.
    intros. eapply eq_loop2; eauto.
  Qed.

  Global Instance eq_loop_proper_contains (h : Lab)
    : Proper (eq_loop ==> iff) (loop_contains h).
  Proof.
    unfold Proper, respectful, Basics.impl.
    intros. split;eapply H.
  Qed.

  Global Instance eq_loop_depth
    : Proper (eq_loop ==> eq) depth.
  Proof.
    clear.
    unfold Proper,respectful. intros.
    destruct H.
    eapply deq_loop_depth in H.
    eapply deq_loop_depth in H0.
    lia.
  Qed.

  Lemma loop_head_eq_loop_eq h1 h2
        (Hloop1 : loop_head h1)
        (Hloop2 : loop_head h2)
        (Heq : eq_loop h1 h2)
    : h1 = h2.
  Proof.
    destruct Heq.
    eapply loop_contains_Antisymmetric;eauto.
    1: eapply H0.
    2: eapply H.
    1,2: eapply loop_contains_self;eauto.
  Qed.

  Lemma head_unique h b x y
        (Hh : loop_contains h x)
        (Hb : loop_contains b y)
        (Heq : eq_loop h b)
    : h = b.
  Proof.
    unfold eq_loop in Heq.
    unfold deq_loop in *.
    destruct Heq as [H1 H2].
    eapply loop_contains_Antisymmetric; eauto using loop_contains_loop_head, loop_contains_self.
  Qed.

  Lemma eq_loop_same (h h' : Lab)
        (Heq : eq_loop h h')
        (Hl : loop_head h)
        (Hl' : loop_head h')
    : h = h'.
  Proof.
    eapply loop_contains_Antisymmetric.
    all: unfold eq_loop,deq_loop in *;destructH;eauto using loop_contains_self.
  Qed.

  Definition basic_edge p q := eq_loop p q /\ a_edge__P p q.
  Definition eexit_edge p q := exists h, exit_edge h p q.

  Lemma basic_edge_eq_loop p q
        (Hedge : basic_edge p q)
    : eq_loop p q.
  Proof.
    destruct Hedge;auto.
  Qed.

  Lemma depth_basic p q
        (Hedge : basic_edge p q)
    : depth p = depth q.
  Proof.
    eapply basic_edge_eq_loop in Hedge.
    rewrite Hedge. reflexivity.
  Qed.

  Lemma back_edge_eq_loop (p h : Lab)
        (Hp : p ↪ h)
    : eq_loop p h.
  Proof.
    split.
    - eapply loop_contains_deq_loop. eapply loop_contains_ledge;eauto.
    - decide (deq_loop h p);[auto|exfalso]. unfold deq_loop in n. simpl_dec' n.
      simpl_dec' n. destructH. eapply no_exit_head.
      + unfold exit_edge. split_conj;eauto 1. eapply back_edge_incl;eauto.
      + eexists;eauto.
  Qed.

  Lemma depth_back p q
        (Hedge : p ↪ q)
    : depth p = depth q.
  Proof.
    eapply back_edge_eq_loop in Hedge.
    rewrite Hedge. reflexivity.
  Qed.
  Lemma deq_loop_entry (p q : Lab)
        (Hentry : entry_edge p q)
    : deq_loop q p.
  Proof.
    unfold entry_edge in Hentry.
    destructH.
    intros h Heq.
    assert (~ exit_edge h p q).
    - contradict Hentry0. eapply no_exit_head;eauto.
    - do 2 simpl_dec' H. destruct H as [H|[H|H]];[contradiction| |contradiction].
      eapply dec_DN;eauto.
  Qed.

  Lemma deq_loop_entry_or (p q : Lab)
        (Hentry : entry_edge p q)
    : forall h, loop_contains h q -> loop_contains h p \/ h = q.
  Proof.
    intros.
    decide (h = q);[right;auto|left].
    unfold loop_contains,entry_edge in *. destructH. destructH.
    exists p0, (π :r: p). split_conj;eauto.
    - eapply path_rcons;eauto.
    - rewrite rev_rcons. cbn. rewrite <-in_rev. eapply nin_tl_iff in H3;eauto.
      destruct H3;[eauto|]. destr_r' π;subst π;cbn in H. 1: inversion H2.
      path_simpl' H2.
      rewrite rev_rcons in H. cbn in H. inversion H. contradiction.
  Qed.

  Lemma depth_entry p q
        (Hentry : entry_edge p q)
    : S (depth p) = depth q.
  Proof.
    unfold depth.
    match goal with |- S (| ?l |) = | ?l' | => set (lp := l); set (lq := l') end.
    assert (lq =' (q :: lp)).
    {
      split.
      - intros h H. eapply deq_loop_entry_or in Hentry. destruct Hentry;[right|left].
        + eapply in_filter_iff in H. eapply in_filter_iff. destructH. cbn in *. split;eauto.
        + symmetry;eauto.
        + eapply in_filter_iff in H. destructH. cbn in *. eauto.
      - intros h H. destruct H.
        + subst. eapply in_filter_iff. split;eauto. cbn.
          unfold entry_edge in Hentry. destructH.
          eauto using loop_contains_self.
        + eapply in_filter_iff. split; eauto; cbn. eapply deq_loop_entry;eauto.
          eapply in_filter_iff in H. destructH. cbn in H1. auto.
    }
    setoid_rewrite set_eq_NoDup_len at 2;eauto.
    - cbn. reflexivity.
    - eapply NoDup_iff_dupfree. eapply dupfree_filter.
      eapply dupfree_elements.
    - econstructor.
      + intro N. eapply in_filter_iff in N. destructH. cbn in N1. unfold entry_edge in Hentry.
        destructH. contradiction.
      + eapply NoDup_iff_dupfree. eapply dupfree_filter.
        eapply dupfree_elements.
  Qed.

  Lemma deq_loop_exit_or (h p q : Lab)
        (Hexit : exit_edge h p q)
    : forall h', loop_contains h' p -> loop_contains h' q \/ h' = h.
  Proof.
    intros.
    decide (h' = h);[right;auto|left].
    decide (loop_contains h' q);[eauto|].
    exfalso. eapply n.
    eapply single_exit;eauto.
    unfold exit_edge in *. destructH. split;eauto.
  Qed.


  Lemma deq_loop_exiting h qe e
        (Hexit : exit_edge h qe e)
    : deq_loop h qe.
  Proof.
    unfold deq_loop;intros. copy Hexit Hexit'.
    unfold exit_edge in Hexit. destructH. eapply loop_contains_either in Hexit0;eauto.
    destruct Hexit0;[auto|].
    enough (h = h0) by (subst;eauto using loop_contains_self,loop_contains_loop_head).
    eapply single_exit;eauto.
    unfold exit_edge. repeat (split;eauto).
    contradict Hexit2. eapply loop_contains_trans;eauto.
  Qed.

  Lemma deq_loop_exited h qe e
        (Hexit : exit_edge h qe e)
    : deq_loop qe e.
  Proof.
    eapply no_exit_head in Hexit as Hneh.
    unfold exit_edge in *. destructH.
    unfold deq_loop. intros.
    eapply preds_in_same_loop in H;eauto.
    intro N. eapply loop_contains_loop_head in H. subst. contradiction.
  Qed.

  Lemma deq_loop_exited' : forall (h qe e : Lab), exit_edge h qe e -> deq_loop h e.
  Proof.
    intros.
    eapply deq_loop_exited in H as H'.
    eapply deq_loop_exiting in H as H''.
    eapply deq_loop_trans;eauto.
  Qed.

  Lemma eq_loop_exiting h p q
        (Hexit : exit_edge h p q)
    : eq_loop h p.
  Proof.
    split.
    - eapply deq_loop_exiting;eauto.
    - unfold exit_edge in Hexit.
      destruct Hexit as [Hexit _].
      eapply loop_contains_deq_loop;eauto.
  Qed.

  Lemma depth_exit p q
        (Heexit : eexit_edge p q)
    : depth p = S (depth q).
  Proof.
    unfold depth.
    match goal with |- | ?l | = S (| ?l' |) => set (lp := l); set (lq := l') end.
    unfold eexit_edge in Heexit. destructH.
    assert (lp =' (h :: lq)).
    {
      split;intros h' H;[|destruct H]. 1,3: eapply in_filter_iff in H; cbn in H; destructH.
      1: decide (h = h');[left;auto|right].
      all: eapply in_filter_iff; cbn;split;eauto.
      - eapply deq_loop_exit_or in Heexit;eauto. destruct Heexit;[auto|subst;contradiction].
      - eapply deq_loop_exited;eauto.
      - subst. unfold exit_edge in Heexit;destructH;eauto.
    }
    setoid_rewrite set_eq_NoDup_len at 1;eauto.
    3: econstructor.
    2,4: eapply NoDup_iff_dupfree; eapply dupfree_filter;
      eapply dupfree_elements.
    - cbn. reflexivity.
    - intro N. eapply in_filter_iff in N. destructH. cbn in N1. unfold exit_edge in Heexit.
      destructH. contradiction.
  Qed.

  Lemma root_no_loop h
    : ~ loop_contains h root.
  Proof.
    intro H. copy H Q.
    eapply dom_loop in H. unfold Dom in H.
    specialize (H [root]). exploit H. 1: econstructor.
    destruct H;[|contradiction]. subst h.
    eapply loop_contains_loop_head in Q.
    unfold loop_head in Q. destructH. eapply back_edge_incl in Q.
    eapply root_no_pred;eauto.
  Qed.

  Lemma basic_edge_no_loop2 p q
        (Hedge : basic_edge p q)
    : ~ loop_head q.
  Proof.
    intro N.
    destruct Hedge.
    assert (loop_contains q p) as Hloop.
    { destruct H. eapply H. eapply loop_contains_self. eauto. }
    eapply dom_loop in Hloop.
    specialize (a_reachability p) as Hreach. destructH.
    eapply PathCons in H0;eauto.
    eapply dom_dom_acyclic in Hloop.
    unfold Dom in Hloop. eapply Hloop in Hreach.
    eapply acyclic_path_NoDup in H0. inversion H0;subst. contradiction.
  Qed.

  Lemma depth_root
    : depth root = 0.
  Proof.
    unfold depth. eapply length_zero_iff_nil.
    remember (elem Lab) as l. clear Heql.
    induction l;cbn;auto.
    decide (loop_contains a root).
    - exfalso;eapply root_no_loop;eauto.
    - eauto.
  Qed.

  Lemma depth_loop_head h
        (Hhead : loop_head h)
    : depth h > 0.
  Proof.
    unfold depth.
    match goal with |- | ?x | > 0 => set (l := x) end.
    enough (h ∈ l).
    - eapply not_le. intro N. setoid_rewrite <-NoDup_incl_length with (l:=[h]) in N.
      + cbn in N. lia.
      + econstructor;eauto. econstructor.
      + eauto.
    - eapply loop_contains_self in Hhead.
      eapply in_filter_iff. split;eauto.
  Qed.

  Lemma acyclic_entry_head h p
        (Hedge : p -a> h)
        (Hloop : loop_head h)
    : entry_edge p h.
  Proof.
    unfold entry_edge. split;eauto.
    split;[|eapply a_edge_incl;eauto].
    intro N.
    eapply loop_reachs_member in N.
    destruct N.
    eapply a_edge_acyclic;eauto.
  Qed.

  Definition nexit_edge q p := forall h, ~ exit_edge h q p.
  Definition nexited p := forall h q, ~ exit_edge h q p.

  Lemma exited_or_nexited p
    : (forall q, q --> p -> eexit_edge q p) \/ nexited p.
  Proof.
    decide (exists h q, exit_edge h q p);[left|right].
    - intros. destructH. exists h. eapply exit_edge_pred_exiting;eauto.
    - do 2 simpl_dec' n. eassumption.
  Qed.

  Lemma two_edge_exit_cases (q1 q2 p : Lab)
        (Hedge1 : q1 --> p)
        (Hedge2 : q2 --> p)
    : (exists h, exit_edge h q1 p /\ exit_edge h q2 p)
      \/ nexit_edge q1 p /\ nexit_edge q2 p.
  Proof.
    specialize (exited_or_nexited p) as Hen.
    destruct Hen;[left|right].
    - eapply H in Hedge1.
      destruct Hedge1.
      eexists;split;eauto.
      eapply exit_edge_pred_exiting;eauto.
    - unfold nexited,nexit_edge in *. split;intros;eapply  H.
  Qed.

  Lemma depth_exit': forall [h p q : Lab], exit_edge h p q -> depth p = S (depth q).
  Proof.
    intros.
    eapply depth_exit.
    eexists;eauto.
  Qed.

  Lemma exit_edges_loop_eq h1 h2 e1 e2 q1 q2 p
        (Hexit1 : exit_edge h1 q1 e1)
        (Hexit2 : exit_edge h2 q2 e2)
        (Hin1 : loop_contains h1 p)
        (Hin2 : loop_contains h2 p)
        (Heq : eq_loop e1 e2)
    : eq_loop q1 q2.
  Proof.
    eapply loop_contains_either in Hin1 as Heither. 2: eapply Hin2.
    eapply depth_exit' in Hexit1 as Hexdep1.
    eapply depth_exit' in Hexit2 as Hexdep2.
    eapply eq_loop_exiting in Hexit1.
    eapply eq_loop_exiting in Hexit2.
    rewrite <-Hexit1. rewrite <-Hexit2.
    rewrite Heq in Hexdep1. rewrite <-Hexdep1 in Hexdep2.
    rewrite <-Hexit1 in Hexdep2. rewrite <-Hexit2 in Hexdep2.
    destruct Heither;eapply loop_contains_deq_loop in H.
    - eapply deq_loop_depth_eq in Hexdep2;eauto. split;eauto.
    - symmetry in Hexdep2. eapply deq_loop_depth_eq in Hexdep2;eauto. split;eauto.
  Qed.

  (** * Innermost loops and strit-innermost loops **)

  (** ** Definitions **)

  Definition innermost_loop h p : Prop := loop_contains h p /\ deq_loop h p.

  Definition innermost_loop_strict (h p : Lab)
    := loop_contains h p /\ h <> p /\ forall h', loop_contains h' p -> (loop_contains h' h \/ h' = p).

  Definition finType_sig_or_never (X : finType) (P : decPred X) : {x : X | P x} + {forall x : X, ~ P x}.
  Proof.
    remember (filter P (elem X)).
    destruct l.
    - right. intros ? ?. specialize (in_filter_iff P x (elem X)) as Hiff. rewrite <-Heql in Hiff.
      cbn in Hiff. eapply Hiff. split;eauto.
    - left. econstructor. specialize (in_filter_iff P e (elem X)) as Hiff.
      rewrite <-Heql in Hiff. cbn in Hiff. eapply Hiff. eauto.
  Qed.

  Definition ex_innermost_loop p
    := finType_sig_or_never (DecPred (fun h => innermost_loop h p)).

  Definition ex_innermost_loop_strict (p : Lab)
    : {h : Lab | innermost_loop_strict h p} + {forall h, ~ innermost_loop_strict h p}
    := finType_sig_or_never (DecPred (fun h => innermost_loop_strict h p)).

  Definition get_innermost_loop (p : Lab) : option Lab :=
    match ex_innermost_loop p with
    | inleft (exist _ h _) => Some h
    | inright _ => None
    end.

  Definition get_innermost_loop_strict (p : Lab) : option Lab :=
    match ex_innermost_loop_strict p with
    | inleft (exist _ h _) => Some h
    | inright _ => None
    end.

  Definition get_innermost_loop_dep (p : Lab) : option {h : Lab | loop_contains h p} :=
    match ex_innermost_loop p with
    | inleft (exist _ h H) => Some (exist _ h (match H with
                                              | conj Q _ => Q
                                              end))
    | inright _ => None
    end.

  Definition get_innermost_loop_strict_dep (p : Lab) : option {h : Lab | loop_contains h p} :=
    match ex_innermost_loop_strict p with
    | inleft (exist _ h H) => Some (exist _ h (match H with
                                              | conj Q _ => Q
                                              end))
    | inright _ => None
    end.

  (** ** Basic facts  **)


  Lemma innermost_eq_loop h q
        (Hinnermost : innermost_loop h q)
    : eq_loop h q.
  Proof.
    destruct Hinnermost. split;auto.
    eapply loop_contains_deq_loop;auto.
  Qed.

  Lemma innermost_loop_head h h'
        (Hloop : loop_head h)
        (Hinner : innermost_loop h' h)
    : h = h'.
  Proof.
    eapply eq_loop_same.
    - symmetry. eapply innermost_eq_loop;eauto.
    - eauto.
    - destruct Hinner. eapply loop_contains_loop_head;eauto.
  Qed.

  Lemma innermost_loop_deq_loop h p q
        (Hinner : innermost_loop h p)
        (Hloop : loop_contains h q)
    : deq_loop q p.
  Proof.
    unfold innermost_loop in Hinner. destructH.
    eapply deq_loop_trans;eauto.
    eapply loop_contains_deq_loop;eauto.
  Qed.

  Lemma eq_loop_innermost h p q
        (Heq : eq_loop p q)
        (Hinner : innermost_loop h p)
    : innermost_loop h q.
  Proof.
    unfold innermost_loop in *.
    destructH.
    split;[eapply Heq in Hinner0;auto|].
    unfold eq_loop in Heq. destructH.
    eapply deq_loop_trans;eauto.
  Qed.

  Lemma path_no_loop_head_deq p e h π
        (Hπ : Path edge__P p e π)
        (Hinner : innermost_loop h e)
        (Hnin : h ∉ π)
    : forall x, x ∈ π -> deq_loop x e.
  Proof.
    intros.
    decide (deq_loop x e); try eassumption.
    rename n into Hndeq.
    exfalso.
    assert (Hncont : ~ loop_contains h x). {
      eauto using innermost_loop_deq_loop.
    }
    eapply path_from_elem in H; try eauto.
    destruct H as [ϕ [Hϕ Hpost]].
    eapply Hnin.
    destruct Hinner.
    eapply in_postfix_in; try eassumption.
    eapply dom_loop_contains; try eassumption.
  Qed.

  Global Instance eq_loop_proper_innermost (h : Lab)
    : Proper (eq_loop ==> iff) (innermost_loop h).
  Proof.
    unfold Proper, respectful, Basics.impl.
    intros. unfold innermost_loop. split; intros.
    - rewrite H in H0. eassumption.
    - rewrite <- H in H0. eassumption.
  Qed.

  (** ** Uniqueness *)

  Lemma innermost_loop_strict_unique (h h' p : Lab)
        (H : innermost_loop_strict h p)
        (Q : innermost_loop_strict h' p)
    : h = h'.
  Proof.
    unfold innermost_loop_strict in *. do 2 destructH.
    eapply H3 in Q0. destruct Q0;[|contradiction].
    eapply Q3 in H0. destruct H0;[|contradiction].
    eapply loop_contains_Antisymmetric;auto.
  Qed.

  Lemma innermost_unique a b c
        (Ha : innermost_loop a c)
        (Hb : innermost_loop b c)
    : a = b.
  Proof.
    destruct Ha as [Ha Ha'].
    destruct Hb as [Hb Hb'].
    unfold deq_loop in *.
    eauto using loop_contains_Antisymmetric.
  Qed.

  Lemma innermost_unique' a b c d
        (Ha : innermost_loop a c)
        (Hb : innermost_loop b d)
        (Heq : eq_loop c d)
    : a = b.
  Proof.
    destruct Ha as [Ha Ha'].
    destruct Hb as [Hb Hb'].
    destruct Heq.
    unfold deq_loop in *.
    eapply loop_contains_Antisymmetric; eauto.
  Qed.

  Lemma back_edge_loop_contains a b x
        (Hedge : back_edge a b)
        (Hinner : loop_contains x a)
    : loop_contains x b.
  Proof.
    specialize (loop_contains_loop_head Hinner) as Hhead.
    eauto using loop_contains_deq_loop, back_edge_eq_loop, deq_loop_head_loop_contains, eq_loop1.
  Qed.

  Lemma back_edge_innermost h l
        (Hbe : back_edge l h)
    : innermost_loop h l.
  Proof.
    destruct (back_edge_eq_loop Hbe) as [H1 H2].
    unfold innermost_loop.
    eauto using loop_contains_ledge.
  Qed.

  Lemma back_edge_src_no_loop_head
        a b
        (Hbe : back_edge b a)
    : ~ loop_head b.
  Proof.
    intro. eapply no_self_loops.
    - eapply Hbe.
    - eapply innermost_unique. unfold innermost_loop. unfold deq_loop.
      eauto using loop_contains_self.
      eauto using back_edge_innermost.
  Qed.

  (** ** Paths in the loop tree **)

  Definition LPath := Path (fun h p => (innermost_loop_strict h p)).

  Lemma find_some_strong (A : Type) `{Q:EqDec A eq} (f : A -> bool) (l : list A) (x : A) (Hnd : NoDup l)
    : find f l = Some x -> x ∈ l /\ f x = true /\ forall y, y ≻* x | l -> f y = true -> x = y.
  Proof.
    repeat split. 1,2: eapply find_some in H; firstorder.
    revert dependent x.
    induction l;intros.
    - inversion H0.
    - cbn in H.
      destruct (f a) eqn:E.
      + inversion H; subst. inversion H0;subst;auto.
        inversion Hnd; subst. exfalso; contradict H5. eapply splinter_incl;[eapply H4|]. firstorder 0.
      + destruct (a == y);[rewrite e in E;congruence|].
        inversion Hnd; subst. eapply IHl;eauto. inversion H0;subst;auto. congruence.
  Qed.

  Lemma loop_LPath_helper p h π
        (Hpath : Path a_edge__P root p (p :: π))
        (Hloop : loop_contains h p)
        (Hin : h ∈ π)
        (Hnolo : forall q : Lab, q ≻* h | π -> toBool _ (D:=decision (loop_contains q p)) = true -> h = q)
    : (forall h' : Lab, loop_contains h' p -> loop_contains h' h \/ h' = p).
  Proof.
    intros. eapply loop_contains_either in H as H';[|apply Hloop].
    destruct H';[|left;auto].
    decide (h' = p);[right;auto|].
    specialize (Hnolo h'). exploit Hnolo.
    - eapply subgraph_path' in Hpath;eauto using a_edge_incl.
      eapply loop_contains_splinter in Hpath;eauto.
      cbn in Hpath. inversion Hpath;subst;auto. inversion H2;subst;contradiction.
    - decide (loop_contains h' p); cbn in *;[congruence|contradiction].
    - subst. left. eapply loop_contains_self. eapply loop_contains_loop_head;eauto.
  Qed.

  Lemma loop_LPath h p
        (Hloop : loop_contains h p)
    : exists π, LPath h p π.
  Proof.
    specialize (a_reachability p) as Hreach.
    destructH. revert dependent p. revert dependent π.
    specialize (well_founded_ind (R:=(@StrictPrefix' Lab)) (@StrictPrefix_well_founded Lab)
                                 (fun π : list Lab => forall p, loop_contains h p
                                                           -> Path a_edge__P root p π
                                                           -> exists (π0 : list Lab), LPath h p π0))
      as WFind.
    eapply WFind.
    intros;clear WFind.
    destruct x.
    - inversion H1; subst p a e.
    - remember (find (fun h' => decision (loop_contains h' p)) x) as S.
      destruct S; symmetry in HeqS.
      + eapply find_some_strong in HeqS. destructH. decide (loop_contains e0 p);cbn in *;[|congruence].
        2: auto.
        2: { eapply acyclic_path_NoDup in H1. inversion H1;auto. }
        inversion H1; [subst x ;contradiction|]. subst π a c e.
        decide (h = p).
        { subst;eexists;econstructor. }
        specialize (@path_to_elem _ a_edge__P _ _ e0 x H6 HeqS0) as [ϕ [Hϕ0 Hϕ1]].
        specialize (H ϕ). exploit' H.
        { cbn. clear - Hϕ1.
          eapply prefix_strictPrefix;auto.
        }
        specialize (H e0). exploit H.
        { clear - l H0 n HeqS0 HeqS3 H1.
          decide (e0 = h);[subst;eapply loop_contains_self;unfold loop_contains in H0;firstorder|].
          eapply loop_contains_either in H0 as H0'; eauto.
          destruct H0';[exfalso|auto].
          eapply (loop_LPath_helper) in HeqS3;auto. 2:exact H0. destruct HeqS3;[|contradiction].
          eapply loop_contains_Antisymmetric in H. exploit H. contradiction.
        }
        destructH.
        exists (p :: π0).
        econstructor;cycle 1.
        * instantiate (1:=e0). decide (innermost_loop_strict e0 p);cbn;[auto|exfalso;contradict n0].
          unfold innermost_loop_strict. split;auto. split.
          -- eapply acyclic_path_NoDup in H1. clear - HeqS0 H1. inversion H1; subst.
             contradict H2. subst. auto.
          -- eapply loop_LPath_helper;eauto.
        * auto.
      + decide (h = e); subst.
        { inversion H1.
          - subst x e p a. repeat econstructor.
          - subst π e c a. repeat econstructor. }
        eapply find_none in HeqS;cycle 1.
        * instantiate (1:=h).
          enough (h ∈ (e :: x)) as Hex.
          { destruct Hex;[symmetry in H2;contradiction|auto]. }
          eapply dom_dom_acyclic;eauto. eapply dom_loop;auto.
        * exfalso. decide (loop_contains h p); cbn in *; [congruence|contradiction].
  Qed.

  (** ** Existence **)

  Lemma loop_contains_innermost (h p : Lab)
        (Hloop : loop_contains h p)
    : exists h', innermost_loop h' p.
  Proof.
    unfold innermost_loop.
    eapply loop_LPath in Hloop as Hloop'. destructH.
    decide (loop_head p).
    + exists p. split;eauto using loop_contains_self. unfold deq_loop; firstorder.
    + inversion Hloop'. subst.
      * exists p. split;eauto using loop_contains_self. unfold deq_loop; firstorder.
      * subst. exists b.
        decide (innermost_loop_strict b p);cbn in *;[|congruence]. unfold innermost_loop_strict in i.
        clear - i n. destructH. unfold deq_loop.
        split;auto. intros. exploit i3. destruct i3;auto.
        subst. eapply loop_contains_loop_head in H. contradiction.
  Qed.

  Lemma loop_contains_innermost_strict (h p : Lab)
        (Hloop : loop_contains h p)
        (Hneq : h <> p)
    : exists h', innermost_loop_strict h' p.
  Proof.
    eapply loop_LPath in Hloop as Hloop'. destructH.
    inversion Hloop';subst;eauto;[contradiction].
  Qed.

  Lemma get_innermost_loop_spec
    : forall p : Lab,
      match get_innermost_loop p with
      | Some h => innermost_loop h p
      | None => forall h' : Lab, loop_contains h' p -> False
      end.
  Proof.
    unfold get_innermost_loop.
    intro. destruct (ex_innermost_loop p).
    - destruct s;eauto.
    - cbn in n. unfold innermost_loop in n. intros.
      eapply loop_contains_innermost in H. clear h'. destructH.
      specialize (n h'). eapply dec_DM_and in n;eauto.
      destruct n;unfold innermost_loop in H;firstorder.
  Qed.

  Lemma get_innermost_loop_dep_spec
    : forall p : Lab,
      match get_innermost_loop_dep p with
      | Some (exist _ h _) => innermost_loop h p
      | None => forall h' : Lab, loop_contains h' p -> False
      end.
  Proof.
    unfold get_innermost_loop_dep.
    intro. destruct (ex_innermost_loop p).
    - destruct s;eauto.
    - cbn in n. unfold innermost_loop in n. intros.
      eapply loop_contains_innermost in H. clear h'. destructH.
      specialize (n h'). eapply dec_DM_and in n;eauto.
      destruct n;unfold innermost_loop in H;firstorder.
  Qed.

  Lemma get_innermost_loop_strict_spec (p : Lab)
    : match get_innermost_loop_strict p with
      | Some h => innermost_loop_strict h p
      | None => forall h', loop_contains h' p -> h' = p
      end.
  Proof.
    unfold get_innermost_loop_strict.
    destruct (ex_innermost_loop_strict p); cbn.
    - destruct s. eauto.
    - intros.
      decide (h' = p);[eauto|].
      eapply loop_contains_innermost_strict in H;eauto.
      destructH. specialize (n h'0); contradiction.
  Qed.

  Lemma get_innermost_loop_strict_dep_spec (p : Lab)
    : match get_innermost_loop_strict_dep p with
      | Some (exist _ h H) => innermost_loop_strict h p
      | None => forall h', loop_contains h' p -> h' = p
      end.
  Proof.
    unfold get_innermost_loop_strict_dep.
    destruct (ex_innermost_loop_strict p); cbn.
    - destruct s. eauto.
    - intros.
      decide (h' = p);[eauto|].
      eapply loop_contains_innermost_strict in H;eauto.
      destructH. specialize (n h'0); contradiction.
  Qed.

  (** * Lemmas about relative loop depth on exit edges **)

  Lemma exit_edge_innermost h q e
        (Hexit : exit_edge h q e)
    : innermost_loop h q.
  Proof.
    clear - Hexit.
    unfold innermost_loop. split.
    - destruct Hexit. eauto.
    - eapply deq_loop_exiting;eauto.
  Qed.

  Lemma depth_ex_innermost p
        (Hdep : 0 < depth p)
    : exists h, innermost_loop h p.
  Proof.
    decide (exists h, loop_contains h p).
    - destructH. eapply loop_contains_innermost;eauto.
    - simpl_dec' n. eapply depth_zero_iff in n. lia.
  Qed.

  Lemma ex_depth_head' p n
        (Hdep : S n <= depth p)
    : exists h, loop_contains h p /\ depth h = S n.
  Proof.
    eapply Nat.le_exists_sub in Hdep. destructH. clear Hdep1.
    rename Hdep0 into Hdep. rename p0 into d.
    revert dependent p.
    induction d;intros.
    - specialize (@depth_ex_innermost p) as Hinner.
      exploit Hinner. lia. destructH.
      exists h. split;[destruct Hinner;eauto|].
      eapply innermost_eq_loop in Hinner. rewrite Hinner. lia.
    - specialize (@depth_ex_innermost p) as Hinner.
      exploit Hinner. lia. destructH.
      eapply innermost_eq_loop in Hinner as Heq.
      destruct Hinner as [Hloop Hdeq].
      specialize (a_reachability h) as Hreach.
      destructH.
      destruct π as [ | x π];[inv Hreach|].
      destruct π as [ | y π].
      { exfalso. eapply path_single in Hreach. destructH. subst h. subst x.
        eapply root_no_loop. eauto using loop_contains_self, loop_contains_loop_head. }
      inv_path Hreach.
      eapply acyclic_entry_head in H0 as Hentry. 2:eauto using loop_contains_loop_head.
      eapply depth_entry in Hentry as Hentry_dep.
      specialize (IHd y).
      exploit IHd. rewrite Heq in Hentry_dep. lia.
      destructH.
      exists h0. split;[|eauto].
      eapply deq_loop_entry in Hentry.
      eapply Hentry in IHd0.
      eapply loop_contains_trans;eauto.
  Qed.

  Lemma ex_depth_head p n
        (Hdep : n <= depth p)
        (Hn0 : n <> 0)
    : exists h, loop_contains h p /\ depth h = n.
  Proof.
    destruct n. 1:contradiction.
    eapply ex_depth_head' in Hdep;eauto.
  Qed.

(*  Lemma dom_self_loop h p π
        (Hpath : CPath p p π)
        (Hinl : innermost_loop h p)
        (Hnin : h ∉ π)
    : π = [p].
  Proof.
    clear - Hpath Hinl Hnin.
    inversion Hpath;subst.
    - reflexivity.
    - exfalso. eapply Hnin.
*)

  (** * Variant of get_innermost_loop that uses the root if there is no loop **)

  Definition get_innermost_loop' p
    := match get_innermost_loop p with
       | Some h => h
       | None => root
       end.

  Lemma deq_loop_innermost' (p : Lab)
    : deq_loop (get_innermost_loop' p) p.
  Proof.
    remember (get_innermost_loop' p) as h.
    specialize (get_innermost_loop_spec p) as Hspec.
    unfold get_innermost_loop' in Heqh.
    destruct (get_innermost_loop p).
    - subst. unfold innermost_loop in Hspec. subst. destructH; auto.
    - subst. unfold deq_loop. intros. exfalso; eauto.
  Qed.
  Definition innermost_loop' `{redCFG} (h p : Lab) := (loop_contains h p \/ h = root) /\ deq_loop h p.

  Definition get_innermost_loop_strict' p
    := match get_innermost_loop_strict p with
       | Some h => h
       | None => root
       end.

End cfg.
