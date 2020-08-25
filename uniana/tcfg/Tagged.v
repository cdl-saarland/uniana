Require Export Precedes CFGancestor Tagle.

Require Import PropExtensionality Lia.

Section tagged.

  Context `{C : redCFG}.

  Program Instance Tag_dec : EqDec Tag eq.
  Next Obligation.
    apply list_eqdec, nat_eq_eqdec.
  Qed.

  Definition start_tag : Tag := nil.

  Definition Coord : Type := (Lab * Tag).
  Hint Resolve Tag_dec.

  Program Instance Coord_dec : EqDec Coord eq.
  Next Obligation.
    eapply prod_eqdec;eauto.
  Qed.

  Hint Resolve Coord_dec.

  (** * Kinds of edges in a redCFG **)

  Definition basic_edge p q := eq_loop p q /\ a_edge__P p q.
  Definition eexit_edge p q := exists h, exit_edge h p q.

  Inductive Edge (p q : Lab) : Type :=
  | Enormal : basic_edge p q -> Edge p q
  | Eback : back_edge p q -> Edge p q
  | Eentry : entry_edge p q -> Edge p q
  | Eexit : eexit_edge p q -> Edge p q.

  Lemma Edge_disj (p q : Lab) (H Q : Edge p q)
    : H = Q.
  Proof.
    destruct H,Q.
    all: match goal with
         | |- ?x _ = ?x _ => f_equal;eapply proof_irrelevance
         | |- _ => exfalso
         end.
    all: unfold back_edge,entry_edge, eexit_edge, exit_edge, basic_edge in *.
    all: unfold_edge_op' b; unfold_edge_op' b0; repeat destructH;
      try contradiction.
    7,10:eapply no_exit_head;unfold exit_edge;eauto.
    4,8:exfalso;eapply no_exit_head;eexists;eauto; unfold back_edge; unfold_edge_op; eauto.
(*    all: lazymatch goal with
         | H : ~ loop_contains ?q ?p,
               Q : eq_loop ?p ?q |- _ => eapply H; rewrite Q; eapply loop_contains_self;eauto
         | H : eq_loop ?p ?q,
               Q : ~ loop_contains _ ?q |- _ => rewrite <-H in Q; contradiction
         | _ : loop_head ?q,
               H : ~ loop_contains ?q ?p,
                   _ : ~ a_edge__P ?p ?q |- _
           => eapply H; specialize (back_edge_eq_loop (p:=p) (h:=q)) as Q;
               exploit Q;[firstorder|rewrite Q;eapply loop_contains_self;eauto]
         | _ => idtac
         end.
 *)
  Admitted.

  Lemma edge_Edge : forall (p q : Lab), edge__P p q -> Edge p q.
  Proof.
    intros ? ? Hedge.
    decide (deq_loop p q).
    - decide (deq_loop q p).
      + decide (a_edge__P p q).
        * econstructor;eauto;split;eauto;split;eauto.
        * eapply Eback. refine (conj Hedge n).
      + eapply Eexit.
        simpl_dec' n. simpl_dec' n. destructH.
        exists x. split;eauto.
    - eapply Eentry.
      unfold entry_edge. split_conj;eauto.
      + simpl_dec' n. simpl_dec' n. destructH.
        enough (x = q).
        * subst. eapply loop_contains_loop_head;eauto.
        * eapply dom_loop_contains in n1 as Hdom;eauto.
          specialize (PathSingle edge__P p) as Hpath.
          eapply PathCons in Hedge;eauto.
          eapply Hdom in Hedge. destruct Hedge;subst;auto.
          exfalso. cbn in H; destruct H;[|auto]. subst.
          eapply n1. eapply loop_contains_self;eapply loop_contains_loop_head;eauto.
      + contradict n. eapply loop_contains_deq_loop;auto.
  Defined.

  Lemma Edge_eq (p q : Lab)
        (H : edge__P p q)
        (Q : edge__P p q)
    : edge_Edge H = edge_Edge Q.
  Proof.
    erewrite Edge_disj. reflexivity.
  Qed.

  (** * The edge relation on the tagged CFG **)

  Definition STag (i : Tag)
    := match i with
       | nil => nil
       | n :: i => (S n) :: i
       end.

  Definition eff_tag' (p q : Lab) (i : Tag) (E : edge__P p q)
    := match edge_Edge E with
       | Enormal _ => i
       | Eback _ => STag i
       | Eentry _ => 0 :: i
       | Eexit _ => tl i
       end.

  Definition eff_tag (p q : Lab) (i : Tag)
    := match decision (edge__P p q) with
       | left E => Some (eff_tag' i E)
       | _ => None
       end.

  Lemma eff_tag'_eq (i : Tag) (p q : Lab) (H Q : edge__P p q)
    : eff_tag' i H = eff_tag' i Q.
  Proof.
    unfold eff_tag'.
    erewrite Edge_eq.
    reflexivity.
  Qed.

  (*
  Definition eff_tag p q i : Tag
    := if decision (p ↪ q)
       then match i with
            | nil => nil
            | n :: l => (S n) :: l
            end
       else
         if decision (exists h, exit_edge h p q) then
           tl i
         else
           if decision (loop_head q) then
             O :: i
           else
             i.
   *)

  Definition tcfg_edge (c c' : Coord) :=
    let (p,i) := c  in
    let (q,j) := c' in
    edge__P p q /\ eff_tag p q i = Some j.

  Hint Unfold Coord tcfg_edge.

  Notation "pi -t> qj" := (tcfg_edge pi qj) (at level 50).
  (*Notation "pi -t> qj" := ((fun `(redCFG) => tcfg_edge pi qj = true) _ _ _ _ _)
                          (at level 50).*)

  (** ** Basic facts **)

  Global Instance tcfg_edge_dec : forall pi qj, dec (pi -t> qj).
  Proof.
    intros. destruct pi as [p i]. destruct qj as [q j].
    cbn. decide (edge__P p q);eauto.
  Qed.

  Lemma tcfg_edge_spec (p q : Lab) i j
    : (p,i) -t> (q,j) <-> edge p q = true /\ eff_tag p q i = Some j.
  Proof.
    reflexivity.
  Qed.

  Hint Resolve tcfg_edge_spec.

  Lemma tag_eff p i q j
        (Hpq : (p,i) -t> (q,j))
    : exists (Hedge : edge__P p q),  eff_tag' i Hedge = j.
  Proof.
    unfold tcfg_edge,eff_tag in Hpq.
    destructH.
    decide (edge__P p q);[|congruence].
    unfold eff_tag'. inversion Hpq1. eexists. erewrite Edge_eq. reflexivity.
    Unshelve. eauto.
  Qed.

    Lemma cons_neq (A : Type) (l : list A) (a : A)
    : l = a :: l -> False.
    Proof.
      induction l;intros;[congruence|].
      inversion H. subst. eauto.
    Qed.

  Lemma STag_neq_cons n i
    : STag i = n :: i -> False.
  Proof.
    induction i;intros;cbn in *;[congruence|].
    inversion H. eapply cons_neq;eauto.
  Qed.

  Lemma tl_neq_cons (A : Type) (a : A) (l : list A)
    : tl l = a :: l -> False.
  Proof.
    revert a. induction l;intros;[cbn in *;congruence|].
    eapply IHl. cbn in H. rewrite H at 1. cbn. reflexivity.
  Qed.

  Section eff_tag_facts.
    Variables (p q : Lab) (i j : Tag).
    Hypothesis (Hpq : (p,i) -t> (q,j)).

    Ltac tag_fact_prep := eapply tag_eff in Hpq as Hpq'; destructH; subst j; clear Hpq.

    Lemma tag_exit_iff
      : match get_innermost_loop p with
        | Some h => exit_edge h p q
        | None => False
        end -> j = tl i.
    Proof.
      destruct (get_innermost_loop p);[|contradiction].
      tag_fact_prep.
      intro H.
      apply ex_intro with (x:=e) in H.
      specialize (Edge_disj (Eexit H) (edge_Edge Hedge)) as Hdj.
      unfold eff_tag'.
      rewrite <-Hdj.
      reflexivity.
    Qed.

    (* TODO : change name *)
    Lemma tag_exit_iff'
      : (exists h, exit_edge h p q) -> j = tl i.
    Proof.
      intro H.
      - eapply tag_exit_iff. specialize (get_innermost_loop_spec p) as E.
        destruct (get_innermost_loop p).
        + destructH.
          split;eauto. 1: unfold innermost_loop in E; destructH; auto.
          split;eauto. 2: eapply tcfg_edge_spec;eauto.
          unfold exit_edge in H. destructH. intro Hl.
          eapply innermost_loop_deq_loop in E;eauto.
        + destructH. eapply E. unfold exit_edge in H; destructH. eauto.
    Qed.

    Lemma tag_exit_eq h
      : exit_edge h p q -> j = tl i.
    Proof.
      intros. eapply tag_exit_iff';eauto.
    Qed.

    Lemma tag_exit_lt
          (Hgt : |j| < |i|)
      : j = tl i.
    Proof.
      tag_fact_prep.
      unfold eff_tag' in *. destruct (edge_Edge Hedge). 4:auto.
      all: exfalso;try lia.
      - destruct i;cbn in *;lia.
      - cbn in *;lia.
    Qed.

    Lemma tag_entry_lt
          (Hlt : |i| < |j|)
      : j = O :: i.
    Proof.
      tag_fact_prep.
      unfold eff_tag' in *. destruct (edge_Edge Hedge). 3:auto.
      all: exfalso;try lia.
      - destruct i;cbn in *;lia.
      - destruct i;cbn in *;lia.
    Qed.

    (* possibly unused
    Lemma tag_normal_iff
      : j = i <-> eq_loop p q.
    Proof.
     *)

    Ltac tag_fact_s1 H Hedge :=
      unfold eff_tag' in *; destruct (edge_Edge Hedge) in H;auto;exfalso;
      eauto using cons_neq, STag_neq_cons, tl_neq_cons.

    Ltac tag_fact_s2 H Q :=
      let Hdj := fresh "Hdj" in
      specialize (Edge_disj H Q) as Hdj;
      unfold eff_tag';
      rewrite <-Hdj;
      reflexivity.

    Lemma tag_entry_iff
      : j = O :: i <-> entry_edge p q.
    Proof.
      tag_fact_prep.
      split;intro H.
      - tag_fact_s1 H Hedge.
      - tag_fact_s2 (Eentry H) (edge_Edge Hedge).
    Qed.

    Lemma tag_back_edge
      : p ↪ q -> j = STag i.
    Proof.
      tag_fact_prep.
      intro H.
      tag_fact_s2 (Eback H) (edge_Edge Hedge).
    Qed.

    Lemma tag_back_edge_iff n
          (Hpq' : (p,n :: i) -t> (q,j))
      : j = STag (n :: i) <-> p ↪ q.
    Proof.
      clear Hpq.
      rename Hpq' into Hpq.
      tag_fact_prep.
      split;intro H.
      - tag_fact_s1 H Hedge.
        cbn in H. inversion H. lia.
      - tag_fact_s2 (Eback H) (edge_Edge Hedge).
    Qed.

    (* possibly not used
    Lemma tag_deq_le
      : |i| <= |j| <-> deq_loop q p.
    Proof.

    Lemma tag_deq_ge
      : |i| >= |j| <-> deq_loop p q.
    Proof.

    Lemma tag_deq_total
      : deq_loop p q \/ deq_loop q p.
    Proof.
      specialize (Nat.le_ge_cases (|i|) (|j|)) as Hcases.
      destruct Hcases;[right|left].
      - eapply tag_deq_le;auto.
      - eapply tag_deq_ge;auto.
    Qed.
     *)

    Lemma tag_deq_or_entry
      : deq_loop p q \/ entry_edge p q.
    Proof.
      tag_fact_prep.
      eapply edge_Edge in Hedge.
      destruct Hedge;eauto.
      - left. destruct b. destruct H. auto.
      - eapply back_edge_eq_loop in b. left. eapply b.
      - unfold eexit_edge in e. destructH. left. eapply deq_loop_exited;eauto.
    Qed.

    Lemma tcfg_edge_destruct'
      : (j = i /\ basic_edge p q)
        \/ (j = O :: i /\ entry_edge p q)
        \/ (j = STag i /\ back_edge p q)
        \/ (j = tl i /\ eexit_edge p q).
    Proof.
      tag_fact_prep.
      unfold eff_tag'.
      destruct (edge_Edge Hedge).
      Local Ltac tcfg_dstr_tac
        := match goal with
           | |- ?P \/ ?Q => match P with
                         | context [?x = ?x] => left; tcfg_dstr_tac
                         | _ => right; tcfg_dstr_tac
                         end
           | |- ?P /\ ?Q => split;eauto
           end.
      all: tcfg_dstr_tac.
    Qed.

    Lemma tcfg_edge_destruct
      : i = j (* normal *)
        \/ j = O :: i (* entry *)
        \/ j = STag i (* back *)
        \/ j = tl i. (* exit *)
    Proof.
      unfold tcfg_edge in Hpq. destructH. unfold eff_tag in Hpq1.
      decide (edge__P p q);[|congruence]. inversion Hpq1. unfold eff_tag'.
      destruct (edge_Edge e);firstorder 0.
    Qed.

  End eff_tag_facts.

  Lemma STag_len i
    : | STag i | = | i |.
  Proof.
    destruct i;cbn;eauto.
  Qed.

  Definition TPath := Path tcfg_edge.

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

  (** * Depth of a node equals Tag length **)

  (** ** Lemmas **)

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

  Lemma set_eq_NoDup_len (A : Type) (l l' : list A)
        (Heq : l =' l')
        (Hnd : NoDup l)
        (Hnd' : NoDup l')
    : | l | = | l' |.
  Proof.
    destruct Heq.
    eapply Nat.le_antisymm;eapply NoDup_incl_length;eauto.
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

  Lemma tag_depth'  p i t
        (Hpath : TPath (root,start_tag) (p,i) t)
    : length i = depth p.
  Proof.
    revert p i Hpath.
    induction t;intros;[inversion Hpath|].
    destruct a as [q j].
    unfold TPath in Hpath. path_simpl' Hpath.
    inversion Hpath;subst t a;[subst i p|subst c]. clear H3.
    - rewrite depth_root. cbn. reflexivity.
    - destruct b. eapply tcfg_edge_destruct' in H3.
      destruct H3 as [[H Q]|[[H Q]|[[H Q]|[H Q]]]].
      all: rewrite H;cbn.
      3: rewrite STag_len; eapply back_edge_eq_loop in Q.
      1: destruct Q as [Q _].
      1,3: setoid_rewrite <-Q;eauto.
      + erewrite <-depth_entry;eauto.
      + eapply eq_add_S.
        erewrite <-depth_exit;eauto.
        destruct t.
        * exfalso. clear - H0 Q IHt. unfold eexit_edge in Q. destructH.
          eapply IHt in H0. cbn in H0. eapply eq_loop_exiting in Q as Q'.
          rewrite <-Q' in H0.
          unfold exit_edge in Q. destructH.
          eapply loop_contains_loop_head in Q0. eapply depth_loop_head in Q0. lia.
        * erewrite <-IHt;eauto. cbn. reflexivity.
  Qed.

  (** ** Theorem **)

  Lemma tag_depth  p i q j t
        (Hpath : TPath (root,start_tag) (p,i) t)
        (Hin : (q,j) ∈ t)
    : length j = depth q.
  Proof.
    eapply path_to_elem in Hpath;eauto. destructH.
    eapply tag_depth';eauto.
  Qed.

  Lemma STag_inj (i j : Tag)
        (Heq : STag i = STag j)
    : i = j.
  Proof.
    destruct i,j; cbn in *;eauto;congruence.
  Qed.

Lemma tag_eq_loop_exit p q i j j'
      (Htag : (q,j ) -t> (p,i))
      (Htag': (q,j') -t> (p,i))
      (Hneq : j <> j')
  : match (get_innermost_loop q) with
    | Some h => exit_edge h q p
    | None => False
    end.
Proof.
  unfold tcfg_edge,eff_tag in Htag,Htag'.
  do 2 destructH.
  decide (edge__P q p);[|congruence].
  unfold eff_tag' in *.
  inversion Htag1. inversion Htag'1. clear Htag1 Htag'1.
  destruct (edge_Edge e);subst.
  - contradiction.
  - eapply STag_inj in H1. subst j. contradiction.
  - inversion H1. subst. contradiction.
  - unfold eexit_edge in e0. destructH.
    specialize (get_innermost_loop_spec q) as Himl.
    destruct (get_innermost_loop q).
    + replace e1 with h;eauto. eapply single_exit;eauto. unfold innermost_loop in Himl. destructH.
      unfold exit_edge. split_conj;eauto.
      specialize (exit_not_deq e0) as Q. contradict Q. eapply loop_contains_deq_loop in Q.
      rewrite Q. rewrite Himl1. eapply eq_loop_exiting;eauto.
    + eapply Himl. unfold exit_edge in e0. destructH. eauto.
Qed.

(** * Monotonicity & Freshness of tags **)

(** ** Lemmas **)

Lemma TPath_CPath  c c' π :
  TPath c c' π -> CPath (fst c) (fst c') (map fst π).
Proof.
  intros Q. dependent induction Q; [|destruct b,c]; econstructor; cbn in *.
  - apply IHQ.
  - conv_bool. firstorder.
Qed.

Lemma p_p_ex_head' (p q : Lab) π ϕ
      (Hpath : CPath p q π)
      (Hdeq : forall x, x ∈ π -> deq_loop p x)
      (Hacy : APath q p ϕ)
      (Hlen : | π | >= 2)
  : exists h, h ∈ π /\ forall x, x ∈ π -> loop_contains h x.
Proof.
  (* by induction on π:
   * * if nil,singleton: contradiction
   * * if doubleton: easy style: h=q, bc of APath p-->q must be a back_edge, thus loop_contains q p
   * * else:
   * * edge distinction for ? --> q:
   *   * if back_edge then: we have found h
   *   * otw. IH
   *)
Admitted.

Lemma p_p_ex_head (p : Lab) π
      (Hpath : CPath p p π)
      (Hlen : | π | >= 2)
  : exists h, h ∈ π /\ forall x, x ∈ π -> loop_contains h x.
Proof.
  (* implode π wrt. p then Hdeq of p_p_ex_head' holds and the conclusion is extendable from there *)
  eapply p_p_ex_head';eauto.
  - admit.
  - econstructor.
Admitted.

Lemma take_len_id (A : Type) (l : list A)
  : take (|l|) l = l.
Proof.
  induction l;cbn;eauto.
  rewrite IHl;eauto.
Qed.

Lemma take_r_len_id (A : Type) (l : list A)
  : take_r (|l|) l = l.
Proof.
  unfold take_r. eapply rev_rev_eq. rewrite rev_involutive.
  rewrite <-rev_length. eapply take_len_id.
Qed.

Definition ancestor' a p q := deq_loop p a /\ deq_loop q a.

Lemma ancestor_ancestor' a p q
  : ancestor a p q -> ancestor' a p q.
  intros. unfold ancestor',ancestor in *. destruct H.
  - destruct H. split;eauto using loop_contains_deq_loop.
  - subst. split;eapply deq_loop_root.
Qed.

Lemma tagle_prefix i j
      (Hpre : Prefix i j)
  : i ⊴ j.
Proof.
  eapply prefix_eq in Hpre. destructH. subst j.
  induction l2'.
  - cbn. reflexivity.
  - cbn. eapply Tagle_cons. eauto.
Qed.

Lemma take_postfix (A : Type) (l : list A) n
  : Postfix (take n l) l.
Proof.
  eapply postfix_eq.
  revert l.
  induction n;intros;cbn.
  - eexists;eauto.
  - destruct l;cbn.
    + econstructor;eauto.
    + specialize (IHn l). destructH. eexists. f_equal. eauto.
Qed.

Lemma take_r_prefix (A : Type) (l : list A) n
  : Prefix (take_r n l) l.
Proof.
  eapply postfix_rev_prefix'.
  unfold take_r. rewrite rev_involutive.
  eapply take_postfix.
Qed.

Global Instance ancestor'_sym : forall a, Symmetric (ancestor' a).
Proof.
  intros.
  econstructor;unfold ancestor' in *;destructH;eauto.
Qed.

Global Instance ancestor'_eq_loop a p
  : Proper (eq_loop ==> Basics.impl) (ancestor' a p).
Proof.
  econstructor;unfold ancestor' in *;destructH;eauto.
  destruct H. transitivity x;auto.
Qed.

Lemma take_r_nil (A : Type) n
  : @take_r A n [] = [].
Proof.
  unfold take_r. cbn. rewrite take_nil. cbn. auto.
Qed.
Notation "x ◁ y" := (x ⊴ y /\ x <> y) (at level 70).

Lemma tagle_or i j
      (Htag : i ⊴ j)
  : |i| <= |j| \/ i ◁ j.
Proof.
  induction Htag;cbn.
  - left. lia.
  - destruct IHHtag.
    + left. do 2 rewrite app_length. cbn. lia.
    + right. econstructor.
      * econstructor;eauto.
      * destruct H. contradict H0. eapply rcons_eq1. eauto.
  - right. econstructor.
    + econstructor;eauto.
    + intro N. eapply rcons_eq2 in N. lia.
Qed.

Lemma take_rcons_ex (A : Type) n (l : list A)
      (Hlen : S n <= |l|)
  : exists a, take (S n) l = take n l ++[a].
Proof.
  revert l Hlen.
  induction n;intros.
  - cbn. destruct l;[cbn in Hlen;lia|].
    eexists;eauto.
  - destruct l;[cbn in Hlen;lia|].
    rewrite take_one. 2: lia.
    replace (S (S n) - 1) with (S n) by lia.
    rewrite take_one. 2: lia.
    replace (S n - 1) with n by lia.
    specialize (IHn l). exploit IHn.
    + cbn in Hlen. lia.
    + destructH. rewrite IHn. eexists;cbn;eauto.
Qed.

Lemma take_r_cons_ex (A : Type) n (l : list A)
      (Hlen : S n <= |l|)
  : exists a, take_r (S n) l = a :: take_r n l.
Proof.
  rewrite <-rev_length in Hlen.
  specialize (take_rcons_ex Hlen) as H. destructH.
  eexists. unfold take_r. rewrite <-rev_rcons.
  rewrite <-rev_rev_eq. eauto.
Qed.

Lemma taglt_eq i j
      (Htlt : i ◁ j)
      (Hlen : |i| = |j|)
  : exists k0 k1 k2 n1 n2, i = k1 ++ n1 :: k0 /\ j = k2 ++ n2 :: k0 /\ n1 < n2.
Proof.
  destruct Htlt. induction H.
  - cbn in *. symmetry in Hlen. eapply length_zero_iff_nil in Hlen. subst. contradiction.
  - exploit IHTagle.
    + contradict H0. subst. reflexivity.
    + do 2 rewrite app_length in Hlen. clear - Hlen. lia.
    + destructH. do 5 eexists. split_conj;[| |eauto].
      1,2: rewrite <-cons_rcons_assoc; rewrite app_assoc; f_equal; eauto.
  - do 5 eexists. split_conj;[| |eauto].
    1,2: reflexivity.
Qed.

Lemma tagle_app_app i j k
  : i ⊴ j -> i ++ k ⊴ j ++ k.
Proof.
  revert i j. induction k;intros;cbn;eauto.
  - do 2 rewrite <-app_nil_end. eauto.
  - rewrite app_cons_assoc. setoid_rewrite app_cons_assoc at 2.
    eapply IHk. eapply Tagle_rcons;eauto.
Qed.

Lemma taglt_cons i j n m
      (Hlen : |i| = |j|)
      (Htlt : i ◁ j)
  : n :: i ◁ m :: j.
Proof.
  eapply taglt_eq in Htlt;eauto.
  destructH. subst i j.
  split.
  - rewrite app_cons_assoc. setoid_rewrite app_cons_assoc at 2.
    do 4 rewrite app_comm_cons.
    eapply tagle_app_app.
    econstructor;eauto.
  - intro N. inversion N. subst.
    rewrite app_cons_assoc in H1. setoid_rewrite app_cons_assoc in H1 at 2.
    eapply app_inv_tail in H1.
    eapply rcons_eq2 in H1. subst. lia.
Qed.

Lemma taglt_tagle i j
      (Htlt : i ◁ j)
  : i ⊴ j.
Proof.
  firstorder.
Qed.

Lemma tagle_taglt_iff i j
  : i ⊴ j <-> i ◁ j \/ i = j.
Proof.
  split;intros.
  - decide (i = j);[right|left];eauto.
  - destruct H.
    + destruct H;eauto.
    + subst. reflexivity.
Qed.

Notation "p '>=' q" := (deq_loop p q).

Lemma tl_len (A : Type) (l : list A)
  : |tl l| = |l| - 1.
Proof.
  induction l;cbn;eauto. lia.
Qed.

Lemma take_rcons_drop (A : Type) (l : list A) n a
      (Hle : n <= | l |)
  : take n (l ++[a]) = take n l.
Proof.
  revert l Hle.
  induction n;[cbn;eauto|];intros.
  rewrite rcons_cons'.
  cbn.
  destruct l;cbn.
  - cbn in Hle. lia.
  - cbn in Hle.
    f_equal. eapply IHn. lia.
Qed.

Lemma take_r_drop (A : Type) (l : list A) n a
      (Hle : n <= | l |)
  : take_r n (a :: l) = take_r n l.
Proof.
  unfold take_r.
  rewrite rev_cons. rewrite take_rcons_drop.
  - reflexivity.
  - rewrite rev_length. auto.
Qed.

Lemma take_r_tl_eq (A : Type) (l : list A)
  : tl l = take_r (|l| - 1) l.
Proof.
  rewrite <- tl_len.
  destruct l;eauto. unfold tl in *.
  rewrite take_r_drop;[|eauto].
  rewrite take_r_len_id. reflexivity.
Qed.

Lemma tagle_take_r (i j : Tag) (n : nat)
      (Htgl : i ⊴ take_r n j)
  : i ⊴ j.
Proof.
  rewrite Htgl. eapply prefix_tagle. eapply take_r_prefix.
Qed.

Lemma take_r_rcons (A : Type) (l : list A) n a
  : take_r (S n) (l :r: a) = take_r n l :r: a.
Proof.
  unfold take_r.
  rewrite <-rev_cons.
  rewrite <-rev_rev_eq.
  rewrite rev_rcons.
  rewrite take_one;[|lia].
  cbn.
  replace (n - 0) with n by lia.
  reflexivity.
Qed.

Lemma tagle_take_r_leq (i j : Tag) (n : nat)
      (Hleq : |i| <= n)
      (Htgl : i ⊴ j)
  : i ⊴ take_r n j.
Proof.
  revert n Hleq.
  induction Htgl;intros;cbn.
  - econstructor.
  - rewrite app_length in Hleq. cbn in Hleq.
    destruct n0.
    { exfalso. lia. }
    rewrite take_r_rcons.
    econstructor.
    eapply IHHtgl. lia.
  - destruct n0.
    { exfalso. rewrite app_length in Hleq. cbn in Hleq. lia. }
    rewrite take_r_rcons.
    econstructor;eauto.
Qed.

Lemma tagle_STag (i : Tag)
  : i ⊴ STag i.
Proof.
  induction i;cbn;eauto.
  - reflexivity.
  - eapply Tagle_cons2. lia.
Qed.

Lemma take_r_len_leq (A : Type) (l : list A) n
  : |take_r n l| <= n.
Proof.
  unfold take_r.
  rewrite rev_length.
  rewrite take_length.
  eapply Nat.le_min_r.
Qed.

(** ** Weak monotonicity **)

Lemma tcfg_monotone' p i t q j t' h
      (Hpath : TPath (root,start_tag) (p,i) t)
      (Hsuff : Postfix t' t)
      (Hel : (q,j) ∈ t')
      (Hincl : forall r k, (r,k) ∈ t' -> loop_contains h r)
  : take_r (depth h) j ⊴ i.
Proof.
  eapply postfix_eq in Hsuff. destructH. subst t.
  revert p i Hpath Hel Hincl. induction t';intros. 1: contradiction. inversion Hpath.
  - subst p i a0. destruct t'.
    + cbn in H4. subst l2' a. destruct Hel;[|contradiction]. inversion H. subst q j.
      rewrite take_r_nil. econstructor.
    + exfalso. cbn in H4. congruence.
  - subst a a0 c π. destruct b as [p' i'].
    destruct Hel as [Hel|Hel].
    { inversion Hel. subst. eapply tagle_prefix. eapply take_r_prefix. }
    eapply tcfg_edge_destruct' in H4. destruct H4 as [Q|[Q|[Q|Q]]]. all: destruct Q as [Htag Hedge].
    + rewrite <-Htag in *.
      rewrite IHt'. 2:eauto. all:eauto. reflexivity.
    + rewrite Htag in *. rewrite IHt'. 2:eauto. all:eauto. eapply Tagle_cons. reflexivity.
    + subst i. rewrite IHt'. 2:eauto. all:eauto.
      eapply tagle_STag.
    + subst i.
      rewrite take_r_tl_eq. eapply tagle_take_r_leq;cycle 1.
      * eapply IHt'. eauto. all:eauto.
      * rewrite <-tl_len.
        setoid_rewrite tag_depth at 2.
        -- rewrite take_r_len_leq.
           eapply deq_loop_depth.
           eapply loop_contains_deq_loop.
           eapply Hincl. left;eauto.
        -- eapply Hpath.
        -- left;eauto.
Qed.

Lemma splinter_strict_suffix (L : Type) `{EqDec L eq} (e: L -> L -> Prop) x y z π
      (Hpath : Path e x y π)
      (Hsp : splinter_strict [y;z] π)
  : exists ϕ, Path e z y ϕ /\ Postfix ϕ π /\ 2 <= |ϕ|.
Proof.
  inversion Hpath;subst.
  - exfalso. inversion Hsp;subst. inversion H1. inversion H2.
  - assert (z ∈ π0) as Hel.
    + inversion Hsp;subst;eapply splinter_strict_incl;eauto.
    + eapply path_from_elem in Hel;eauto.
      destructH. exists (y :: ϕ). split_conj.
      * econstructor;eauto.
      * eapply postfix_cons;eauto.
      * destruct ϕ;[inversion Hel0|]. cbn. lia.
Qed.

Require Import GetSucc.


Lemma taglt_tagle_trans (i j k : Tag)
  : i ◁ j -> j ⊴ k -> i ◁ k.
Proof.
  intros. split;[destruct H;transitivity j;eauto|].
  destruct H.
  contradict H1. subst i.
  eapply antisymmetry;eauto.
Qed.

Lemma tagle_nil_eq (i : Tag)
  : i ⊴ [] -> i = [].
Proof.
  intros. inversion H;subst;eauto;try congruence'.
Qed.

Lemma tagle_taglt_trans (i j k : Tag)
  : i ⊴ j -> j ◁ k -> i ◁ k.
Proof.
  intros. split;[destruct H0;transitivity j;eauto|].
  destruct H0.
  contradict H1. subst i.
  eapply antisymmetry;eauto.
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

Lemma filter_nil (A : Type) (f : decPred A) l
      (Hnil : filter f l = [])
  : forall x, x ∈ l -> ~ f x.
Proof.
  induction l;intros;cbn.
  - contradiction.
  - destruct H;subst.
    + cbn in Hnil. decide (f x);[congruence|auto].
    + eapply IHl;eauto. cbn in Hnil. decide (f a);[congruence|auto].
Qed.

Lemma loop_contains_depth_lt h p
      (Hloop : loop_contains h p)
  : depth p > 0.
Proof.
  unfold depth.
  match goal with |- length ?x > 0 => enough (x <> []) end.
  - enough (depth p <> 0). 1:unfold depth in *;lia.
    contradict H.
    eapply length_zero_iff_nil. eauto.
  - intro N. eapply filter_nil;eauto.
Qed.

Lemma tcfg_head_taglt h q j k t
      (Hloop : loop_head h)
      (Hpath : TPath (root,start_tag) (q,j) t)
      (Hedge : (q,j) -t> (h,k))
  : j ◁ k.
Proof.
  eapply tcfg_edge_destruct' in Hedge. destruct Hedge as [Q|[Q|[Q|Q]]].
  all: destruct Q as [Heq Hedge];subst.
  1,4:exfalso.
  - eapply basic_edge_no_loop2;eauto.
  - unfold eexit_edge in Hedge. destructH. eapply no_exit_head;eauto.
  - split.
    + eapply Tagle_cons. reflexivity.
    + intro N. eapply cons_neq;eauto.
  - destruct j.
    + exfalso. eapply loop_contains_ledge in Hedge.
      eapply tag_depth' in Hpath. cbn in Hpath.
      eapply loop_contains_depth_lt in Hedge. lia.
    + cbn. split;[eapply tagle_STag|intro N;inversion N]. lia.
Qed.

Lemma postfix_eq_app (A : Type) (l l' : list A)
  : Postfix l (l ++ l').
Proof.
  induction l;cbn.
  - eapply postfix_nil.
  - eapply postfix_cons. auto.
Qed.

(** ** Freshness **)

Lemma tcfg_fresh p i t
      (Hpath : TPath (root,start_tag) (p,i) t)
      (Hsp : splinter_strict [(p,i);(p,i)] t)
  : False.
Proof.
  eapply splinter_strict_suffix in Hsp;eauto.
  destructH.
  copy Hsp0 Hpath'.
  eapply TPath_CPath in Hsp0. cbn in Hsp0.
  eapply p_p_ex_head in Hsp0;eauto.
  2: { rewrite map_length. lia. }
  destructH.
  (* destruct ϕ *)
  destr_r' ϕ. all: subst ϕ. 1:cbn in Hsp3;lia.
  destruct l. 1: cbn in Hsp3; lia.
  path_simpl' Hpath'. cbn in Hpath'. path_simpl' Hpath'. rename x into y.
  let tac Q :=
      rewrite map_rcons in Q;rewrite map_cons in Q;unfold fst in Q at 1 3
                             in tac Hsp1; tac Hsp4.
  (* some ridiculous simplifications *)
  assert (forall z, z ∈ ((p :: map fst l :r: p)) <-> z ∈ (p :: map fst l)) as H2cons.
  { clear. intros. cbn. setoid_rewrite In_rcons. firstorder. }
  rewrite H2cons in Hsp1. setoid_rewrite H2cons in Hsp4.
  remember (find (fun y => decision (fst y = h)) ((p,i) :: l)) as x. symmetry in Heqx.
  destruct x;cycle 1. (* show the existence of such x *)
  { fold (fst (p,i)) in Hsp1. rewrite <-map_cons in Hsp1.
    eapply in_fst in Hsp1. destructH. eapply find_none in Heqx. 2:eapply Hsp1. cbn in Heqx.
    decide (h = h);inversion Heqx. contradiction. }
  eapply find_some in Heqx. destructH.
  destruct p1 as [e k]. cbn in Heqx1. decide (e = h);[|inversion Heqx1].
  subst e. clear Heqx1.
  remember (get_pred (h,k) (p,i) ((p,i) :: l)) as rj.
  destruct rj as [r j].
  specialize (get_pred_cons (p,i) Heqx0) as Hsucc.
  rewrite <-Heqrj in Hsucc. copy Hsp2 Hsp2'.
  eapply postfix_eq in Hsp2. destructH.
  assert (TPath (root,start_tag) (p,i) ((p,i)::l2')) as Hpath0.
  { eapply path_prefix_path. 2: eapply Hpath. 1:eauto. eapply prefix_eq.
    eexists;eauto. rewrite <-app_assoc in Hsp2. eauto. }
  eapply path_to_elem in Hpath' as Hpath_r.
  2: { cbn. right. eapply in_succ_in2. cbn in Hsucc;eauto. }
  destructH.
  eapply path_app' in Hpath_r0 as Hpath_r'. 2: eapply Hpath0.
  assert (take_r (depth h) i ⊴ j) as Hij.
  {
    eapply tcfg_monotone'.
    instantiate (2 := r).
    - eapply Hpath_r'.
    - instantiate (1:=ϕ).
      eapply postfix_eq_app.
    - eapply path_contains_back;eauto.
    - intros. eapply Hsp4. eapply H2cons.
      eapply prefix_incl in H;eauto.
      eapply in_map with (f:=fst) in H. cbn in H. rewrite map_rcons in H. cbn in H.
      cbn;eauto.
  }
  assert (j ◁ k) as Hjk. {
    eapply tcfg_head_taglt.
    - eapply loop_contains_loop_head. eapply Hsp4. left. auto.
    - eapply Hpath_r'.
    - eapply succ_in_path_edge; cycle 1;eauto.
  }
  assert (k = take_r (depth h) k) as Hkeq.
  {
    replace (depth h) with (|k|). 1:symmetry;eapply take_r_len_id.
    eapply tag_depth. 1: eapply Hpath. eapply postfix_incl;eauto.
  }
  assert (take_r (depth h) k ⊴ take_r (depth h) i) as Hki.
  {
    eapply tagle_take_r_leq. 1: eapply take_r_len_leq.
    eapply tcfg_monotone'. 1: eapply Hpath. 1:eauto.
    - eapply in_succ_in1;eauto.
    - intros. eapply Hsp4.
      eapply H2cons.
      eapply in_map with (f:=fst) in H. cbn in H. rewrite map_rcons in H. cbn in H.
      cbn;eauto.
  }
  rewrite <-Hkeq in Hki.
  eapply tagle_taglt_trans in Hjk;eauto.
  eapply taglt_tagle_trans in Hjk;eauto.
  destruct Hjk. eapply H0. reflexivity.
Qed.

(* TODO: move ex_entry proof to this point. it does not require any assumptions,
thus it should be possible *)
Lemma tcfg_fresh_head' h p i k t
      (Hpath : TPath (root,start_tag) (h,0::k) t)
      (Hloop : loop_contains h p)
      (Hsp : splinter_strict [(h,0::k);(p,i)] t)
      (Hpre : Prefix k i)
  : False.
  (*
   * find entry of h corresponding to (p,i) in t with tag 0::k', where Prefix k' i.
   * bc freshness we have 0::k <> 0::k', thus bc |k|=|k'| also k <> k' cntrdiction.
   *)
Admitted.

Lemma take_r_leq_id (A : Type) (l : list A) n
      (Hlen : |l| <= n)
  : take_r n l = l.
Proof.
  unfold take_r.
  rewrite take_eq_ge.
  - rewrite rev_involutive. reflexivity.
  - rewrite rev_length. lia.
Qed.

(** ** Strong monotonicity **)

Lemma tcfg_monotone p i t q j a
      (Hpath : TPath (root,start_tag) (p,i) t)
      (Hel : (q,j) ∈ t)
      (Hdeqp : p >= a)
      (Hdeqq : q >= a)
  : take_r (depth a) j ⊴ i.
Proof.
  revert p i q j a Hpath Hel Hdeqp Hdeqq. induction t;intros;inversion Hpath.
  - symmetry in H1,H2. subst. destruct Hel as [Hel|Hel];inversion Hel. subst q j.
    rewrite take_r_nil. econstructor.
  - subst. destruct b as [p' i'].
    destruct Hel as [Hel|Hel].
    { inversion Hel. subst. eapply tagle_prefix. eapply take_r_prefix. }
    eapply tcfg_edge_destruct' in H4. destruct H4 as [Q|[Q|[Q|Q]]].
    1-4:destruct Q as [Htag Hedge].
    +
      rewrite <-Htag in *.
      rewrite IHt;eauto.
      * reflexivity.
      * destruct Hedge as [[Hedge _] _]. transitivity p;eauto.
    + decide (eq_loop a0 p).
      * specialize (IHt _ _ _ _ p' H3 Hel). exploit IHt. 1: reflexivity.
        { transitivity p.
          - rewrite <-e. eauto.
          - eapply deq_loop_entry;eauto.
        }
        subst i. rewrite e.
        setoid_rewrite <-depth_entry;eauto.
        destruct j.
        -- rewrite take_r_nil. econstructor.
        -- copy IHt IHt'.
           eapply tagle_taglt_iff in IHt.
           destruct IHt.
           ++ assert (depth p' = |i'|) as Hpieq.
              { symmetry. eapply tag_depth';eauto. }
              rewrite Hpieq in *.
              decide (|n :: j| <= |i'|).
              ** rewrite take_r_leq_id. 2: lia.
                 eapply Tagle_cons. rewrite take_r_leq_id in IHt'. 2: lia. eauto.
              ** assert (S (|i'|) <= |n :: j|) as n1. 1: clear - n0;lia.
                 specialize (take_r_cons_ex n1) as Q. destructH' Q. rewrite Q.
                 eapply taglt_tagle. eapply taglt_cons. 2:eauto.
                 unfold take_r. rewrite rev_length,take_length,rev_length.
                 clear - n1. rewrite Nat.min_r. auto. lia.
           ++ exfalso.
              eapply tcfg_fresh_head'.
              ** cbn in Hpath. eapply Hpath.
              ** instantiate (1:=q).
                 eapply deq_loop_head_loop_contains.
                 --- rewrite <-e. eauto.
                 --- destruct Hedge. auto.
              ** econstructor. eapply splinter_strict_single;eauto.
              ** rewrite <- H. eapply take_r_prefix.
              (* contradiction to freshness:
               * find an acyclic path from p' to q, then argue it has the same tag prefix as q
               * contradiction to strict freshness *)
              (* there should be a contradiction somewhere along these lines:
               * deq_loop q p, thus there is an acyclic path from p' to q.
               * thus there is header containing p' on q --> q, well,
               * and then we need stuff from the freshness proof sketch,
               * looks like this induction scheme is broken *)
              (**)
      * rewrite Htag in *.
        rewrite IHt;eauto.
        eapply Tagle_cons. reflexivity.
        -- simpl_dec' n. destruct n;try contradiction.
           intros h' Hh'.
           eapply deq_loop_entry_or in Hedge.
           ++ destruct Hedge;eauto. subst. exfalso. clear - H Hh'. eauto using loop_contains_deq_loop.
           ++ eapply Hdeqp in Hh'. eauto.
    + rewrite Htag in *.
      rewrite IHt. 2,3,5:eauto.
      * eapply tagle_STag.
      * eapply back_edge_eq_loop in Hedge. destruct Hedge. transitivity p;eauto.
    + subst i.
      rewrite take_r_tl_eq. eapply tagle_take_r_leq;cycle 1.
      * eapply IHt. eauto. all:eauto. transitivity p;eauto. destruct Hedge.
        eapply deq_loop_exited;eauto.
      * rewrite <-tl_len.
        setoid_rewrite tag_depth at 2.
        -- rewrite take_r_len_leq.
           eapply deq_loop_depth.
           exact Hdeqp.
        -- eapply Hpath.
        -- left;eauto.
Qed.

(** ** Corollaries **)

Lemma tcfg_monotone_deq p q i j t
      (Hdeq : deq_loop p q)
      (Hpath : TPath (root, start_tag) (p, i) t)
      (Hel : (q,j) ∈ t)
  : j ⊴ i.
Proof.
  eapply tcfg_monotone in Hpath as Hmon;eauto. 2:reflexivity.
  erewrite <-tag_depth in Hmon;eauto.
  rewrite take_r_len_id in Hmon. eauto.
Qed.

Lemma eff_tag_unfresh q j t p
      (Hpath : TPath (root,start_tag) (q,j) t)
      (Hedge : edge__P q p)
      (Hel : (p,eff_tag' j Hedge) ∈ t)
  : False.
Proof.
  set (j':=eff_tag' j Hedge) in *.
  eapply PathCons with (edge:=tcfg_edge) in Hpath;cycle 1.
  - instantiate (1:=(p,j')). split;eauto. subst j'. unfold eff_tag.
    decide (edge__P q p);[|contradiction].
    erewrite eff_tag'_eq. reflexivity.
  - eapply tcfg_fresh;eauto.
    econstructor. eapply splinter_strict_single;eauto.
Qed.

Lemma eff_tag_fresh : forall p q i j l,
    TPath (root,start_tag) (q,j) l -> eff_tag q p j = Some i -> forall i', In (p, i') l -> i' <> i.
Proof.
  intros ? ? ? ? ? Hpath Heff ? Hel Heq.
  unfold eff_tag in Heff. decide (edge__P q p);[|congruence].
  subst i'. inversion Heff. subst i.
  eapply eff_tag_unfresh;eauto.
Qed.

Lemma eff_tag_det : forall  q j p i i',
    eff_tag q p j = i ->
    eff_tag q p j = i' ->
    i = i'.
Proof.
  intros. rewrite <-H, <-H0. reflexivity.
Qed.

Lemma eff_tag_det'
  : forall (q : Lab) (j : Tag) (p : Lab) (i i' : Tag),
    eff_tag q p j = Some i -> eff_tag q p j = Some i' -> i = i'.
Proof.
  intros.
  eapply eff_tag_det in H;eauto. inversion H;eauto.
Qed.

Lemma tpath_succ_eff_tag  p q r i j s t a l
      (Hpath : TPath (a,l) (r,s) ((r,s) :: t))
      (Hsucc : (q,j) ≻ (p,i) | (r,s) :: t)
  : eff_tag p q i = Some j.
Proof.
  unfold succ_in in Hsucc. destructH.
  assert ((r,s) :: t = l2 :r: (q,j) :r: (p,i) ++ l1) as Hsucc'.
  {
    rewrite Hsucc.
    do 2 rewrite app_cons_assoc. reflexivity.
  }
  rewrite Hsucc' in Hpath.
  eapply postfix_path with (l:=l2 :r: (q,j)) (p:=(p,i)) in Hpath.
  - eapply path_prefix_path with (ϕ:= [(p,i)]) (r:=(q,j))in Hpath.
    + inversion Hpath;subst;eauto. unfold tcfg_edge in H3. cbn in H3. destruct b. conv_bool.
      inversion H0;subst. destruct H3. eauto. inversion H5.
    + eauto.
    + cbn; clear. induction l2; cbn in *; econstructor; eauto.
  - cbn; clear. induction l2; cbn; destruct l1; cbn; eauto using postfix_cons.
    1,2: repeat (eapply postfix_cons; try econstructor). eapply postfix_nil.
Qed.

(** ** Tagged paths are duplicate-free **)

Lemma tpath_NoDup q t
      (Hpath : TPath (root,start_tag) q t)
  : NoDup t.
Proof.
  revert q Hpath. induction t.
  - econstructor; eauto.
  - intros. unfold TPath in Hpath. path_simpl' Hpath.
    econstructor.
    + intro. inversion Hpath; subst; cbn in H; [contradiction|].
      destruct q. destruct b. eapply eff_tag_fresh;eauto. destruct H4. eauto.
    + inversion Hpath; subst;[econstructor|]. destruct b, q.
      eapply IHt;eauto.
Qed.

(** * Lemmas about TCFGs **)

Lemma exit_edge_tcfg_edge (h p q : Lab) (j : Tag)
      (Hexit : exit_edge h q p)
  : (q,j) -t> (p,tl j).
Proof.
  cbn. copy Hexit Hexit'.
  unfold exit_edge in Hexit. destructH.
  split;auto.
  unfold eff_tag. decide (edge__P q p);[|contradiction].
  f_equal.
  unfold eff_tag'.
  destruct (edge_Edge e);auto.
  all: exfalso.
  - eapply Hexit2. unfold basic_edge in b. destructH. rewrite <-b0. auto.
  - eapply back_edge_eq_loop in b. destruct b. eapply Hexit2. eauto.
  - eapply deq_loop_entry in e0. eapply Hexit2. eauto.
Qed.

(* possibly unused
Lemma exit_succ_exiting (p q h e : Lab) (k i j : Tag) r
      (Hpath : TPath (p,k) (q,j) (r :r: (p,k)))
      (Hexit : exited h e)
      (Hel : (e,i) ∈ r)
  : exists qe n, exit_edge h qe e /\ (e,i) ≻ (qe,n :: i) | r :r: (p,k).
Proof.
*)

  Lemma prec_tpath_pre_tpath p i q j l
        (Hneq : p <> q)
        (Htr : TPath (root,start_tag) (p,i) ((p, i) :: l))
        (Hprec : Precedes fst l (q, j))
    : exists l', TPath (root,start_tag) (q,j) ((q,j) :: l') /\ Prefix ((q,j) :: l') ((p,i) :: l).
  Proof.
    eapply path_to_elem with (r:= (q,j)) in Htr.
    - destructH. exists (tl ϕ).
      assert (ϕ = (q,j) :: tl ϕ) as ϕeq.
      { inversion Htr0;subst a;cbn;eauto. }
      split;eauto.
      + rewrite ϕeq in Htr0;eauto.
      + rewrite ϕeq in Htr1;eauto.
    - eapply precedes_in. econstructor;eauto;cbn;eauto.
  Qed.

  Lemma prec_tpath_tpath p i q j l
        (Htr : TPath (root,start_tag) (p,i) ((p, i) :: l))
        (Hprec : Precedes fst ((p,i) :: l) (q, j))
    : exists l', TPath (root,start_tag) (q,j) ((q,j) :: l').
  Proof.
    inversion Hprec;subst.
    - firstorder.
    - eapply prec_tpath_pre_tpath in Htr;eauto. destructH. eauto.
  Qed.

  Lemma precedes_fst_same_tag {A B : Type} `{EqDec B} (p : A) (i j : B) l
        (Hprec1 : Precedes fst l (p,i))
        (Hprec2 : Precedes fst l (p,j))
    : i = j.
  Proof.
    clear edge root a_edge C.
    dependent induction Hprec1.
    - inversion Hprec2;subst;[reflexivity|]. cbn in H2; contradiction.
    - inversion Hprec2;subst.
      + cbn in H0;contradiction.
      + eapply IHHprec1;eauto.
  Qed.

  Lemma tpath_tag_len_eq p j1 j2 l1 l2
        (Hpath1 : TPath (root, start_tag) (p, j1) l1)
        (Hpath2 : TPath (root, start_tag) (p, j2) l2)
    : length j1 = length j2.
  Proof.
    eapply tag_depth' in Hpath1.
    eapply tag_depth' in Hpath2.
    rewrite Hpath1,Hpath2. reflexivity.
  Qed.

  Lemma tpath_tag_len_eq_elem p q i1 i2 j1 j2 l1 l2
        (Hpath1 : TPath (root, start_tag) (p, i1) l1)
        (Hpath2 : TPath (root, start_tag) (p, i2) l2)
        (Hin1 : (q,j1) ∈ l1)
        (Hin2 : (q,j2) ∈ l2)
    : length j1 = length j2.
  Proof.
    eapply path_to_elem in Hin1;eauto.
    eapply path_to_elem in Hin2;eauto.
    do 2 destructH.
    eapply tpath_tag_len_eq in Hin0;eauto.
  Qed.

  Lemma dom_tpath_prec p q i l
        (Hdom : Dom edge__P root q p)
        (Hpath : TPath (root,start_tag) (p,i) l)
    : exists j, Precedes fst l (q,j).
  Proof.
    (* FIXME *)
  Admitted.

  Lemma tag_prefix_head h p i j l
        (Hloop : loop_contains h p)
        (Hpath : TPath (root, start_tag) (p,i) l)
        (Hprec : Precedes fst l (h,j))
    : Prefix j i.
  Proof.
  Admitted. (* FIXME *)

  Lemma root_tag_nil p i j l
        (HPath : TPath (root,start_tag) (p,i) l)
        (Hin : (root,j) ∈ l)
    : j = nil.
  Proof.
    revert dependent p. revert i.
    induction l;intros.
    - inversion HPath. (*subst a0 p i a. cbn in Hin. destruct Hin;[|contradiction].
      inversion H;subst. eauto.*)
    - destruct a. cbn in Hin.
      destruct Hin.
      + inversion H. subst. inversion HPath.
        * reflexivity.
        * exfalso.
          subst a c p i π. destruct b.
          eapply root_no_pred. eapply tcfg_edge_spec; eauto.
      + inversion HPath.
        * subst l. contradiction.
        * destruct b. eapply IHl;eauto.
  Qed.

  Lemma tag_prefix_ancestor a p q i j l
        (Hanc : ancestor a p q)
        (Hpath : TPath (root, start_tag) (p,i) l)
        (Hprec : Precedes fst l (a,j))
    : Prefix j i.
  Proof.
    unfold ancestor in Hanc.
    destruct Hanc as [[Hanc _]|Hanc]; [eapply tag_prefix_head|subst a];eauto.
    replace j with (@nil nat);[eapply prefix_nil|].
    symmetry; eapply root_tag_nil;eauto using precedes_in.
  Qed.

  Hint Unfold Coord.

  Lemma tag_prefix_ancestor_elem a p q r i j k l
        (Hanc : ancestor a p q)
        (Hpath : TPath (root,start_tag) (r,k) ((r,k) :: l))
        (Hprec : Precedes fst ((r,k) :: l) (a,j))
        (Hib : (p,i) ≻* (a,j) | (r,k) :: l)
    : Prefix j i.
  Proof.
    eapply splinter_in in Hib as Hin.
    eapply path_to_elem in Hin;eauto. destructH.
    decide (i = j).
    { subst. reflexivity. }
    eapply tag_prefix_ancestor;eauto.
    eapply path_contains_front in Hin0 as Hfront.
    eapply tpath_NoDup in Hin0.
    eapply tpath_NoDup in Hpath.
    clear - Hprec Hib Hin1 Hpath Hin0 n Hfront. set (l' := (r,k) :: l) in *.
    eapply prefix_eq in Hin1. destructH.
    revert dependent l'. revert dependent ϕ. induction l2';intros.
    - cbn in Hin1. rewrite Hin1 in Hprec. eauto.
    - destruct l'. 1: inversion Hprec.
      inversion Hin1.
      eapply IHl2'. 6:eauto. 1,2:eauto.
      + inversion Hpath. subst. eauto.
      + inversion Hprec;subst.
        * exfalso.
          inversion Hib; subst. 1: contradiction.
          inversion Hpath. subst.
          eapply splinter_cons in H1. eapply splinter_in in H1. contradiction.
        * eauto.
      + subst. clear Hin1. inversion Hib;subst.
        * exfalso.
          inversion Hpath;subst.
          eapply H2.
          eapply in_or_app. right;auto.
        * eauto.
  Qed.

  Lemma first_occ_tag j j1 j2 p t
        (Htag : j = j1 ++ j2)
        (Hpath : TPath (root,start_tag) (p,j) t)
    : exists h, loop_contains h p /\ Precedes fst t (h,j2).
  Proof.
    (* FIXME *)
  Admitted.

  Lemma first_occ_tag_elem i j j1 j2 p q t
        (Htag : j = j1 ++ j2)
        (Hpath : TPath (root,start_tag) (p,i) t)
        (Hin : (q,j) ∈ t)
    : exists h, loop_contains h q /\ Precedes fst t (h,j2) /\ (q,j) ≻* (h, j2) | t.
  Proof.
    eapply path_to_elem in Hpath;eauto. destructH.
    eapply first_occ_tag in Hpath0;eauto. destructH.
    (* FIXME *)
  Admitted.

  (* possibly not used *)
  Lemma prec_prec_eq l (q : Lab) (j j' : Tag)
        (Hprec1 : Precedes fst l (q,j))
        (Hprec2 : Precedes fst l (q,j'))
    : j = j'.
  Proof.
  Admitted.

  (* possibly not used *)
  Lemma prefix_prec_prec_eq l l' (p q : Lab) (i j j' : Tag)
        (Hpre : Prefix ((p,i) :: l') l)
        (Hprec1 : Precedes fst l (q,j))
        (Hprec2 : Precedes fst ((p,i) :: l') (q,j'))
        (Hnd : NoDup l)
        (Hib : (p,i) ≻* (q,j) | l)
    : j' = j.
  Proof.
  Admitted.

  (* possibly not used *)
  Lemma ancestor_in_before_dominating a p q (i j k : Tag) l
        (Hdom : Dom edge__P root q p)
        (Hanc : ancestor a q p)
        (Hprec__a: Precedes fst ((p,i) :: l) (a,k))
        (Hprec__q: Precedes fst ((p,i) :: l) (q,j))
    : (q,j) ≻* (a,k) | (p,i) :: l.
  Proof.
  Admitted.

  Lemma ancestor_level_connector p q a i j k t
        (Hpath : TPath (root,start_tag) (p,i) t)
        (Hin : (q,j) ∈ t)
        (Hanc  : near_ancestor a p q)
        (Hprec : Precedes fst t (a,k))
        (Hib : (q,j) ≻* (a,k) | t)
    : exists a', Precedes fst t (a',k) /\ (p,i) ≻* (a',k) ≻* (q,j) | t.
  Proof.
    (* FIXME *)
  Admitted.

  Lemma find_loop_exit h a p i j k n l
        (Hpath : TPath (root,start_tag) (p,i) l)
        (Hpre : Prefix k j)
        (Hib : (a,k) ≻* (h, n :: j) | l)
        (Hprec : Precedes fst l (h, n :: j))
    : exists qe e, (a,k) ≻* (e,j) ≻* (qe,n :: j) ≻* (h, n :: j) | l /\ (e,j) ≻ (qe,n :: j) | l /\ exit_edge h qe e.
  Proof.
    (* FIXME *)
  Admitted.

  Lemma tpath_deq_loop_prefix p q i j t x l y m
        (Hdeq : deq_loop p q)
        (Hpath : TPath (x,l) (y,m) t)
        (Hpre : Prefix j i)
    : (q,j) ≻* (p,i) | t.
  Proof.
     (* FIXME *)
  Admitted.

  Hint Resolve precedes_in.

  Lemma dom_dom_in_between  (p q r : Lab) (i j k : Tag) l
        (Hdom1 : Dom edge__P root r q)
        (Hdom2 : Dom edge__P root q p)
        (Hprec : Precedes fst ((p,i) :: l) (q,j))
        (Hin : (r,k) ∈ ((p,i) :: l))
        (Hpath : TPath (root,start_tag) (p,i) ((p,i) :: l))
    : (q,j) ≻* (r,k) | (p,i) :: l.
  Proof.
    (* FIXME *)
  Admitted.

  Lemma loop_cutting q p t
        (Hpath : CPath q p t)
        (Hnoh : forall h, loop_contains h q -> h ∉ t)
    : exists t', Path a_edge__P q p t'.
  Proof.
    (* FIXME *)
  Admitted.

  Lemma tpath_exit_nin h q e n j t
        (Hpath : TPath (root, start_tag) (q,n :: j) t)
        (Hloop : loop_contains h q)
        (Hexit : exited h e)
    : (e,j) ∉ t.
  Proof.
    intro N.
    unfold exited in Hexit. destructH.
    unfold exit_edge in Hexit. destructH.
    eapply PathCons in Hexit3;eauto. cycle 1.
  Admitted. (* FIXME *)

  Lemma loop_cutting_elem q p t i j x l
        (Hpath : TPath (x,l) (p,i) ((p,i) :: t))
        (Hib : (p,i) ≻* (q,j) | (p,i) :: t)
        (Hnoh : forall h k, loop_contains h q -> ~ (p,i) ≻* (h,k) ≻* (q,j) | (p,i) :: t)
    : exists t', Path a_edge__P q p t'.
  Proof.
    (* FIXME *)
  Admitted.

  Lemma exit_cascade u p t i j k x l
        (Hdom : Dom edge__P root u p)
        (Hprec : Precedes fst ((p,i) :: t) (u,j))
        (Hpath : TPath (x,l) (p,i) ((p,i) :: t))
    : forall h, loop_contains h u -> ~ (p,i) ≻* (h,k) ≻* (u,j) | (p,i) :: t.
    (* otw. there would be a path through this q to p without visiting u *)
    (* this could even be generalized to CPaths *)
    (* TODO: lift on tpaths, on cpaths we might have duplicates, thus it doesn't work there *)
  Proof. (* FIXME *)
  Admitted.

  Lemma tpath_depth_eq (p q : Lab) (i j : Tag) pi qj t
        (Hpath : TPath pi qj t)
        (Hel1 : (p,i) ∈ t)
        (Hel2 : (q,j) ∈ t)
        (Heq : |i| = |j|)
    : depth p = depth q.
  Proof.
    (* FIXME *)
  Admitted.

  Lemma tpath_depth_lt (p q : Lab) (i j : Tag) pi qj t
        (Hpath : TPath pi qj t)
        (Hel1 : (p,i) ∈ t)
        (Hel2 : (q,j) ∈ t)
        (Hlt : |i| < |j|)
    : depth p < depth q.
  Proof.
    (* FIXME *)
  Admitted.

  Lemma loop_tag_dom (h p : Lab) (i j : Tag) t
    (Hloop : loop_contains h p)
    (Hpath : TPath (root,start_tag) (p,i) t)
    (Htagle : j ⊴ i)
    (Hdep : |j| = depth h)
    : (h,j) ∈ t.
  Proof.
    eapply dom_loop in Hloop as Hdom.
    eapply TPath_CPath in Hpath as Hpath'. cbn in Hpath'.
    eapply Hdom in Hpath'.
    (* FIXME *)
  Admitted.

  Lemma loop_tag_prec (h p : Lab) (i j : Tag) t
    (Hloop : loop_contains h p)
    (Hpath : TPath (root,start_tag) (p,i) t)
    (Htagle : j ⊴ i)
    (Hdep : |j| = depth h)
    : Precedes fst t (h,j).
  Proof.
  Admitted.

  Lemma deq_loop_le p i j q t t'
        (Hdeq : deq_loop p q)
        (Hpath : TPath (root,start_tag) (p,i) t)
        (Hpath' : TPath (root,start_tag) (q,j) t')
    : |j| <= |i|.
  Proof.
    eapply tag_depth in Hpath as Hdep'. 2: eapply path_contains_front;eauto.
    eapply tag_depth in Hpath' as Hdep. 2: eapply path_contains_front;eauto.
    rewrite Hdep, Hdep'.
    eapply deq_loop_depth;auto.
  Qed.

  (* not true !
  Lemma tagle_monotone p q i j t
    (Hpath : TPath (root,start_tag) (p,i) t)
    (Hel : (q,j) ∈ t)
    (Hlen : |j| <= |i|)
    : j ⊴ i.
  Proof.
    (* FIXME *)
  Admitted.
   *)

End tagged.
