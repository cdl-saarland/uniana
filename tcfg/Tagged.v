Require Export ImplodeCFG Precedes CFGancestor Tagle.

Require Import PropExtensionality.
  

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
    all: lazymatch goal with
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
  Qed.   

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

    Lemma tag_exit_lt
          (Hgt : |j| < |i|)
      : j = tl i.
    Proof.
      tag_fact_prep. 
      unfold eff_tag' in *. destruct (edge_Edge Hedge). 4:auto.
      all: exfalso;try omega.
      - destruct i;cbn in *;omega.
      - cbn in *;omega.
    Qed.

    Lemma tag_entry_lt
          (Hlt : |i| < |j|)
      : j = O :: i.
    Proof.
      tag_fact_prep.
      unfold eff_tag' in *. destruct (edge_Edge Hedge). 3:auto.
      all: exfalso;try omega.
      - destruct i;cbn in *;omega.
      - destruct i;cbn in *;omega.
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
        cbn in H. inversion H. omega.
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
      + cbn in N. omega.
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
          eapply loop_contains_loop_head in Q0. eapply depth_loop_head in Q0. omega.
        * erewrite <-IHt;eauto. cbn. reflexivity.
  Qed.        
    
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

Lemma eff_tag_unfresh q j t p
      (Hpath : TPath (root,start_tag) (q,j) t)
      (Hedge : edge__P q p)
      (Hel : (p,eff_tag' j Hedge) ∈ t)
  : False.
Proof.
  set (j':=eff_tag' j Hedge) in *.
  eapply path_from_elem in Hel;eauto. destructH.
  assert ((q,j) -t> (p,j')) as Hedge'.
  { split;eauto. subst j'. unfold eff_tag. decide (edge__P q p);[|congruence]. f_equal.
    eapply eff_tag'_eq. }
  eapply PathCons in Hedge';eauto.
  eapply TPath_CPath in Hedge' as HCpath. cbn in HCpath.
  eapply p_p_ex_head in HCpath. 2:{ destruct ϕ;[inversion Hel0|]. cbn. clear. omega. }
  destructH.
Admitted.

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
    (* FIXME *)
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

  Lemma tagle_monotone p q i j t
    (Hpath : TPath (root,start_tag) (p,i) t)
    (Hel : (q,j) ∈ t)
    (Hlen : |j| <= |i|)
    : j ⊴ i.
  Proof.
    (* FIXME *)
  Admitted.
  
End tagged.
