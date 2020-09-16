Require Export TcfgEdge.
Require Import Lia.

Section cfg.
  Context `{C : redCFG}.

  Notation "pi -t> qj" := (tcfg_edge pi qj) (at level 50).

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

  (** ** relation between tag length and depth **)

  Lemma tag_depth  p i q j t
        (Hpath : TPath (root,start_tag) (p,i) t)
        (Hin : (q,j) ∈ t)
    : length j = depth q.
  Proof.
    eapply path_to_elem in Hpath;eauto. destructH.
    eapply tag_depth';eauto.
  Qed.

  Lemma tcfg_reach p i
        (Hlen : | i | = depth p)
    : exists t, TPath (root,start_tag) (p,i) t.
  Admitted.

  Lemma tag_depth_path p i q j t
        (Hlen : | i | = depth p)
        (Hpath : TPath (p,i) (q,j) t)
    : | j | = depth q.
  Proof.
    eapply tcfg_reach in Hlen.
    destructH.
    eapply path_app' in Hpath;eauto.
    eapply tag_depth';eauto.
  Qed.

  Lemma tag_depth_edge p i q j
        (Hedge : (p,i) -t> (q,j))
    : | i | = depth p <-> | j | = depth q.
  Proof.
    eapply tcfg_edge_destruct' in Hedge.
    destruct Hedge as [[H Q]|[[H Q]|[[H Q]|[H Q]]]].
    all: admit. (* TODO: I need depth edge lemmas *)
  Admitted.

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
    inversion Htag1. inversion Htag'1. clear Htag1 Htag'1.
    destruct (edge_Edge e);subst.
    - inversion H0. inversion H1. subst. contradiction.
    - destruct j;[congruence|]. destruct j';[congruence|].
      inversion H0. inversion H1. subst. inversion H3. subst. contradiction.
    - inversion H1. subst. inversion H0. contradiction.
    - unfold eexit_edge in e0. destructH.
      specialize (get_innermost_loop_spec q) as Himl.
      destruct (get_innermost_loop q).
      + replace e1 with h;eauto. eapply single_exit;eauto. unfold innermost_loop in Himl. destructH.
        unfold exit_edge. split_conj;eauto.
        specialize (exit_not_deq e0) as Q. contradict Q. eapply loop_contains_deq_loop in Q.
        rewrite Q. rewrite Himl1. eapply eq_loop_exiting;eauto.
      + eapply Himl. unfold exit_edge in e0. destructH. eauto.
  Qed.

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

  Lemma tcfg_edge_exit_nil p q j
        (Hedge : tcfg_edge (p,[]) (q,j))
        (Hexit : eexit_edge p q)
    : False.
  Proof.
    destruct Hedge. unfold eff_tag in H0.
    decide (edge__P p q).
    2: contradiction.
    eapply depth_exit in Hexit.
    destruct (edge_Edge e).
    - eapply depth_basic in b. lia.
    - congruence.
    - eapply depth_entry in e0. lia.
    - congruence.
  Qed.

  Lemma tcfg_edge_back_nil p q j
        (Hedge : tcfg_edge (p,[]) (q,j))
        (Hback : back_edge p q)
    : False.
  Proof.
    destruct Hedge. unfold eff_tag in H0.
    decide (edge__P p q).
    2: contradiction.
    eapply depth_back in Hback as Hdep.
    destruct (edge_Edge e).
    - destruct b. destruct Hback. contradiction.
    - congruence.
    - eapply depth_entry in e0. lia.
    - congruence.
  Qed.

  Lemma tcfg_edge_depth_iff p q i j
        (Hedge : tcfg_edge (p,i) (q,j))
    : | i | = depth p <-> | j | = depth q.
  Proof.
    specialize (tcfg_edge_destruct' Hedge) as Hd.
    destruct Hd as [Hd|[Hd|[Hd|Hd]]].
    all: destructH.
    - subst. eapply basic_edge_eq_loop in Hd1. rewrite Hd1. reflexivity.
    - subst. eapply depth_entry in Hd1. rewrite <-Hd1. cbn.
      split;lia.
    - eapply back_edge_eq_loop in Hd1 as Hd2. rewrite Hd2. subst.
      destruct i.
      + exfalso.
        eapply tcfg_edge_back_nil;eauto.
      + cbn. lia.
    - eapply depth_exit in Hd1 as Hd2. rewrite Hd2. subst.
      destruct i.
      + exfalso. eapply tcfg_edge_exit_nil;eauto.
      + cbn. lia.
  Qed.

  (** ** p p ex head **)

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

  (** ** Lemmas with take_r **)

  Lemma taglt_take_r_taglt i j n
        (Hlt : take_r n i ◁ take_r n j)
        (Hlen : | i | = | j |)
    : i ◁ j.
  Proof.
    remember (|i| - n) as m.
    revert n i j Hlt Hlen Heqm.
    induction m;intros.
    - do 2 (rewrite take_r_geq in Hlt;[|lia]). auto.
    - destruct i;[cbn in Heqm;lia|].
      destruct j;[cbn in Hlen;lia|].
      econstructor.
      cbn in Hlen. replace (|n0 :: i|) with (S (|i|)) in Heqm by (cbn;auto).
      eapply IHm;auto.
      + do 2 (rewrite take_r_cons_drop in Hlt;[|lia]).
        eassumption.
      + lia.
  Qed.

  Lemma tagle_neq_taglt (i j : Tag)
    : i ⊴ j -> i <> j -> i ◁ j.
  Proof.
    intros. destruct H;[assumption|contradiction].
  Qed.

  Lemma tagle_take_r i j n
        (Htagle : i ⊴ j)
    : take_r n i ⊴ take_r n j.
  Proof.
    destruct Htagle.
    - induction H.
      + decide (n <= |i|).
        * erewrite take_r_cons_replace;eauto. reflexivity.
        * rewrite take_r_geq. 2: cbn;lia.
          rewrite take_r_geq. 2: cbn;lia.
          left. econstructor;eauto.
      + decide (n <= |i|).
        * do 2 (rewrite take_r_cons_drop;eauto).
          erewrite <-Taglt_len;eauto.
        * do 2 (rewrite take_r_geq;[|cbn;try lia]).
          2: erewrite <-Taglt_len;eauto;lia.
          left.
          econstructor;eauto.
    - subst. reflexivity.
  Qed.

  Lemma taglt_leq i j m n
        (Htaglt : take_r m j ◁ take_r m i)
        (Hleq : m <= n)
        (Hleni : n <= |i|)
        (Hlenj : n <= |j|)
    : take_r n j ◁ take_r n i.
  Proof.
    eapply taglt_take_r_taglt.
    - do 2 (rewrite take_r_take_r_leq;eauto).
    - decide (n <= |i|).
      + do 2 (rewrite take_r_length_le;[|auto;lia]). reflexivity.
      + do 2 (rewrite take_r_length_ge;[|auto;lia]). lia.
  Qed.

  Lemma taglt_cons i j n
    : n :: i ◁ n :: j <-> i ◁ j.
  Proof.
    split.
    - intros. inv H.
      + lia.
      + auto.
    - intros. econstructor. auto.
  Qed.

  Lemma taglt_tagle (i j : Tag)
    : i ◁ j -> i ⊴ j.
  Proof.
    intros. left. auto.
  Qed.

End cfg.
