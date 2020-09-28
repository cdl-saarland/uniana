Require Export Tcfg CFGinnermost.
Require Import Lia.

(** ** STag **)

Definition STag (i : Tag)
  := match i with
     | nil => nil
     | n :: i => (S n) :: i
     end.

Lemma STag_len i
  : | STag i | = | i |.
Proof.
  destruct i;cbn;eauto.
Qed.

Lemma STag_inj (i j : Tag)
      (Heq : STag i = STag j)
  : i = j.
Proof.
  destruct i,j; cbn in *;eauto;congruence.
Qed.

Lemma taglt_stag n (i : Tag)
  : n :: i ◁ STag (n :: i).
Proof.
  cbn. econstructor. auto.
Qed.

Section eff_tag_facts.
  Context `{C : redCFG}.
  Notation "pi -t> qj" := (tcfg_edge pi qj) (at level 50).
  Variables (p q : Lab) (i j : Tag).
  Hypothesis (Hpq : (p,i) -t> (q,j)).

  (*    Ltac tag_fact_prep := eapply tag_eff in Hpq as Hpq'; destructH; subst j; clear Hpq.*)

  Lemma tag_exit_iff
    : match get_innermost_loop p with
      | Some h => exit_edge h p q
      | None => False
      end -> j = tl i.
  Proof.
    destruct (get_innermost_loop p);[|contradiction].
    intro Hexit.
    destruct Hpq as [Hedge Htag].
    unfold eff_tag in Htag.
    decide (edge__P p q);[|congruence].
    destruct (edge_Edge e0);try edge_excl.
    destruct i;[congruence|]. cbn. inv Htag.
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
    destruct Hpq as [Hedge Htag].
    unfold eff_tag in Htag.
    decide (edge__P p q);[|congruence].
    destruct (edge_Edge e);inv Htag.
    all:try lia.
    - destruct i;[congruence|]. cbn in *. inv H0. cbn in *. lia.
    - cbn in *. lia.
    - destruct i;[congruence|]. cbn. inv H0. reflexivity.
  Qed.

  Ltac prep :=
    destruct Hpq as [Hedge Htag];
    unfold eff_tag in Htag;
    decide (edge__P p q);[|congruence].

  Lemma tag_entry_lt
        (Hlt : |i| < |j|)
    : j = O :: i.
  Proof.
    prep.
    destruct (edge_Edge e);inv Htag.
    all:try lia.
    - destruct i;[congruence|]. inv H0. cbn in Hlt. lia.
    - reflexivity.
    - destruct i;[congruence|]. inv H0. cbn in Hlt. lia.
  Qed.

  Lemma tag_entry_iff
    : j = O :: i <-> entry_edge p q.
  Proof.
    split; intro Q.
    - prep.
      destruct (edge_Edge e);inv Htag.
      all: try (now (exfalso;eapply list_cycle;eauto)).
      + destruct i;[congruence|]. admit. (* this is not true in general! *)


  Admitted. (*
      tag_fact_prep.
      split;intro H.
      - tag_fact_s1 H Hedge.
      - tag_fact_s2 (Eentry H) (edge_Edge Hedge).
    Qed. *)

  Lemma tag_back_edge
    : p ↪ q -> j = STag i.
  Proof.
  Admitted. (*
      tag_fact_prep.
      intro H.
      tag_fact_s2 (Eback H) (edge_Edge Hedge).
    Qed.*)

  Lemma tag_back_edge_iff n
        (Hpq' : (p,n :: i) -t> (q,j))
    : j = STag (n :: i) <-> p ↪ q.
  Proof.
    clear Hpq.
    rename Hpq' into Hpq.
  Admitted. (*
      tag_fact_prep.
      split;intro H.
      - tag_fact_s1 H Hedge.
        cbn in H. inversion H. lia.
      - tag_fact_s2 (Eback H) (edge_Edge Hedge).
    Qed. *)

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
  Admitted. (*
      tag_fact_prep.
      eapply edge_Edge in Hedge.
      destruct Hedge;eauto.
      - left. destruct b. destruct H. auto.
      - eapply back_edge_eq_loop in b. left. eapply b.
      - unfold eexit_edge in e. destructH. left. eapply deq_loop_exited;eauto.
    Qed.
             *)

  Lemma tcfg_edge_destruct'
    : (j = i /\ basic_edge p q)
      \/ (j = O :: i /\ entry_edge p q)
      \/ (j = STag i /\ back_edge p q)
      \/ (j = tl i /\ eexit_edge p q).
  Proof.
  Admitted. (*
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
             *)

  Lemma tcfg_edge_destruct
    : i = j (* normal *)
      \/ j = O :: i (* entry *)
      \/ j = STag i (* back *)
      \/ j = tl i. (* exit *)
  Proof.
    unfold tcfg_edge in Hpq. destructH. unfold eff_tag in Hpq1.
    decide (edge__P p q);[|congruence]. inversion Hpq1.
  Admitted. (*
      destruct (edge_Edge e);firstorder 0.
    Qed. *)

End eff_tag_facts.

Section cfg.
  Context `(C : redCFG).
  Notation "pi -t> qj" := (tcfg_edge pi qj) (at level 50).

  Lemma tcfg_basic_edge p q i
        (H : basic_edge p q)
    : (p,i) -t> (q,i).
  Proof.
    copy H H'.
    destruct H.
    eapply a_edge_incl in H0.
    split;eauto.
    unfold eff_tag.
    decide (edge__P p q);[|contradiction].
    destruct (edge_Edge e);eauto.
    all:exfalso;edge_excl.
  Qed.

  Lemma tcfg_back_edge p q n i
        (H : back_edge p q)
    : (p, n :: i) -t> (q, S n :: i).
  Proof.
    copy H H'.
    destruct H.
    split;eauto.
    unfold eff_tag.
    decide (edge__P p q);[|contradiction].
    destruct (edge_Edge e);eauto.
    all:exfalso;edge_excl.
  Qed.

  Lemma tcfg_entry_edge p q i
        (H : entry_edge p q)
    : (p,i) -t> (q, 0 :: i).
  Proof.
    copy H H'.
    destruct H.
    destructH.
    split;eauto.
    unfold eff_tag.
    decide (edge__P p q);[|contradiction].
    destruct (edge_Edge e);eauto.
    all:exfalso;edge_excl.
  Qed.

  Lemma tcfg_exit_edge p q i n
        (H : eexit_edge p q)
    : (p,n :: i) -t> (q, i).
  Proof.
    copy H H'.
    destruct H.
    destruct H. destructH.
    split;eauto.
    unfold eff_tag.
    decide (edge__P p q);[|contradiction].
    destruct (edge_Edge e);eauto.
    all:exfalso;edge_excl.
  Qed.

  Lemma tag_exit_eq' h p q i j
        (Hedge : (p,i) -t> (q,j))
        (Hexit : exit_edge h p q)
    : exists n, i = n :: j.
  Proof.
    destruct Hedge.
    unfold eff_tag in H0.
    decide (edge__P p q);[|congruence].
    destruct (edge_Edge e);try edge_excl.
    destruct i.
    - exfalso.
      congruence.
    - inv H0. eexists; reflexivity.
  Qed.

  Lemma tcfg_edge_edge (q p : Lab) (i j : Tag)
        (Hedge : (q,j) -t> (p,i))
    : edge__P q p.
  Proof.
    destruct Hedge. auto.
  Qed.

  Lemma no_entry_STag (i j : Tag)
    : 0 :: i <> STag j.
  Proof.
    destruct j;cbn;congruence.
  Qed.

  Lemma tcfg_edge_eq_loop q1 q2 j p i
        (Hedge1 : (q1,j) -t> (p,i))
        (Hedge2 : (q2,j) -t> (p,i))
    : eq_loop q1 q2.
  Proof.
    copy Hedge1 Htedge1.
    copy Hedge2 Htedge2.
    eapply tcfg_edge_destruct' in Hedge1.
    eapply tcfg_edge_destruct' in Hedge2.
    destruct Hedge1 as [Hedge1|[Hedge1|[Hedge1|Hedge1]]].
    all: destruct Hedge2 as [Hedge2|[Hedge2|[Hedge2|Hedge2]]].
    all: destruct Hedge1 as [Htag1 Hedge1].
    all: destruct Hedge2 as [Htag2 Hedge2].
    all: repeat
            lazymatch goal with
            | H : basic_edge _ _ |- _ => eapply basic_edge_eq_loop in H
            | H : back_edge _ _ |- _ => eapply back_edge_eq_loop in H
            end.
    all: lazymatch goal with
         | H : eq_loop _ _, Q : eq_loop _ _ |- _ => try (rewrite Hedge1,Hedge2;eauto;try reflexivity)
         | _ => idtac
         end.
    all: subst i.
    all: unfold eexit_edge in *; repeat destructH.
    all: try lazymatch goal with
             | H: exit_edge _ _ _ |- _ => eapply tag_exit_eq' in H as Hexit;eauto;destructH
             end.
    all: lazymatch goal with
         | H : _ :: ?x = ?x |- _
           => eapply list_cycle in H;contradiction
         | H : ?x = _ :: ?x |- _
           => symmetry in H; eapply list_cycle in H;contradiction
         | _ => idtac
         end.
    all: lazymatch goal with
         | H : 0 :: _ = STag _ |- _
           => eapply no_entry_STag in H;contradiction
         | H : STag _ = 0 :: _ |- _
           => symmetry in H; eapply no_entry_STag in H;contradiction
         | _ => idtac
         end.
    all: lazymatch goal with
         | H : eq_loop _ _, Q : exit_edge _ _ _ |- _
           => eapply exit_not_deq in Q;
               [contradiction|eapply exit_pred_loop in Q;
                              [eapply loop_contains_deq_loop in Q;eapply eq_loop1;eauto
                              |eapply tcfg_edge_edge;eauto]]
         | _ => idtac
         end.
    2: exfalso;eapply list_cycle2;cbn in *;eauto.
    2: exfalso;destruct j;cbn in *;[congruence|eapply list_cycle2;symmetry;eauto].
    - eapply deq_loop_entry in Hedge1 as Hentry1.
      eapply deq_loop_entry in Hedge2 as Hentry2.
      split.
      + intros h Hh.
        decide (h = p).
        * exfalso. subst. destruct Hedge2. destruct H0. contradiction.
        * eapply deq_loop_entry_or in Hedge1. 2:eauto. destruct Hedge1;[assumption|contradiction].
      + intros h Hh.
        decide (h = p).
        * exfalso. subst. destruct Hedge1. destruct H0. contradiction.
        * eapply deq_loop_entry_or in Hedge2. 2:eauto. destruct Hedge2;[assumption|contradiction].
    - eapply deq_loop_exiting in Hedge1 as Hdeq1.
      eapply deq_loop_exiting in Hedge2 as Hdeq2.
      eapply exit_pred_loop in Hedge1. 2: eapply tcfg_edge_edge in Htedge2;eauto.
      eapply exit_pred_loop in Hedge2. 2: eapply tcfg_edge_edge in Htedge1;eauto.
      eapply loop_contains_deq_loop in Hedge1.
      eapply loop_contains_deq_loop in Hedge2.
      split;[transitivity h|transitivity h0];eauto.
  Qed.

  Lemma tag_cons_exit q p n i
        (Hedge : (q,n :: i) -t> (p,i))
    : exists h, exit_edge h q p.
  Proof.
    destruct Hedge.
    unfold eff_tag in H0.
    decide (edge__P q p);[|congruence].
    destruct (edge_Edge e).
    1-3: exfalso. 4:unfold eexit_edge in *;destructH;eexists;eauto.
    1,2: inv H0; eapply list_cycle;eauto.
    1: inv H0; eapply list_cycle2;eauto.
  Qed.

  Lemma nexit_injective q1 q2 p1 p2 j1 j2 i
        (Hedge1 : (q1,j1) -t> (p1,i))
        (Hedge2 : (q2,j2) -t> (p2,i))
        (Hnexit1 : nexit_edge q1 p1)
    : j1 = j2.
  Admitted.

End cfg.
