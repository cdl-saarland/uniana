Require Export CFGinnermost CFGgeneral.


(** * head_exits **)

Definition head_exits_edge `{redCFG} h h' q : bool
  := if decision (exited h' q /\ ~ loop_contains h' h) then true else false. 

Lemma head_exits_edge_spec :
  forall `{redCFG} h h' q, head_exits_edge h h' q = true -> exists p, exit_edge h' p q.
Proof.
  intros. unfold head_exits_edge in H0. decide (exited h' q); cbn;eauto.
  decide (exited h' q /\ ~ loop_contains h' h);[|congruence]. destructH. contradiction.
Qed.

Lemma head_exits_edge_spec_iff :
  forall `{redCFG} h h' q, head_exits_edge h h' q = true <-> (exists p, exit_edge h' p q) /\ ~ loop_contains h' h.
Proof.
  intros. unfold head_exits_edge. decide (exited h' q /\ ~ loop_contains h' h).
  - split;intros;[|reflexivity]. firstorder.
  - split;intros;[congruence|]. simpl_dec' n. destructH. unfold exited in n.
    destruct n as [n|n];[simpl_dec' n; specialize (n p)|]; contradiction.
Qed.

Lemma head_exits_path `{redCFG} h p q :
  head_exits_edge h p q = true -> exists π, Path a_edge p q π.
Proof.
  intros. cbn.
  eapply head_exits_edge_spec in H0.
  destructH.
  copy H0 Hexit.
  unfold exit_edge in H0. destructH.
  eapply loop_reachs_member in H1.
  destructH.
  exists (q :: π).
  eapply exit_a_edge in Hexit.
  econstructor;eauto.
Qed.

Lemma head_exits_in_path_head_incl `{redCFG} qh ql π
      (Hπ : Path (edge ∪ (head_exits_edge qh)) root ql π)
  : exists ϕ, Path edge root ql ϕ /\ forall (h : Lab), loop_contains h ql -> h ∈ ϕ -> h ∈ π.
Proof.
  remember ql as ql'.
  setoid_rewrite Heqql' at 2.
  assert (deq_loop ql' ql) as Hdeq by (subst;eapply deq_loop_refl).
  clear Heqql'.
  revert dependent ql.
  induction Hπ;intros;cbn;eauto.
  - eexists;split;econstructor;eauto. inversion H1;subst;auto. inversion H2.
  - unfold_edge_op' H0. destruct H0.
    + specialize (IHHπ b). exploit IHHπ;[eapply deq_loop_refl|]. destructH.
      exists (c :: ϕ). split;[econstructor;eauto|].
      intros. cbn in H2. destruct H2;eauto.
      eapply Hdeq in H1.
      decide (h = c);[left;auto|].
      eapply preds_in_same_loop in H1;eauto.
    + eapply head_exits_path in H0 as Hψ. destruct Hψ as [ψ Hψ].
      specialize (IHHπ c). exploit IHHπ.
      * eapply head_exits_edge_spec in H0. destructH.
        eapply deq_loop_trans;[eapply deq_loop_exiting;eauto|eapply deq_loop_exited;eauto].
      * destructH.
        eexists. split;[eauto using path_app',subgraph_path'|].
        intros.
        eapply in_app_or in H2. destruct H2.
        -- left.
           
           eapply head_exits_edge_spec in H0. destructH.
           decide (c = h);[auto|].
           eapply acyclic_parallel_exit_path in Hψ;eauto.
           ++ eapply loop_contains_trans in H1;eauto.
              eapply Hdeq in H1.
              unfold exit_edge in H0. destructH. contradiction.
           ++ destruct Hψ;cbn in *;destruct H2. 1-3: contradiction. auto.
        -- right;eauto using tl_incl. eapply IHHπ1. eapply Hdeq;auto. eapply tl_incl. auto.
Qed.

Lemma head_exits_back_edge `{redCFG} ql qh h :
  ((edge ∪ (head_exits_edge h)) ∖ (a_edge ∪ (head_exits_edge h))) ql qh = true <-> ql ↪ qh.
Proof.
  unfold back_edge,back_edge_b.
  unfold_edge_op. split;intros. 
  - destructH. destruct H1;[eauto|].
    destruct (head_exits_edge h ql qh);cbn in *;congruence.
  - split_conj;[firstorder|firstorder|].
    unfold head_exits_edge.
    decide (exited ql qh /\ ~ loop_contains ql h);[|cbn;auto].
    exfalso.
    unfold exited in a.
    destructH' a.
    eapply no_exit_head;eauto.
    exists ql. unfold back_edge,back_edge_b;conv_bool. unfold_edge_op. eauto.
Qed.

Lemma head_exits_no_self_loop `{redCFG} h p q : head_exits_edge h p q = true -> p <> q.
Proof.
  intros. eapply head_exits_edge_spec in H0.
  destructH.
  unfold exit_edge in H0. destructH.
  eapply loop_contains_loop_head in H1.
  eapply loop_contains_self in H1.
  intro N;subst.
  contradiction.
Qed.

Lemma head_exits_same_connected `{redCFG} h p q π
      (Hpath : Path (a_edge ∪ (head_exits_edge h)) p q π)
  : exists ϕ, Path a_edge p q ϕ.
Proof.
  induction Hpath;cbn;eauto.
  - eexists. econstructor.
  - destructH. unfold_edge_op' H0. destruct H0.
    + eexists. econstructor;eauto.
    + eapply head_exits_path in H0. destructH.
      eexists; eauto using path_app'.
Qed.

Lemma head_exits_same_connected' `{redCFG} h p q π
      (Hpath : Path (edge ∪ (head_exits_edge h)) p q π)
  : exists ϕ, Path edge p q ϕ.
Proof.
  induction Hpath;cbn;eauto.
  - eexists. econstructor.
  - destructH. unfold_edge_op' H0. destruct H0.
    + eexists. econstructor;eauto.
    + eapply head_exits_path in H0. destructH.
      eapply subgraph_path' in H0;eauto.
      eexists; eauto using path_app'.
Qed.


Lemma head_exits_loop_equivalence `{redCFG} qh h p
  : loop_contains h p <-> loop_contains' (edge ∪ (head_exits_edge qh)) (a_edge ∪ (head_exits_edge qh)) h p.
Proof.
  split;intros.
  - unfold loop_contains'. unfold loop_contains in H0.
    destructH.
    exists p0, π.
    split_conj.
    + eapply head_exits_back_edge;eauto.
    + clear - H0.
      induction H0;econstructor;eauto. unfold_edge_op. left;auto.
    + auto.
  - copy H0 H0'.
    unfold loop_contains. unfold loop_contains' in H0.
    destructH.
    assert (Path (edge ∪ (head_exits_edge qh)) p p0 π -> h ∉ tl (rev π)
            -> loop_contains h p0
            -> exists π0, Path edge p p0 π0 /\ h ∉ tl (rev π0)).
    {
      clear. intros.
      induction H0.
      - exists ([a]). split;eauto. econstructor.
      - exploit' IHPath.
        + cbn in *. contradict H1.
          destr_r' π; subst π. 1: inversion H0.
          rewrite rev_rcons. cbn. rewrite rev_rcons in H1. cbn in *.
          eapply in_or_app. left;auto.
        + unfold_edge_op' H3. destruct H3.
          * exploit IHPath.
            {
              eapply preds_in_same_loop;eauto.
              contradict H1. subst.
              cbn. destr_r' π;subst π. 1: inversion H0. rewrite rev_rcons. cbn. eapply in_or_app. right;firstorder.
            }
            destructH.
            exists (c :: π0). split;[econstructor;eauto|].
            contradict IHPath1.
            destr_r' π0;subst π0. 1: inversion IHPath0.
            cbn. rewrite rev_rcons. cbn.
            rewrite <-cons_rcons_assoc in IHPath1.
            rewrite rev_rcons in IHPath1. cbn in *.
            eapply In_rcons in IHPath1. destruct IHPath1;auto.
            subst h. exfalso. contradict H1. 
            destr_r' π;subst π. 1: inversion H0.
            cbn. rewrite rev_rcons. cbn. eapply in_or_app. right;firstorder.
          * eapply head_exits_edge_spec in H3 as Hexit. destruct Hexit as [qe Hexit].
            assert (loop_contains h b) as Hloop.
            {
              eapply deq_loop_exiting;eauto.
              eapply deq_loop_exited;eauto.
            }
            exploit IHPath.
            destructH.
            eapply head_exits_path in H3. destructH.
            exists (π1 ++ tl π0).
            split.
            -- eapply subgraph_path' in H3; [eapply path_app'|];eauto.
            -- intro N. rewrite rev_app_distr in N.
               enough (h ∉ rev π1).
               {
                 destr_r' π0;subst π0. 1: inversion IHPath0. rename l into π0.
                 destruct π0;cbn in N;eapply H4;[eapply tl_incl;auto|].
                 cbn in *. rewrite rev_rcons in N,IHPath1.
                 cbn in *.
                 eapply in_app_or in N. destruct N;[exfalso;apply IHPath1|contradiction].
                 eapply in_or_app. left;auto.
               }
               rewrite <-in_rev.
               clear - H3 Hexit H2 Hloop.
               decide (h = c).
               {
                 subst.
                 exfalso.
                 eapply no_exit_head;eauto using loop_contains_loop_head.
               }      
               inversion H3;subst.
               ++ cbn. firstorder.
               ++ cbn. simpl_dec. split;[auto|].
                  intro Hin.
                  eapply acyclic_path_stays_in_loop in Hin;auto;cycle 1.
                  ** eauto.
                  ** unfold exit_edge in Hexit. destructH. eapply loop_contains_self.
                     eapply loop_contains_loop_head;eauto.
                  ** eapply a_edge_incl in H1.
                     eapply exit_pred_loop;eauto.
                  ** eapply loop_contains_Antisymmetric in Hin. exploit Hin. subst.
                     unfold exit_edge in Hexit; destructH; contradiction.
    }
    exists p0.
    exploit H2.
    {
      rewrite head_exits_back_edge in H1. eapply loop_contains_ledge;eauto.
    }
    destructH.
    eexists;split;eauto.
    eapply head_exits_back_edge;eauto.
Qed.


Lemma head_exits_exit_edge `{redCFG} qh h p q
      (Hexit : exit_edge' (edge ∪ (head_exits_edge qh)) (a_edge ∪ (head_exits_edge qh)) h p q)
  : exists p', exit_edge h p' q.
Proof.
  unfold exit_edge' in *. destructH.
  unfold_edge_op' Hexit3.
  destruct Hexit3.
  - exists p. unfold exit_edge. split_conj.
    1,2: rewrite head_exits_loop_equivalence;eauto.
    auto.
  - eapply head_exits_edge_spec in H0.
    destructH. exists p0.
    unfold exit_edge in *. destructH.
    split_conj;eauto.
    + eapply loop_contains_trans;eauto. eapply head_exits_loop_equivalence;eauto.
    + rewrite head_exits_loop_equivalence;eauto.
Qed.

Instance head_exits_CFG `(redCFG) qh
  : redCFG (edge ∪ (head_exits_edge qh)) root (a_edge ∪ (head_exits_edge qh)).
Proof.
econstructor;intros.
{ (* loop_head_dom *)
  unfold Dom. intros π Hpath.
  rewrite head_exits_back_edge in H0.
  eapply loop_contains_ledge in H0.
  eapply head_exits_in_path_head_incl in Hpath;eauto.
  destructH.
  eapply dom_loop in Hpath0 as Hpath';eauto.
}
{ (* a_edge_incl *)
  eapply union_subgraph.
  - exact a_edge_incl.
  - firstorder.
}
{ (* a_edge_acyclic *)
  unfold acyclic. intros p q π Hedge Hπ. eapply head_exits_same_connected in Hπ. destructH.
  unfold union_edge in Hedge; conv_bool. destruct Hedge as [Hedge|Hedge].
  - eapply a_edge_acyclic; eauto.
  - eapply head_exits_no_self_loop in Hedge as Hnself.
    eapply head_exits_path in Hedge. destructH. eapply path_path_acyclic;eauto.
}
{ (* reachability *)
  specialize a_reachability as H0. eapply subgraph_path in H0;eauto.
  unfold sub_graph,union_edge. firstorder. 
}
{ (* single_exit *)
  fold_lp_cont'.
  assert (loop_contains h p /\ loop_contains h' p) as [Hloop Hloop'].
  {
    unfold exit_edge' in *. do 2 destructH.
    split; eapply head_exits_loop_equivalence; eauto.
  }
  eapply loop_contains_either in Hloop;eauto.
  destruct Hloop.
  - eapply head_exits_exit_edge in H0.
    eapply head_exits_exit_edge in H1.
    do 2 destructH.
    eapply single_exit;eauto.
    unfold exit_edge in *.
    do 2 destructH.
    split;auto.
    eapply loop_contains_trans;eauto.
  - eapply head_exits_exit_edge in H0.
    eapply head_exits_exit_edge in H1.
    do 2 destructH.
    eapply single_exit;cycle 1; eauto.
    unfold exit_edge in *.
    do 2 destructH.
    split;auto.
    eapply loop_contains_trans;eauto.
}
{ (* no_head_exit *)
  fold_lp_cont'.
  intro N. destructH.
  eapply head_exits_exit_edge in H0. destructH.
  eapply no_exit_head;eauto.
  unfold loop_head.
  exists p0.
  eapply head_exits_back_edge;eauto.
}
{ (* exit_pred_loop *)
  fold_lp_cont'.
  eapply head_exits_exit_edge in H0. destructH.
  unfold_edge_op' H1.
  destruct H1.
  - copy H1 Hedge. eapply exit_edge_pred_exiting in H1;eauto.
    apply (exit_pred_loop (q:=q)) in H1;eauto.
    rewrite <-head_exits_loop_equivalence;eauto.
  - eapply head_exits_edge_spec in H1.
    destructH.
    copy H0 Hexit.
    unfold exit_edge in H0.
    destructH.
    eapply exit_edge_pred_exiting in H1;eauto.
    eapply single_exit in Hexit;eauto. subst.
    rewrite <-head_exits_loop_equivalence. 
    eauto using loop_contains_self, loop_contains_loop_head.
}
{
  intro Heq.
  eapply no_self_loops;eauto. subst. unfold_edge_op' H0. destruct H0;[auto|].
  eapply head_exits_edge_spec in H0. destructH.
  unfold exit_edge in H0. destructH.
  exfalso. contradict H0. eauto using loop_contains_loop_head,loop_contains_self.
}
{
  intro N. eapply root_no_pred.
  unfold_edge_op' N. destruct N.
  - eauto.
  - eapply head_exits_edge_spec in H0. destructH. unfold exit_edge in H0.
    exfalso.
    destructH.
    eapply root_no_pred;eauto.
} 
Qed.

(* We need LOCAL head exits and also a local headexits property, bc
 * otherwise every loop head becomes a loop_split of itself and any exit in the imploded graph *)
Definition head_exits_property `(C : redCFG) qh := forall h p q, exit_edge h p q -> ~ loop_contains h qh
                                                            -> edge h q = true.

Local Arguments exit_edge {_ _ _ _} (_).

Lemma head_exits_property_satisfied `(C : redCFG) qh : head_exits_property (head_exits_CFG C qh) qh.
Proof.
  unfold head_exits_property. 
  intros h p q Hexit Hloop. unfold union_edge. conv_bool.
  eapply head_exits_exit_edge in Hexit.
  unfold loop_contains in Hloop. unfold back_edge,back_edge_b in Hloop. fold_lp_cont'.
  rewrite <-head_exits_loop_equivalence in Hloop.
  right.
  rewrite head_exits_edge_spec_iff.
  split;eauto. 
Qed.

Lemma head_exits_property_a_edge `{C : redCFG} qh 
  : head_exits_property C qh -> forall h p q : Lab, exit_edge _ h p q -> ~ loop_contains h qh -> a_edge h q = true.
Proof.
  intros.
  eapply H in H0 as H2.
  - decide (a_edge h q = true);[auto|exfalso].
    eapply no_exit_head;eauto. unfold loop_head.
    exists h. unfold back_edge,back_edge_b. unfold_edge_op. split;auto.
    eapply negb_true_iff,not_true_is_false. auto.
Qed.

Local Arguments loop_contains {_ _ _ _} _.

Lemma head_exits_loop_contains_iff `(C : redCFG) (h p q : Lab)
  : loop_contains C h q <-> loop_contains (head_exits_CFG C p) h q.
Proof.
  setoid_rewrite <-loop_contains'_basic at 2.
  eapply head_exits_loop_equivalence.
Qed.          

Lemma head_exits_deq_loop_inv1 `(C : redCFG) (h p q : Lab)
  : deq_loop (C:=C) p q -> deq_loop (C:=head_exits_CFG C h) p q.
Proof.
  intros.
  unfold deq_loop in *.
  setoid_rewrite <-head_exits_loop_contains_iff.
  eauto.
Qed.

Lemma head_exits_deq_loop_inv2 `(C : redCFG) (h p q : Lab)
  : deq_loop (C:=head_exits_CFG C h) p q -> deq_loop (C:=C) p q.
Proof.
  unfold deq_loop.
  setoid_rewrite <-head_exits_loop_contains_iff.
  eauto.
Qed.

Lemma head_exits_exited_inv1 `(C : redCFG) (qh h p : Lab)
  : exited (C:=C) h p -> exited (C:=head_exits_CFG C qh) h p.
Proof.
  unfold exited, exit_edge.
  setoid_rewrite <-head_exits_loop_contains_iff.
  intros. destructH.
  exists p0. split_conj;eauto.
  eapply union_subgraph1;auto.
Qed.

Lemma head_exits_exited_inv2 `(C : redCFG) (qh h p : Lab)
  : exited (C:=head_exits_CFG C qh) h p -> exited (C:=C) h p.
Proof.
  unfold exited, exit_edge.
  setoid_rewrite <-head_exits_loop_contains_iff.
  intros. destructH.
  unfold_edge_op' H3. destruct H3.
  - exists p0. split_conj;eauto.
  - eapply head_exits_edge_spec in H. destructH. exists p1.
    replace p0 with h in *.
    + unfold exit_edge in H. destructH. split_conj; eauto.
    + eapply exit_edge_unique_diff_head;eauto.
Qed.
