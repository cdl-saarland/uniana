Require Export SubCFG CFGgeneral.

(** * loop_CFG **)

Definition loop_nodes `{redCFG} (h : Lab) := DecPred (fun p => loop_contains h p \/ exited h p).

Definition purify_head `{C : redCFG} h
           (H : loop_head h)
  : pure (loop_nodes h) h (D:=decide_pred (loop_nodes h))
  := purify (or_introl (loop_contains_self H)).

Instance loop_CFG
         `(C : redCFG)
         (h : Lab)
         (H : loop_head h)
  : @redCFG (finType_sub_decPred (loop_nodes h))
            (restrict_edge edge (loop_nodes h))
            (↓ (purify_head H))
            (restrict_edge a_edge (loop_nodes h)).
Proof. (* this proof is broken since I have changed sub_CFG *)
  unfold purify_head. 
  eapply sub_CFG; intros.
  - assert (forall p, loop_contains h p -> exists π : ne_list Lab, Path (restrict_edge' a_edge (loop_nodes h)) h p π) as Hloo.
    {
      clear.
      intros.
      specialize (a_reachability p) as [π Hπ].
      eapply dom_loop with (h0:=h) in H as Hdom;eauto.
      eapply dom_dom_acyclic in Hdom.
      eapply Hdom in Hπ as Hϕ.
      eapply path_from_elem in Hϕ;eauto. destructH.
      exists ϕ. eapply all_sat_restrict_edge';auto.
      intros. left.
      eapply acyclic_path_stays_in_loop;eauto.
      eapply loop_contains_self. eapply loop_contains_loop_head;eauto.
    }
    destruct H0;auto.
    unfold exited in H0. destructH. 
    copy H0 Hexit.
    unfold exit_edge in H0. destructH. exploit Hloo.
    destructH.
    exists (p :<: π). econstructor;eauto.
    unfold_edge_op.
    split_conj;[eapply exit_a_edge;eauto|left;auto|right;eexists;eauto].
  - clear H2.
    enough (loop_contains h h0). 
    + unfold loop_contains' in *.
      destructH' H1.
      exists p0, π. split_conj;[| |apply H5].
      * unfold_edge_op.
        assert (loop_contains h0 p0).
        {
          exists p0, (ne_single p0).
          split_conj;[unfold back_edge; auto|econstructor|contradict H5;cbn in H5;contradiction].
        }
        unfold_edge_op' H3. destruct H3. split_conj;eauto;unfold loop_nodes;cbn;left;auto.
        eapply loop_contains_trans;eauto.
      * specialize (loop_contains_ledge_path H3 H1 H5) as Hle.
        eapply all_sat_restrict_edge';auto.
        intros. unfold loop_nodes. cbn. left. eapply loop_contains_trans;eauto.
    + clear - H0.
      destructH.
      assert (loop_head h0).
      {
        decide (loop_nodes h x);decide (loop_nodes h h0).
        2-4: exfalso;unfold_edge_op' H0; destruct H0; destructH; contradiction.
        cstr_subtype p.
        cstr_subtype p0.
        rewrite <-restrict_back_edge_intersection in H0.
        eapply restrict_back_edge in H0.
        cbn. exists x. auto.
      } 
      unfold_edge_op' H0. destruct H0. destruct H0 as [_ [_ H0]]. destruct H0;auto.
      unfold exited in H0. destructH.
      eapply no_exit_head in H0;contradiction.
Admitted.

Lemma loop_CFG_elem `{C : redCFG} (h p : Lab)
      (Hloop : loop_contains h p)
  : finType_sub_decPred (loop_nodes h).
Proof.
  intros.
  econstructor. instantiate (1:=p).
  unfold pure. decide ((loop_nodes h) p);eauto.
  contradict n. unfold loop_nodes,predicate. left;auto.
Defined.

Arguments loop_CFG_elem {_ _ _ _} _.


(* Definition implode_nodes `{C : redCFG}
  := DecPred (fun p => (deq_loop root p
                     \/ (depth p = S (depth root)) /\ loop_head p)).

Definition implode_nodes' `{C : redCFG}
  := DecPred (fun p => (deq_loop root p
                     \/ exists q, edge p q = true /\ loop_head p /\ deq_loop root q)). *)

Definition get_root `(C : redCFG) := root.

Arguments loop_CFG {_ _ _ _} _.

Lemma loop_CFG_head_root (* unused *)`{C : redCFG} (h : Lab)
      (Hhead : loop_head h)
      (D := loop_CFG C h Hhead)
  : get_root D = loop_CFG_elem C h h (loop_contains_self Hhead).
Proof.
  unfold get_root. unfold loop_CFG_elem.
Admitted.


Definition loop_CFG_type `(C : redCFG) (h : Lab) (H : loop_head h)
  := @finType_sub_decPred Lab (@loop_nodes Lab edge root a_edge C h).