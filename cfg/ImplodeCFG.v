Require Import NePreSuffix CFGgeneral.
Require Export HeadexitsCFG SubCFG.

Definition implode_nodes `{C : redCFG} (r : Lab)
  := DecPred (fun p => (deq_loop r p
                     \/ exists e, exited p e /\ deq_loop r e)).

Local Arguments loop_contains {_ _ _ _ _}.
Local Arguments exit_edge {_ _ _ _} (_).

Lemma head_exits_implode_nodes_inv1 `(C : redCFG) (h p : Lab)
  : implode_nodes (C:=C) h p -> implode_nodes (C:=head_exits_CFG C h) h p.
Proof.
  intro Himpl.
  cbn in Himpl. destruct Himpl.
  - left. eapply head_exits_deq_loop_inv1. eauto.
  - right. destructH. exists e. split; eauto using head_exits_exited_inv1, head_exits_deq_loop_inv1.
Qed.

Lemma implode_nodes_root_inv `{C : redCFG} r
  : implode_nodes r root.
Proof.
  unfold implode_nodes. cbn.
  left.
  eapply deq_loop_root.
Qed.      

Definition purify_implode `{redCFG} h :=
  purify (implode_nodes_root_inv h) (D:=decide_pred _).
  
Definition impl_list `{redCFG} (h : Lab) :=
  filter (DecPred (fun q : Lab => (loop_contains h q \/ exited h q)
                        /\ (deq_loop h q
                            \/ exists e, exited q e
                                   /\ deq_loop h e
                           )
                  )
         ).


Lemma implode_nodes_back_edge (* unused *)`{redCFG} h p q
      (Hhead : back_edge' (restrict_edge' edge (implode_nodes h)) (restrict_edge' a_edge (implode_nodes h)) p q)
  : p ↪ q.
Proof.
  unfold back_edge' in *.
  unfold_edge_op' Hhead. destructH.
  decide (implode_nodes h p);[|contradiction].
  decide (implode_nodes h q);[|contradiction].
  destruct Hhead1 as [Hhead1|[Hhead1|Hhead1]];cbn in *.
  2,3:congruence.
  unfold back_edge,back_edge_b. unfold_edge_op. split;auto.
Qed.

Instance implode_CFG `(H : redCFG) h7 (Hhe : head_exits_property H h7)
  : @redCFG (finType_sub_decPred (implode_nodes h7))
            (restrict_edge edge (implode_nodes h7))
            (↓ purify_implode h7)
            (restrict_edge a_edge (implode_nodes h7)).
Proof.
  eapply sub_CFG;intros.
  - specialize (a_reachability p) as [π Hπ].
    revert dependent p. revert dependent π.
    specialize (well_founded_ind (R:=(@StrictPrefix' Lab)) (@StrictPrefix_well_founded Lab)
                                 (fun π : ne_list Lab => forall (p : Lab),
                                      implode_nodes h7 p ->
                                      Path a_edge root p π
                                      -> exists π0, Path (restrict_edge' a_edge (implode_nodes h7)) root p π0))
      as WFind.
    eapply WFind.
    intros ? IHwf ? ? ?. clear WFind.
    destruct H1.
    + eexists; econstructor.
    + unfold implode_nodes in H0. cbn in H0.
      decide (implode_nodes h7 b).
      * specialize (IHwf π). exploit IHwf;[econstructor;econstructor|].
        destructH.
        eexists; econstructor;eauto.
        unfold_edge_op. split_conj;auto.
      * unfold implode_nodes in n. cbn in n. simpl_dec' n.
        destructH.
        simpl_dec' n1. simpl_dec' n1.  
        enough (exists h, exit_edge _ h b c).
        {
          destructH.
          enough (h ∈ π).
          {
            eapply path_to_elem in H4;eauto. destructH.
            specialize (IHwf ϕ).
            assert (implode_nodes h7 h) as Himpl.
            {
              destruct H0.
              * right. exists c. split;[exists b|];eauto.
              * exfalso.
                destructH. eapply no_exit_head;eauto.
                unfold exited,exit_edge in H4; destructH. eauto using loop_contains_loop_head.
            }
            exploit IHwf.
            - eapply prefix_ex_cons in H6. destructH. econstructor. cbn. eauto.
            - destructH. 
              exists (c :<: π0). econstructor;eauto. unfold_edge_op. split_conj;eauto.
              eapply head_exits_property_a_edge;eauto.
              contradict n0.
              eapply loop_contains_deq_loop in n0.
              eapply eq_loop_exiting in H3.
              eapply eq_loop2;eauto.
          }
          eapply dom_loop;[unfold exit_edge in H3;destructH;eauto|].
          eapply subgraph_path';eauto.
        }
        simpl_dec' n0. simpl_dec' n0.
        destructH.
        exists x. unfold exit_edge;split_conj;eauto using a_edge_incl.
        destruct H0.
        -- contradict n3. eauto.
        -- destructH.
           destruct H3 as [q Hexit]. 
           decide (x = c).
           ++ exfalso. subst. eapply loop_reachs_member in n2. destructH.
              eapply a_edge_acyclic;eauto.
           ++ 
              intro N.
              eapply exit_edge_unique_diff_head in Hexit;auto;cycle 1.
              ** exact N.
              ** contradict n3. eapply H4;eauto.
              ** contradiction.
  - rewrite loop_contains'_basic in H1.
    unfold loop_contains in H1. rename H1 into Hloop.
    destructH.
    exists p0.
    revert dependent p.
    induction π;intros;inversion Hloop2;subst.
    + exists (ne_single a). split_conj;eauto.
      * unfold_edge_op. split_conj;eauto using back_edge_incl.
        -- admit. (*left;eapply deq_loop_refl.*)
        -- left. unfold back_edge,back_edge_b in Hloop0. unfold_edge_op' Hloop0. firstorder.
      * econstructor.
    + admit. (* FIXME: give intuition *)
Admitted.

Lemma implode_CFG_elem `{C : redCFG} (p h : Lab) (Himpl : implode_nodes h p)
  : finType_sub_decPred (implode_nodes h).
Proof.
  econstructor. unfold pure. instantiate (1:=p).
  decide (implode_nodes h p);eauto.
Defined.

Arguments head_exits_CFG {_ _ _ _} _.
Arguments implode_CFG {_ _ _ _} _.

Definition local_impl_CFG `(C : redCFG) (h : Lab)
  := implode_CFG (head_exits_CFG C h) h (head_exits_property_satisfied (C:=C) (qh:=h)).

Arguments redCFG : clear implicits.
Arguments implode_nodes {_ _ _ _} _.
Definition local_impl_CFG_type `(C : redCFG) (h : Lab)
  := (finType_sub_decPred (implode_nodes (head_exits_CFG C h) h)).
Arguments redCFG : default implicits.
Arguments implode_nodes : default implicits.

Definition impl_of_original (* unused *)`(C : redCFG) (h : Lab)
  : Lab -> option (local_impl_CFG_type C h).
Proof.
  intro p.
  decide (implode_nodes (head_exits_CFG C h) h p).
  - apply Some. econstructor. eapply purify;eauto.
  - exact None.
Defined.  

Definition impl_of_original' `(C : redCFG) (h p : Lab) (H : implode_nodes C h p)
  : local_impl_CFG_type C h.
Proof.
  econstructor. eapply purify;eauto.
  eapply head_exits_implode_nodes_inv1;eauto.
Defined.

Arguments local_impl_CFG {_ _ _ _} _.

Lemma Lab_dec' `{redCFG} : forall (l l' : Lab), { l = l' } + { l <> l'}.
Proof.
  apply Lab_dec.
Qed.

