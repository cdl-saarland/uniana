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

Parameter loop_contains'_dec
  : forall (L : finType) (e f : L -> L -> bool) (h p : L), dec (loop_contains' e f h p).
Existing Instance loop_contains'_dec.

Definition deq_loop' :=
  fun (Lab : finType) (edge : Lab -> Lab -> bool) (a_edge : Lab -> Lab -> bool) (q p : Lab) =>
    forall h : Lab, loop_contains' edge a_edge h p -> loop_contains' edge a_edge h q.

Instance deq_loop'_dec (Lab : finType) (edge : Lab -> Lab -> bool) (a_edge : Lab -> Lab -> bool) (q p : Lab)
  : dec (deq_loop' edge a_edge q p).
unfold deq_loop'. eauto.
Qed.

Definition exited' :=
  fun (Lab : finType) (edge : Lab -> Lab -> bool) (a_edge : Lab -> Lab -> bool)
    (h q : Lab) => exists p : Lab, exit_edge' edge a_edge h p q.
                                                                   
Definition implode_nodes' :=
  fun (Lab : finType) (edge : Lab -> Lab -> bool) (root : Lab) (a_edge : Lab -> Lab -> bool) (r : Lab) =>
    DecPred (fun p : Lab => deq_loop' edge a_edge r p
                         \/ (exists e : Lab, exited' edge a_edge p e /\ deq_loop' edge a_edge r e)).


Lemma back_edge_eq_loop `{C : redCFG} (p h : Lab)
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
      
Lemma back_edge_eq_loop' `{C : redCFG} (p q h : Lab)
      (Hp : p ↪ h)
      (Hq : q ↪ h)
  : eq_loop p q.
Proof.
  eapply back_edge_eq_loop in Hp.
  eapply back_edge_eq_loop in Hq.
  transitivity h. auto. symmetry. auto.
Qed.

Lemma back_edge_no_head `{C : redCFG} (p h : Lab)
      (Hbe : p ↪ h)
  : ~ loop_head p.
Proof.
  intro N.
  eapply no_self_loops;[eapply back_edge_incl;eauto|].
  eapply loop_contains_Antisymmetric.
  - eapply loop_contains_ledge in Hbe as Hledge. eapply back_edge_eq_loop in Hbe as Q.
    rewrite <-Q. eapply loop_contains_self. auto.
  - eapply loop_contains_ledge;eauto.
Qed.

Lemma all_latches_stay_latches `{C : redCFG} (p q h : Lab)
      (Hbe : p ↪ q)
      (Hhead : loop_head' (restrict_edge' edge (implode_nodes h))
                          (restrict_edge' a_edge (implode_nodes h)) q)
  : back_edge' (restrict_edge' edge (implode_nodes h)) (restrict_edge' a_edge (implode_nodes h)) p q.
Proof.
  unfold back_edge'. unfold loop_head' in Hhead. destructH.
  eapply implode_nodes_back_edge in Hhead as Hbe0.
  eapply back_edge_eq_loop' in Hbe as Heq;eauto 1.
  unfold_edge_op. unfold_edge_op' Hhead. destructH.
  conv_bool. eapply back_edge_incl in Hbe as He.
  split_conj;eauto 1.
  - destruct Hhead0;[left;rewrite <-Heq;auto 1|].
    destructH. unfold exited,exit_edge in H0. destructH. eapply back_edge_no_head in Hbe0.
    eapply loop_contains_loop_head in H2. contradiction.
  - left. unfold back_edge,back_edge_b in Hbe. unfold_edge_op' Hbe. destructH;eauto.
Qed.

Lemma impl_nimpl_ex_headexit `{H : redCFG} a b c h π
      (Haimpl : (implode_nodes h) a)
      (Himpl : (implode_nodes h) c)
      (Hnimpl : ~ (implode_nodes h) b)
      (Hpath : CPath a b π)
      (Hedge : a_edge b c = true)
  : exists h', exit_edge H h' b c /\ h' ∈ π.
Proof.
  unfold implode_nodes in Himpl. cbn in Himpl.
  unfold implode_nodes in Hnimpl. cbn in Hnimpl. simpl_dec' Hnimpl.
  destructH.
  simpl_dec' Hnimpl1. simpl_dec' Hnimpl1.
  simpl_dec' Hnimpl0. simpl_dec' Hnimpl0.
  destructH.
  exists x. unfold exit_edge;split_conj; eauto using a_edge_incl.
  - destruct Himpl.
    + contradict Hnimpl3. eauto.
    + destructH.
      destruct H1 as [q Hexit].
      decide (x = c).
      * exfalso. subst.
          
        exfalso. subst. eapply loop_reachs_member in Hnimpl2. destructH.
        eapply a_edge_acyclic;eauto.
      * intro N.
        eapply exit_edge_unique_diff_head in Hexit;auto;cycle 1.
        -- exact N.
        -- contradict Hnimpl3. eapply H2;eauto.
        -- contradiction.
  - decide (x=a).
    { subst x. eapply path_contains_back;eauto. }
    eapply dom_loop_contains;[eauto| |eauto using subgraph_path'].
    contradict Hnimpl3.
    destruct Haimpl.
    + eapply H0;eauto.
    + clear - H0 Hnimpl3 n. destructH.
      unfold exited in H1. destructH.
      eapply H2. eapply exit_edge_in_loop;eauto.
Qed.


Lemma implode_nodes_path_inv `(C : redCFG) (h : Lab) (Hhe : head_exits_property C h) p q π
      (Hpath : CPath p q π)
      (HPp : (implode_nodes h) p)
      (HPq : (implode_nodes h) q)
  : exists ϕ, Path (restrict_edge' edge (implode_nodes h)) p q ϕ /\ splinter_strict ϕ π.
Proof.
  revert dependent q. revert dependent π.
  specialize (well_founded_ind (R:=(@StrictPrefix' Lab)) (@StrictPrefix_well_founded Lab)
                               (fun π : ne_list Lab => forall (q : Lab),
                                    CPath p q π ->
                                    implode_nodes h q
                                    -> exists π0,
                                        Path (restrict_edge' edge (implode_nodes h)) p q π0
                                        /\ splinter_strict π0 π))
    as WFind.
  eapply WFind.
  intros x IHwf ? Hpath Himpl. clear WFind.
  destruct Hpath.
  - eexists;split;econstructor. econstructor.
  - decide ((implode_nodes h) b).
    + specialize (IHwf π). exploit IHwf;[econstructor;econstructor|].
      destructH.
      eexists;split;[econstructor;eauto 1|cbn;econstructor;auto].
      unfold_edge_op. split_conj;auto.
    + eapply edge_destruct in H. destruct H.
      * eapply impl_nimpl_ex_headexit in n as Hhexit;cycle 3;eauto.
        destruct Hhexit as [h' [Hhexit Hel]].
        eapply path_to_elem in Hel;eauto. destructH.
        specialize (IHwf ϕ).
        assert (implode_nodes h h') as Himpl'.
        {
          destruct Himpl.
          * right. exists c. split;[exists b|];eauto.
          * exfalso.
            destructH. eapply no_exit_head;eauto.
            unfold exited,exit_edge in H1; destructH. eauto using loop_contains_loop_head.
        }
        exploit IHwf.
        -- eapply prefix_ex_cons in Hel1. destructH. econstructor. cbn. eauto.
        -- destructH. 
           exists (c :<: π0). split.
           ++ econstructor;eauto 1. unfold_edge_op. split_conj;eauto 1.
              eapply a_edge_incl.
              eapply head_exits_property_a_edge;eauto.
              contradict n.
              eapply loop_contains_deq_loop in n.
              eapply eq_loop_exiting in Hhexit.
              unfold implode_nodes. cbn. left. 
              eapply eq_loop2;eauto.
           ++ cbn. econstructor.
              transitivity ϕ;eauto with splinter.
      * admit.
Admitted.

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
    + decide (implode_nodes h7 b).
      * specialize (IHwf π). exploit IHwf;[econstructor;econstructor|].
        destructH.
        eexists; econstructor;eauto.
        unfold_edge_op. split_conj;auto.
      * eapply impl_nimpl_ex_headexit in H0 as Hnexit.
        4: eapply subgraph_path';eauto.
        2 :{ eapply implode_nodes_root_inv. }
        2,3: eauto.
        destruct Hnexit as [h [H3 H4]].
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
        -- eapply prefix_ex_cons in H6. destructH. econstructor. cbn. eauto.
        -- destructH. 
           exists (c :<: π0). econstructor;eauto. unfold_edge_op. split_conj;eauto.
           eapply head_exits_property_a_edge;eauto.
           contradict n.
           eapply loop_contains_deq_loop in n.
           eapply eq_loop_exiting in H3.
           unfold implode_nodes. cbn. left. 
           eapply eq_loop2;eauto.
  - rewrite loop_contains'_basic in H1.
    fold (loop_head' (restrict_edge' edge (implode_nodes h7))
                     (restrict_edge' a_edge (implode_nodes h7)) h) in H0.
    unfold loop_contains in H1.
    destructH.
    eapply all_latches_stay_latches in H0;eauto.
    exists p0.
    eapply implode_nodes_path_inv in H1;eauto.
    2: { unfold back_edge' in H0. unfold_edge_op' H0. destructH. auto. }
    destructH. exists ϕ. split_conj;eauto.
    contradict H5. clear - H6 H5.
    eapply splinter_strict_rev in H6.
    destruct (rev ϕ);cbn in *;[contradiction|].
    inversion H6;subst;cbn in *.
    + eapply splinter_strict_incl;eauto.
    + eapply splinter_strict_incl;eauto.
Qed.

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

