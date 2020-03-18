Require Import CFGgeneral.
Require Export HeadexitsCFG SubCFG.

(** * Prerequisites **)

(** ** Definition **)

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


Lemma implode_nodes_back_edge `{redCFG} h p q
      (Hhead : back_edge' (restrict_edge' edge__P (implode_nodes h)) (restrict_edge' a_edge__P (implode_nodes h)) p q)
  : p ↪ q.
Proof.
  unfold back_edge' in *.
  unfold_edge_op' Hhead. destructH.
  decide (implode_nodes h p);[|contradiction].
  decide (implode_nodes h q);[|contradiction]. do 2 simpl_dec' Hhead1.
  destruct Hhead1 as [Hhead1|[Hhead1|Hhead1]];cbn in *.
  2,3:congruence.
  unfold back_edge. unfold_edge_op. split;auto.
Qed.

Parameter loop_contains'_dec
  : forall (L : finType) (e f : L -> L -> Prop) (h p : L), dec (loop_contains' e f h p).
Existing Instance loop_contains'_dec.

Definition deq_loop' :=
  fun (Lab : finType) (edge : Lab -> Lab -> Prop) (a_edge : Lab -> Lab -> Prop) (q p : Lab) =>
    forall h : Lab, loop_contains' edge a_edge h p -> loop_contains' edge a_edge h q.

Instance deq_loop'_dec (Lab : finType) (edge : Lab -> Lab -> Prop) (a_edge : Lab -> Lab -> Prop) (q p : Lab)
  : dec (deq_loop' edge a_edge q p).
unfold deq_loop'. eauto.
Qed.

Definition exited' :=
  fun (Lab : finType) (edge : Lab -> Lab -> Prop) (a_edge : Lab -> Lab -> Prop)
    (h q : Lab) => exists p : Lab, exit_edge' edge a_edge h p q.
                                                                   
(*Definition implode_nodes' :=
  fun (Lab : finType) (edge : Lab -> Lab -> bool) (root : Lab) (a_edge : Lab -> Lab -> bool) (r : Lab) =>
    DecPred (fun p : Lab => deq_loop' edge a_edge r p
                         \/ (exists e : Lab, exited' edge a_edge p e /\ deq_loop' edge a_edge r e)).*)


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
      (Hhead : loop_head' (restrict_edge' edge__P (implode_nodes h))
                          (restrict_edge' a_edge__P (implode_nodes h)) q)
  : back_edge' (restrict_edge' edge__P (implode_nodes h)) (restrict_edge' a_edge__P (implode_nodes h)) p q.
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
  - firstorder. 
Qed.

Global Instance deq_loop_Transitive `(C : redCFG) : Transitive deq_loop.
eapply deq_loop_PreOrder.
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
  - unfold is_true2,is_true. eapply a_edge_incl. eauto.
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

(*Definition implode_nodes' `{C : redCFG} :=
  fun (r : Lab) =>
    DecPred (fun p : Lab => deq_loop r p \/ (exists e : Lab, exited p e /\ eq_loop r e)).*)

Global Instance deq_loop_contains_Proper `(C : redCFG) (h : Lab)
  : Proper (Basics.flip deq_loop ==> Basics.impl) (loop_contains h).
Proof.
  intros x y Hdeq Hloop. unfold Basics.flip in Hdeq. eapply Hdeq. assumption.
Qed.

Lemma implode_nodes_inner_remove `(C : redCFG) (h p q : Lab)
      (Himpl : implode_nodes h p)
      (Hndeq : ~ deq_loop h p)
      (Hel : loop_contains p q)
      (Himplq : implode_nodes h q)
  : p = q.
Proof.
  destruct Himpl;[contradiction|]. destructH.
  unfold exited in H0. destructH.
  destruct Himplq.
  - exfalso. eapply Hndeq. 
  eapply loop_contains_deq_loop in Hel. transitivity q;eauto.
  - decide (p = q);[auto|exfalso].
    destructH. unfold exited in H2. destructH.
    eapply exit_edge_in_loop in n;eauto.
    apply Hndeq. transitivity e0;eauto. eapply loop_contains_deq_loop;auto.
Qed.

Lemma implode_nodes_self `(C : redCFG) (h : Lab)
  : (implode_nodes h) h.
Proof.
  left. eapply deq_loop_refl.
Qed.

(** ** Existence of imploded path **)

Lemma implode_nodes_path_inv `(C : redCFG) (h : Lab) (Hhe : head_exits_property C h) p q π
      (Hpath : CPath p q π)
      (HPp : (implode_nodes h) p)
      (HPq : (implode_nodes h) q)
  : exists ϕ, Path (restrict_edge' edge__P (implode_nodes h)) p q ϕ /\ splinter_strict ϕ π.
Proof.
  revert dependent q. revert dependent π.
  specialize (well_founded_ind (R:=(@StrictPrefix' Lab)) (@StrictPrefix_well_founded Lab)
                               (fun π : list Lab => forall (q : Lab),
                                    CPath p q π ->
                                    implode_nodes h q
                                    -> exists π0,
                                        Path (restrict_edge' edge__P (implode_nodes h)) p q π0
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
           exists (c :: π0). split.
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
      * decide (deq_loop h c).
        { exfalso. apply n. left. eapply back_edge_eq_loop in H. rewrite H. auto. }
        decide (c = a).
        { subst. exists ([a]). split;cbn;econstructor. eauto with splinter. }
        assert (~ loop_contains c a).
        {
          intro N.
          eapply implode_nodes_inner_remove in HPp;eauto.
        }
        eapply dom_loop_contains in Hpath as Hdom;eauto using loop_contains_ledge.
        eapply path_to_elem in Hdom;eauto.
        destructH.
        specialize (IHwf ϕ).
        exploit' IHwf.
        { eapply prefix_ex_cons in Hdom1. destructH. econstructor. cbn.
          eauto using loop_contains_loop_head. }
        specialize (IHwf c).
        exploit IHwf.
        destructH.
        exists π0. split.
        -- eauto.
        -- cbn. econstructor. eapply splinter_strict_prefix in Hdom1. transitivity ϕ;eauto.
Qed.

(** ** Imploded loop containment **)

Lemma implode_CFG_loop_contains:
  forall (Lab : finType) (edge : Lab -> Lab -> bool) (root : Lab) (a_edge : Lab -> Lab -> bool)
    (H : redCFG edge root a_edge) (h7 h p : Lab) (Hhe : head_exits_property H h7),
    (exists x : Lab,
        (restrict_edge' edge__P (implode_nodes h7) ∖ restrict_edge' a_edge__P (implode_nodes h7)) x h) ->
    loop_contains' edge__P a_edge__P h p ->
    (implode_nodes h7) p ->
    loop_contains' (restrict_edge' edge__P (implode_nodes h7)) (restrict_edge' a_edge__P (implode_nodes h7))
                   h p.
Proof.
  intros Lab edge root a_edge H h7 h p Hhe H0 H1 H2.
  
  
  rewrite loop_contains'_basic in H1.
  fold (loop_head' (restrict_edge' edge__P (implode_nodes h7))
                   (restrict_edge' a_edge__P (implode_nodes h7)) h) in H0.
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

(** * redCFG Instance for Imploded CFGs **)

Instance implode_CFG `(H : redCFG) h7 (Hhe : head_exits_property H h7)
  : @redCFG (finType_sub_decPred (implode_nodes h7))
            (fun x y => decision (restrict_edge edge__P (implode_nodes h7) x y))
            (↓ purify_implode h7)
            (fun x y => decision (restrict_edge a_edge__P (implode_nodes h7) x y)).
Proof.
  eapply sub_CFG;intros.
  - specialize (a_reachability p) as [π Hπ].
    revert dependent p. revert dependent π.
    specialize (well_founded_ind (R:=(@StrictPrefix' Lab)) (@StrictPrefix_well_founded Lab)
                                 (fun π : list Lab => forall (p : Lab),
                                      implode_nodes h7 p ->
                                      Path a_edge__P root p π
                                      -> exists π0, Path (restrict_edge' a_edge__P (implode_nodes h7)) root p π0))
      as WFind.
    eapply WFind.
    intros ? IHwf ? ? ?. clear WFind.
(*    set (a := root) in H1.*)
    dependent destruction H1. 
    + eexists; econstructor.
    + decide (implode_nodes h7 b).
      * specialize (IHwf π). exploit IHwf;[econstructor;econstructor|].
        destructH.
        eexists; econstructor;eauto.
        unfold_edge_op. split_conj;auto.
      * eapply impl_nimpl_ex_headexit in H0 as Hnexit.
        2 :{ eapply implode_nodes_root_inv. }
        3: eapply subgraph_path';eauto. 
        2,3: eauto.
        destruct Hnexit as [h [H3 H4]].
        eapply path_to_elem in H4;eauto. destructH.
        specialize (IHwf ϕ). 
        assert (implode_nodes h7 h) as Himpl.
        {
          destruct H0.
          * right. exists p. split;[exists b|];eauto.
          * exfalso.
            destructH. eapply no_exit_head;eauto.
            unfold exited,exit_edge in H4; destructH. eauto using loop_contains_loop_head.
        }
        exploit IHwf.
        -- eapply prefix_ex_cons in H6. destructH. econstructor. cbn. eauto.
        -- destructH. 
           exists (p :: π0). econstructor;eauto. unfold_edge_op. split_conj;eauto.
           eapply head_exits_property_a_edge;eauto.
           contradict n.
           eapply loop_contains_deq_loop in n.
           eapply eq_loop_exiting in H3.
           unfold implode_nodes. cbn. left. 
           eapply eq_loop2;eauto.
  - eapply implode_CFG_loop_contains;eauto.
Qed.

Lemma implode_CFG_elem `{C : redCFG} (p h : Lab) (Himpl : implode_nodes h p)
  : finType_sub_decPred (implode_nodes h).
Proof.
  econstructor. unfold pure. instantiate (1:=p).
  decide (implode_nodes h p);eauto.
Defined.

Arguments head_exits_CFG {_ _ _ _} _.
Arguments implode_CFG {_ _ _ _} _.

(** * redCFG Instance for Imploded CFGs with head exits **)
Definition local_impl_CFG `(C : redCFG) (h : Lab)
  := implode_CFG (head_exits_CFG C h) h (head_exits_property_satisfied (C:=C) (qh:=h)).

(** * Definitions and properties of Imploded CFGs **)
Arguments redCFG : clear implicits.
Arguments implode_nodes {_ _ _ _} _.
Definition local_impl_CFG_type `(C : redCFG) (h : Lab)
  := (finType_sub_decPred (implode_nodes (head_exits_CFG C h) h)).
Arguments redCFG : default implicits.
Arguments implode_nodes : default implicits.
Definition impl_of_original' `(C : redCFG) (h p : Lab) (H : implode_nodes C h p)
  : local_impl_CFG_type C h.
Proof.
  econstructor. eapply purify;eauto.
  eapply head_exits_implode_nodes_inv1;eauto.
Defined.

Definition impl_of_original `(C : redCFG) (h : Lab)
  : Lab -> option (local_impl_CFG_type C h).
Proof.
  intro p.
  decide (implode_nodes (head_exits_CFG C h) h p).
  - apply Some. econstructor. eapply purify;eauto.
  - exact None.
Defined.  

Arguments local_impl_CFG {_ _ _ _} _.

Lemma Lab_dec' `{redCFG} : forall (l l' : Lab), { l = l' } + { l <> l'}.
Proof.
  apply Lab_dec.
Qed.

Definition edge' `(C : redCFG) := edge.

Local Arguments edge__P {_ _ _ _} _.
Local Arguments a_edge__P {_ _ _ _} _.

Lemma head_exits_CFG_path `(C : redCFG) (h p q : Lab) π
      (Hpath : CPath p q π)
  : Path (edge__P (head_exits_CFG C h)) p q π.
Proof.
  unfold edge'.
  eapply subgraph_path'.
  - unfold edge__P, is_true. rewrite is_true2_decision. eapply union_subgraph1.
  - auto.
Qed.

Lemma head_exits_CFG_implode_nodes_inv `(C : redCFG) (h p : Lab)
      (Himpl : implode_nodes C h p)
  : implode_nodes (head_exits_CFG C h) h p.
Proof.
  destruct Himpl;[left|right].
  - eapply head_exits_deq_loop_inv1. assumption.
  - destructH. exists e. split.
    + eapply head_exits_exited_inv1. assumption.
    + eapply head_exits_deq_loop_inv1. assumption.
Qed.


Fixpoint impl_list' `{C : redCFG} (r : Lab) (l : list Lab)
  := match l with
     | nil => nil
     | q :: l => match decision (deq_loop r q) with
               | left H => impl_of_original' (h:=r) (p:=q) (or_introl H) :: impl_list' r l
               | right H => match decision (exists e : Lab, exited q e /\ deq_loop r e) with
                           | left Q =>
                             match l with (* only preserve the head if it's the entry *)
                                      | nil => impl_of_original' (or_intror Q) :: impl_list' r l
                                      | q' :: l' => if decision (loop_contains q q')
                                                  then impl_list' r l
                                                  else impl_of_original' (or_intror Q) :: impl_list' r l
                             end
                           | right Q => impl_list' r l
                           end
               end
     end.

Ltac collapse_ioo x y :=
  replace (impl_of_original' x) with (impl_of_original' y);
  [|unfold impl_of_original'; f_equal; eapply pure_eq].

Ltac resolve_ioo_eq :=
  match goal with
    [ |- impl_of_original' ?H = impl_of_original' ?Q] =>
    unfold impl_of_original';f_equal;eapply pure_eq
  end.  


Lemma implode_nodes_edge `(C : redCFG) (h p q : Lab)
      (HPp : implode_nodes C h p)
      (HPq : implode_nodes C h q)
      (Hedge : edge p q = true)
  : edge__P (local_impl_CFG C h) (impl_of_original' HPp) (impl_of_original' HPq).
Proof.
  unfold edge__P.
  repeat rewrite is_true2_decision.
  rewrite restrict_edge_intersection. unfold_edge_op. cbn.
  eapply head_exits_CFG_implode_nodes_inv in HPp.
  eapply head_exits_CFG_implode_nodes_inv in HPq.
  unfold implode_nodes in *. cbn in *.
  firstorder.
Qed.

Definition impl_list'_cond1 `{C : redCFG} (h p : Lab) (l : list Lab) :=
  ~ deq_loop h p
      /\ (match hd_error l with
         | Some q => loop_contains p q
         | None => False
         end
         \/ ~ exists e, exited p e /\ deq_loop h e).

Definition impl_list'_cond2 `{C : redCFG} (h p : Lab) (l : list Lab) :=
  deq_loop h p
  \/ ((exists e, exited p e /\ deq_loop h e) /\ match hd_error l with
                                        | Some q => ~ loop_contains p q
                                        | None => True
                                        end).

Lemma impl_list'_spec1 `(C : redCFG) (h : Lab) (p : Lab) (l : list Lab)
  : impl_list'_cond1 h p l -> impl_list' h (p :: l) = impl_list' h l.
Proof.
  intro Q.
  cbn. unfold impl_list'_cond1 in Q.
  decide (deq_loop h p);destruct Q. 1:contradiction.
  decide (exists e, exited p e /\ deq_loop h e);destruct H0;try contradiction.
  - destruct l;cbn in H0;[contradiction|].
    decide (loop_contains p e0);auto. contradiction.
  - destruct l;cbn in H0;[contradiction|auto].
  - auto.
Qed.

Lemma impl_list'_spec2 `(C : redCFG) (h p : Lab) (l : list Lab)
      (Hp : implode_nodes C h p)
  : impl_list'_cond2 h p l
    -> impl_list' h (p :: l) = impl_of_original' (p:=p) Hp :: impl_list' h l.
Proof.
  intro Q.
  cbn. unfold impl_list'_cond2 in Q.
  decide (deq_loop h p). 1: f_equal;resolve_ioo_eq.
  destruct Q;[contradiction|]. destruct H. 
  decide (exists e, exited p e /\ deq_loop h e);[|contradiction].
  destruct l;cbn in H0;[f_equal;resolve_ioo_eq|].
  decide (loop_contains p e0);[contradiction|].
  f_equal;resolve_ioo_eq.
Qed.

Lemma impl_list'_spec_destr `(C : redCFG) (h p : Lab) (l : list Lab)
  : impl_list'_cond1 h p l \/ impl_list'_cond2 h p l.
Proof.
  unfold impl_list'_cond1,impl_list'_cond2.
  destruct l;cbn. all: decide (deq_loop h p);[right;firstorder|].
  - decide (exists e, exited p e /\ deq_loop h e);[|left;split;auto].
    right;right. auto. 
  - decide (exists e, exited p e /\ deq_loop h e);[|left;split;auto;right;auto].
    decide (loop_contains p e);
      [left;split;auto;left;auto|right;right;auto].
Qed.      

Require Import MaxPreSuffix.


Lemma impl_list'_remove `(C : redCFG) π ϕ h
      (Hnimpl : forall x, x ∈ π -> ~ implode_nodes C h x)
  : impl_list' h (π ++ ϕ) = impl_list' h ϕ.
Proof.
  induction π;[auto|].
  unfold app. fold (π ++ ϕ).
  rewrite impl_list'_spec1;eauto.
  unfold impl_list'_cond1.
  specialize (Hnimpl a). exploit Hnimpl. simpl_dec' Hnimpl. destructH.
  split;auto.
Qed.

Lemma path_postfix_nincl_in_loop' `(C : redCFG) a b h π x
      (Hpath : CPath a b π)
      (Hnincl : h ∉ π)
      (Hloop : loop_contains h b)
      (Hel : x ∈ π)
  : loop_contains h x.
Proof.
  decide (loop_contains h x);[auto|exfalso].
  eapply dom_loop_contains in Hloop. 2:eauto.
  eapply path_from_elem in Hel;eauto.
  destructH.
  eapply Hloop in Hel0. eapply postfix_incl in Hel1.
  eapply Hnincl. eapply Hel1. auto.
Qed.

Lemma path_postfix_nincl_in_loop `(C : redCFG) a b h π x
      (Hpath : CPath a b π)
      (Hloop : loop_contains h b)
      (Hpfn : x ∈ postfix_nincl h π)
  : loop_contains h x.
Proof.
  specialize (postfix_nincl_postfix h π) as Hpost.
  specialize (@postfix_nincl_nincl _ _ _ h π) as Hnincl.
  set (π' := postfix_nincl h π) in *.
  destruct π';[contradiction|].
  eapply path_postfix_nincl_in_loop'.
  2-4:eauto.
  rewrite cons_rcons' in Hpost. rewrite cons_rcons'.
  eapply path_postfix_path in Hpath;eauto.
Qed.

Lemma implode_nodes_path_inv' `(C : redCFG) (h : Lab) (Hhe : head_exits_property C h) p q π
      (Hpath : CPath p q π)
      (HPp : (implode_nodes C h) p)
      (HPq : (implode_nodes C h) q)
      (q' := impl_of_original' HPq)
  : exists ϕ, Path (edge__P (local_impl_CFG C h)) (impl_of_original' HPp) q' ϕ /\ impl_list' h π = ϕ.
Proof.
  revert dependent q. revert dependent π.
  specialize (well_founded_ind (R:=(@StrictPrefix' Lab)) (@StrictPrefix_well_founded Lab)
                               (fun π : list Lab => forall (q : Lab),
                                    CPath p q π ->
                                    forall HPq : implode_nodes C h q,
                                      let q' := impl_of_original' HPq in
                                      exists ϕ, Path (edge__P (local_impl_CFG C h))
                                                (impl_of_original' HPp) q' ϕ
                                           /\ impl_list' h π = ϕ
                               ))
    as WFind.
  eapply WFind.
  intros x IHwf ? Hpath Himpl q'. clear WFind.
  destruct Hpath.
  - exists ([q']). split.
    + subst q'. collapse_ioo HPp Himpl. econstructor.
    + cbn. decide (deq_loop h a);cbn.
      * f_equal. subst q'. resolve_ioo_eq.
      * decide (exists e, exited a e /\ deq_loop h e).
        -- subst q'. f_equal. resolve_ioo_eq.
        -- exfalso. destruct HPp;contradiction. 
  - decide ((implode_nodes C h) b).
    + specialize (IHwf π). exploit IHwf;[econstructor;econstructor|]. unfold q' in IHwf.
      destructH.
(*      specialize (impl_list'_spec_destr C h c π) as Hdestr.
      destruct Hdestr.*)
      assert (impl_list'_cond2 h c π).
      { unfold impl_list'_cond2. decide (deq_loop h c);[left;auto|].
        destruct Himpl;[contradiction|right;split;auto].
        destruct π eqn:E; [cbn;auto|].
        path_simpl' Hpath.
        intro N. eapply implode_nodes_inner_remove in N. 2:right;eapply e. 3: eapply p. 2:auto.
        subst. eapply no_self_loops;eauto.
      }
      copy H0 H0'.
      eapply impl_list'_spec2 in H0.
      eexists;split.
      econstructor;eauto 1.
      1: eapply implode_nodes_edge;eauto.
      rewrite H0. cbn. subst q'. rewrite IHwf1. reflexivity.
    + eapply edge_destruct in H. destruct H.
      * eapply impl_nimpl_ex_headexit in n as Hhexit;cycle 3;eauto.
        destruct Hhexit as [h' [Hhexit Hel]].
        eapply path_from_elem' in Hel;eauto. destructH.
        eapply postfix_eq in Hel1. destruct Hel1 as [π0 Hπ].
        assert (implode_nodes C h h') as Himpl'.
        {
          destruct Himpl.
          * right. exists c. split;[exists b|];eauto.
          * exfalso.
            destructH. eapply no_exit_head;eauto.
            unfold exited,exit_edge in e1; destructH. eauto using loop_contains_loop_head.
        }
        specialize (IHwf (h' :: π0)).
        assert (Prefix (h' :: π0) π).
        1: { eapply prefix_eq.
             exists (postfix_nincl h' π). rewrite Hπ at 1. setoid_rewrite <-app_cons_assoc at 1.
             reflexivity. }
        exploit' IHwf.
        {
          eapply prefix_ex_cons in H0. destructH. econstructor. cbn. eauto.
        }
        specialize (IHwf h').
        exploit' IHwf.
        { eapply path_prefix_path in H0;eauto. }
        exploit' IHwf. unfold q' in IHwf. destructH. 
        exists (q' :: ϕ). split.
        ++ unfold edge__P,a_edge__P.
           econstructor;eauto 1. 
           repeat rewrite is_true2_decision.
           rewrite restrict_edge_intersection. cbn.
           unfold_edge_op.
           split_conj;eauto 1.
           2,3: eapply head_exits_implode_nodes_inv1 with (C0:=C);eauto. 
           left. eapply a_edge_incl.
           eapply head_exits_property_a_edge;eauto.
           contradict n.
           eapply loop_contains_deq_loop in n.
           eapply eq_loop_exiting in Hhexit.
           unfold implode_nodes. cbn. left. 
           eapply eq_loop2;eauto.
        ++ subst q'.
           rewrite <-IHwf1.
           rewrite Hπ.
           rewrite <-app_cons_assoc.
           erewrite impl_list'_spec2;eauto.
           2: {
             unfold impl_list'_cond2.
             destruct Himpl;[left;auto|].
             exfalso. eapply no_exit_head;eauto.
             destructH. unfold exited,exit_edge in H2. destructH. eapply loop_contains_loop_head;eauto.
           } 
           rewrite impl_list'_remove.
           2: {
             intros. intro N. eapply implode_nodes_inner_remove in N as Hinir;cycle 1.
             - exact Himpl'.
             - contradict n. eapply deq_loop_exiting in Hhexit. left. transitivity h';eauto.
             - eapply path_postfix_nincl_in_loop;cycle 1.
               + unfold exit_edge in Hhexit. destructH. eapply Hhexit0.
               + eauto.
               + eauto. 
             - subst h'. eapply postfix_nincl_nincl;eauto.
           } 
           reflexivity.
      * decide (deq_loop h c).
        { exfalso. apply n. left. eapply back_edge_eq_loop in H. rewrite H. auto. }
        assert (c ∈ π) as Hel.
        {
          decide (a = c).
          { subst a. eapply path_contains_back;eauto. }
          assert (~ loop_contains c a).
          {
            intro N. clear IHwf.
            eapply implode_nodes_inner_remove in HPp;eauto.
          }
          eapply dom_loop_contains;eauto.
          eapply loop_contains_ledge;eauto.
        }
        eapply path_from_elem' in Hel;eauto. destructH.
        eapply postfix_eq in Hel1. destruct Hel1 as [π0 Hπ].
        specialize (IHwf (c :: π0)).
        assert (Prefix (c :: π0) π) as Hpre.
        { eapply prefix_eq. eexists. rewrite Hπ at 1. rewrite <-app_cons_assoc;reflexivity. }
        exploit' IHwf.
        { eapply prefix_ex_cons in Hpre. destructH. econstructor;cbn;eauto. }
        specialize (IHwf c).
        exploit' IHwf.
        { eapply path_prefix_path in Hpre;eauto. }
        exploit' IHwf. unfold q' in IHwf. destructH.
        exists ϕ;split;eauto.
        rewrite Hπ.
        rewrite <-IHwf1.
        rewrite <-app_cons_assoc.
        assert (forall y, y ∈ postfix_nincl c π -> loop_contains c y) as Hy.
        {
          intros. eapply path_postfix_nincl_in_loop;cycle 1.
          - eapply loop_contains_ledge;eauto.
          - eauto.
          - eauto.
        } 
        erewrite impl_list'_spec1;eauto.
        2: {
          unfold impl_list'_cond1. split;[auto|].
          left. destruct (postfix_nincl c π) eqn:E;cbn.
          - eapply loop_contains_self. eexists;eauto.
          - eapply Hy. rewrite E. left;auto.
        } 
        rewrite impl_list'_remove;auto.
        intros. intro N. eapply implode_nodes_inner_remove in N;cycle 1.
        ++ apply Himpl.
        ++ auto.
        ++ auto.
        ++ subst. eapply postfix_nincl_nincl. eauto.
Qed.
  
Lemma local_impl_CFG_path `(C : redCFG) (h p q : Lab) π
      (Hpath : CPath p q π)
      (Hp : implode_nodes C h p)
      (Hq : implode_nodes C h q)
  : exists ϕ, Path (edge__P (local_impl_CFG C h)) (impl_of_original' Hp) (impl_of_original' Hq) ϕ.
Proof.
  unfold local_impl_CFG.
  set (D := head_exits_CFG C h).
  eapply head_exits_CFG_path in Hpath.
  eapply head_exits_CFG_implode_nodes_inv in Hp as Hp'.
  eapply head_exits_CFG_implode_nodes_inv in Hq as Hq'.
  eapply implode_nodes_path_inv in Hpath;eauto.
  2: eapply head_exits_property_satisfied.
  unfold edge__P in *. destructH. repeat rewrite is_true2_decision in *.
  eapply restrict_edge_path_equiv in Hpath0.
  destruct (toSubList ϕ _);[contradiction|].
  exists (s :: l). eauto.
Qed.

Require Import Disjoint.

Lemma impl_list'2_implode_nodes `(C : redCFG) h p π
      (H : impl_list'_cond2 h p π)
  : implode_nodes C h p.
Proof.
  unfold impl_list'_cond2 in H. destruct H;[left;auto|]. destruct H. right;auto.
Qed.
  
Lemma impl_list_incl `(C : redCFG) h π
  : map (@proj1_sig _ _) (impl_list' h π) ⊆ π.
Proof.
  intros x Hx. eapply in_map_iff in Hx. destructH. rewrite <-Hx0. clear Hx0.
  revert dependent x0.
  induction π;intros.
  - cbn in Hx1. contradiction.
  - specialize (impl_list'_spec_destr _ h a π) as Hspec.
    destruct Hspec.
    + rewrite impl_list'_spec1 in Hx1;eauto.
    + destruct x0. push_purify p.
      erewrite impl_list'_spec2 in Hx1;eauto.
      destruct Hx1;eauto. rewrite <-H1. left. cbn. reflexivity.
      Unshelve.
      eapply impl_list'2_implode_nodes;eauto.
Qed.

Lemma impl_list_disj1 `(C : redCFG) h π ϕ
  : Disjoint π ϕ -> Disjoint (impl_list' h π) (impl_list' h ϕ).
Proof.
  intros.
  eapply disjoint_subset in H. 2,3: eapply impl_list_incl.
  eapply Disjoint_map_inj in H;eauto. 1: eapply H.
  unfold injective. intros. rewrite subtype_extensionality in H0. auto.
Qed.

Lemma impl_list_disjoint `(C : redCFG) h π ϕ s p q
      (Hπ : CPath s p (π :r: s))
      (Hϕ : CPath s q (ϕ :r: s))
      (Hdeq : deq_loop h s)
  : Disjoint π ϕ <-> Disjoint (impl_list' h π) (impl_list' h ϕ).
Proof.
  split;intros;[eapply impl_list_disj1;eauto|].
Admitted.

Lemma impl_CFG_deq_loop `(C : redCFG) (h : Lab) (p q : local_impl_CFG_type C h)
      (Hdeq : deq_loop (C:=C) (` p) (` q))
  : deq_loop (C:=local_impl_CFG C h) p q.
Proof.
  destruct p, q. cbn in Hdeq. push_purify p. push_purify p0.
  intros h' Hh.
  (* it holds because loop containment is equivalent for nodes that are present in the imploded case *)
Admitted. (* FIXME *)

Lemma impl_depth_self_eq `(C : redCFG) (q : Lab) (q' : local_impl_CFG_type C q)
      (Heq : eq_loop q (` q'))
  : depth (C:=local_impl_CFG C q) q' = depth q.
Admitted.

Lemma impl_depth_max `(C : redCFG) (q : Lab) (p : local_impl_CFG_type C q)
  : depth (C:=local_impl_CFG C q) p <= depth (C:=C) q.
Admitted.
