Require Export ImplodeTCFG NinR.


Section disj.

  Load X_notations.
  Load X_vars.
  
  Lemma r1_tpath
    : TPath (s,k) (q1,j1) (r1 >: (s,k)).
  Proof.
    unfold last_common' in Hlc. destructH.
    eapply postfix_path in Hlc0;eauto.
  Qed.

  Lemma prefix_tag_r1 p i
        (Hel : (p,i) ∈ r1)
    : Prefix j1 i.
  Admitted.

  Hypothesis (Hdep : depth s = depth q1).

  Lemma s_eq_q1
    : eq_loop s q1.
  Proof.
    eapply dep_eq_impl_head_eq in Hdep;eauto.
  Qed.

  (* this lemma relies on Hdep ! *)
  Lemma ex_entry_r1 h i
        (Hel : (h,i) ∈ r1)
        (Hndeq : ~ deq_loop q1 h)
        (Hexit : exists e : Lab, exited h e /\ deq_loop q1 e)
    : (h,0 :: tl i) ∈ r1.
  Proof.
    eapply ex_entry_elem in Hpath1 as Hentry.
    - enough ((h, 0 :: tl i) ∈ (r1 :r: (s,k))).
      { eapply In_rcons in H. destruct H;[|auto].
        exfalso. inversion H. subst h.
        specialize (s_eq_q1) as Q. destruct Q. contradiction.
      }
      unfold last_common' in Hlc.
      destructH.
      eapply postfix_eq in Hlc0. destructH' Hlc0.
      eapply succ_NoDup_app.
      3: eapply In_rcons;left;reflexivity.
      + setoid_rewrite <-Hlc0. eauto.
      + setoid_rewrite <-Hlc0. eapply tpath_NoDup;eauto.
    - split.
      + eapply loop_contains_self.
        destructH. unfold exited,exit_edge in Hexit0. destructH.
        eapply loop_contains_loop_head;eauto.
      + eapply deq_loop_refl.
    - rewrite s_eq_q1. contradict Hndeq. eapply loop_contains_deq_loop;eauto.
    - eapply lc_succ_rt1;eauto.
  Qed.

  Section same_tag.
    Variable (r3 : list (Lab * Tag)) (q3 : Lab).
    Hypotheses (Hpre : Prefix r3 r2) (Hhd : ne_front (r3 >: (s,k)) = (q3,j1)).

    Lemma r3_tpath
      : TPath (s,k) (q3,j1) (r3 >: (s,k)).
    Proof.
      unfold last_common' in Hlc. destructH.
      eapply postfix_path in Hlc2;eauto.
      eapply path_prefix_path in Hlc2.
      2: { simpl_nl. eapply prefix_rcons. eauto. }
      rewrite Hhd in Hlc2. eauto.
    Qed.

    Lemma disjoint3
      : Disjoint r1 r3.
    Proof.
      eapply disjoint_subset.
      - reflexivity.
      - eapply prefix_incl;eauto.
      - unfold last_common' in Hlc. destructH. eauto.
    Qed.

    Lemma ex_entry_r3 h i
          (Hel : (h,i) ∈ r3)
          (Hexit : exists e, exited h e /\ deq_loop q1 e)
      : (h,0 :: tl i) ∈ r3.
    Admitted.
    
    Lemma disj_inst_impl
      : Disjoint (impl_tlist q1 r1) (impl_tlist q1 r3).
    Proof.
      (* this is not trivial because implosion can project loops with different tags 
       * on the same intstance *)
      intros x Hx Hx'.
      destruct x. 
      specialize (impl_tlist_in Hx) as Htl.
      specialize (impl_tlist_in Hx') as Htl'.
      decide (deq_loop q1 (` e)).
      - eapply disjoint3;eauto.
      - eapply impl_tlist_implode_nodes in Hx as Himpl.
        destruct Himpl ;[contradiction|].
        do 3 destructH.
        eapply ex_entry_r1 in Htl;eauto. cbn in Htl.
        eapply ex_entry_r3 in Htl';eauto. cbn in Htl'.
        eapply disjoint3;eauto.
    Qed.

    Lemma same_tag_impl1 p i
          (Hel : (p,i) ∈ impl_tlist q1 r1)
      : i = j1.
      (* i can generalise the prefix j k  lemma *)
    Admitted.

    Lemma same_tag_impl3 p i
          (Hel : (p,i) ∈ impl_tlist q1 r3)
      : i = j1.
    Admitted.

    Lemma disj_node_impl
      : Disjoint (impl_list' q1 (map fst r1)) (impl_list' q1 (map fst r3)).
    Proof.
      erewrite <-impl_list_impl_tlist.
      erewrite <-impl_list_impl_tlist.
      intros x Hx Hx'.
      eapply in_map_iff in Hx.
      eapply in_map_iff in Hx'.
      destructH' Hx. destructH' Hx'. subst.
      destruct x0,x1. unfold fst in *. subst.
      eapply same_tag_impl1 in Hx1 as Ht.
      eapply same_tag_impl3 in Hx'1 as Ht0. subst.
      eapply disj_inst_impl;eauto.
    Qed.

    Lemma disj_node
      : Disjoint (map fst r1) (map fst r3).
    Proof.
      eapply impl_list_disjoint.
      1: specialize (TPath_CPath r1_tpath) as HQ.
      2: specialize (TPath_CPath r3_tpath) as HQ.
      1,2:cbn in HQ;rewrite ne_map_nl_rcons in HQ;eauto. (* <-- Hdep *)
      - eapply dep_eq_impl_head_eq in Hdep;eauto; destruct Hdep as [_ Hdep'];eauto.
      - eapply disj_node_impl.
    Qed.
  End same_tag.

  Lemma lc_eq_disj
        (Hjeq : j1 = j2)
    : Disjoint (map fst r1) (map fst r2).
  Proof.
    eapply disj_node;[reflexivity|].
    unfold last_common' in Hlc. destructH.
    eapply postfix_path in Hpath2;eauto. 
    eapply path_front in Hpath2. rewrite Hjeq. eauto.
  Qed. 

  Global Instance Prefix_dec (A : eqType) (l l' : list A) : dec (Prefix l l').
  clear.
  revert l.
  induction l';intros l.
  - destruct l;[left; eapply prefix_nil|]. right. intro N. inversion N.
  - destruct l.
    + left. eapply prefix_nil. 
    + decide (a = e).
      * subst. destruct (IHl' (e :: l)).
        -- left. econstructor. eauto.
        -- decide (l = l').
           ++ left. subst. econstructor.
           ++ right. contradict n0. inversion n0;eauto.
              subst. contradiction.
      * admit.
  Admitted. 
  
  Lemma lc_neq_disj
        (Hjneq : j1 <> j2)
    : exists r', Prefix ((get_innermost_loop' q1) :: r') (map fst r2)
            /\ Disjoint (map fst r1) r'.
  Proof.
    exists (map fst (while (DecPred (fun x : Coord => Prefix j1 (snd x))) r2)).
    split.
    - admit. (*bc j1 <> j2 the front of while... is not (_,q2), thus strictly a prefix and 
               a backedge source *)
    - eapply disj_node.
      + eapply while_prefix. reflexivity.
      + (* bc backedge source front of while... has tag j1 *) admit.
  Admitted.

End disj.
