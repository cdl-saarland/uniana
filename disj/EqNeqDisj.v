Require Export ImplodeTCFG NinR.

Section disj.

  Load X_notations.
  Load X_vars.

  Hypothesis (Hdep : depth s = depth q1).

  Lemma s_eq_q1
    : eq_loop s q1.
  Proof.
    eapply dep_eq_impl_head_eq in Hdep;eauto.
  Qed.
  
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


  Lemma impl_tlist_length h p i t
        (Hel : (p,i) ∈ impl_tlist h t)
    : @depth _ _ _ _ (local_impl_CFG C h) p <= depth h.
    clear - Hel.
  Admitted.

  Lemma impl_tlist_cons h p i t
        (Himpl : impl_list'_cond2 h p (map fst t))
    : exists i', impl_tlist h ((p,i) :: t)
            = (impl_of_original' (impl_list'2_implode_nodes Himpl),i') :: impl_tlist h t.
    clear - Himpl.
  Admitted.

  Lemma impl_tlist_tag_prefix p t h i i'
        (Himpl : impl_list'_cond2 h p (map fst t))
        (Heq : impl_tlist h ((p,i) :: t)
               = (impl_of_original' (impl_list'2_implode_nodes Himpl),i') :: impl_tlist h t)
    : Prefix i' i.
    clear - Himpl Heq.
  Admitted.

  Lemma prefix_antisym (A : Type) (l l' : list A)
        (H : Prefix l l')
        (Q : Prefix l' l)
    : l = l'.
  Proof.
    eapply prefix_eq in H.
    eapply prefix_eq in Q.
    do 2 destructH.
    rewrite Q in H.
    rewrite app_assoc in H.
    induction (l2'0 ++ l2') eqn:E.
    - destruct l2'0.
      + cbn in E. rewrite E in Q. cbn in Q. eauto.
      + cbn in E. congruence.
    - exfalso. cbn in H. clear - H.
      revert dependent a. revert l0. induction l';intros.
      + congruence.
      + destruct l0;cbn in H.
        * inversion H. subst. eapply IHl'. instantiate (1:=nil). cbn. eapply H2.
        * inversion H. subst. eapply IHl'. rewrite app_cons_assoc in H2.
          eapply H2.
  Qed.

  Global Instance Prefix_Transitive (A : Type) : Transitive (@Prefix A).
  Proof.
    unfold Transitive.
    eapply prefix_trans.
  Qed.

  Lemma prefix_length_leq (A : Type) (l l' : list A)
        (Hpre : Prefix l l')
    : | l | <= | l' |.
  clear - Hpre.
  Admitted.

  Lemma impl_tlist_prefix p i
        (Hel : (p,i) ∈ impl_tlist q1 r1)
    : i = j1.
  Proof.
    specialize (@prefix_tag_r1 _ _ _ _ _ t1 t2 r1 r2 q1 q2 s j1 j2 k Hpath1 Hpath2 Hlc) as Hpre.
    do 4 exploit' Hpre. clear - Hpre Hel Hpath1.
    induction r1;[cbn in Hel;contradiction|].
    destruct a as [q j].
    destruct (impl_list'_spec_destr _ q1 q (map fst l)).
    - eapply IHl;admit.
    - specialize (@impl_tlist_cons q1 q j l H) as Hcons.
      destructH.
      eapply impl_tlist_length in Hel as Hlen.
      rewrite Hcons in Hel.
      eapply impl_tlist_tag_prefix in Hcons as Hpre'.
      destruct Hel.
      + inversion H0. subst.
        exploit Hpre.
        { cbn. left. reflexivity. }
        eapply prefix_length_eq;eauto.
        eapply Nat.le_antisymm.
        * setoid_rewrite (@tag_depth (local_impl_CFG_type C q1)) at 1.
          setoid_rewrite (@tag_depth Lab).
          eapply Hlen.
          2: eapply Hpath1.
          2: eapply path_contains_front;eauto.
          all: admit.
        * setoid_rewrite (@tag_depth).
          eapply deq_loop_depth.
          all: admit.
      + eapply IHl;eauto.
        intros. eapply Hpre. cbn. right. unfold rcons in Hel. eauto.
  Admitted.
  
  Lemma same_tag_impl1 p i
        (Hel : (p,i) ∈ impl_tlist q1 r1)
    : i = j1.
  Proof.
    specialize (r1_tpath Hpath1 Hlc) as Hr1.
    clear - Hel Hr1.
    induction r1;cbn in Hel;[contradiction|].
    destruct a as [q j].
    decide (deq_loop q1 q).
    - cbn in Hr1. inversion Hr1. subst. destruct Hel.
      + inversion H. reflexivity.
      + eapply IHl;eauto.
    (* i can generalise the prefix j k  lemma *)
  Admitted.
End disj.

(** Close and reopen section to instantiate with other variables **)

Section disj.
  
  Load X_notations.
  Load X_vars.

  Hypothesis (Hdep : depth s = depth q1).

  Section same_tag.
    Variable (r3 : list (Lab * Tag)) (q3 : Lab).
    Hypotheses (Hpre : Prefix r3 r2) (Hhd : ne_front (r3 >: (s,k)) = (q3,j1)) (Hneq3 : r1 <> r3).

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

    Local Definition t3 := r3 >: (s,k) :+ prefix_nincl (s,k) t2.

    Lemma t3_postfix
      : Postfix (r3 :r: (s,k)) t3.
    Proof.
      eapply postfix_eq. exists (prefix_nincl (s,k) t2). unfold t3.
      rewrite <-nlconc_to_list. simpl_nl. reflexivity.
    Qed.

    Lemma t2_eq
      : t2 = r2 >: (s,k) :+ prefix_nincl (s,k) t2.
    Proof.
      unfold last_common' in Hlc. destructH.
      clear - Hpath2 Hlc2.
      eapply postfix_eq in Hlc2. destructH.
      enough (l2' = prefix_nincl (s,k) t2).
      { rewrite <-H. eapply ne_to_list_inj. rewrite <-nlconc_to_list. simpl_nl. eauto. }
      rewrite Hlc2. 
      eapply tpath_NoDup in Hpath2.
      setoid_rewrite Hlc2 in Hpath2. clear Hlc2.
      induction r2;cbn.
      - destruct (s == s).
        + destruct (k == k).
          * reflexivity.
          * congruence.
        + congruence.
      - destr_let. cbn in Hpath2. destruct (s == e).
        + destruct (k == t).
          * exfalso. inversion Hpath2.
            eapply H1. eapply in_or_app. left. eapply in_or_app. right. left.
            f_equal. rewrite e0. reflexivity.  rewrite e1. reflexivity.
          * eapply IHl. inversion Hpath2. unfold rcons. eauto.
        + eapply IHl.
          inversion Hpath2. unfold rcons. eauto.
    Qed.

    Lemma t3_prefix
      : Prefix t3 t2.
    Proof.
      rewrite t2_eq. eapply prefix_eq.
      unfold t3. eapply prefix_eq in Hpre as Hpre'. destructH' Hpre'.
      rewrite Hpre'. eexists.
      do 2 rewrite <-nlconc_to_list. simpl_nl. rewrite app_assoc.
      rewrite <-app_rcons_assoc. reflexivity.
    Qed.
    
    Lemma t3_tpath
      : TPath (root,start_tag) (q3,j1) t3.
    Proof.
      unfold t3.
      replace (prefix_nincl (s,k) t2) with (tl ((s,k) :: prefix_nincl (s,k) t2)) by (cbn;eauto).
      rewrite nlcons_to_list.
      eapply path_app.
      - eapply path_prefix_path;eauto.
        eapply prefix_eq. setoid_rewrite t2_eq at 1.
        rewrite <-nlconc_to_list. simpl_nl. rewrite <-app_cons_assoc. eexists. reflexivity.
      - simpl_nl. eapply r3_tpath.
    Qed.
    
    Lemma q3_eq_loop
      : eq_loop q3 q1.
    Proof.
      decide (r3 = []).
      { 
        subst. cbn in Hhd. inversion Hhd. subst.
        eapply s_eq_q1;eauto.
      }
      enough (deq_loop q3 q1).
      {
        split;auto.
        eapply deq_loop_depth_eq;eauto.
        setoid_rewrite <-tag_depth at 2.
        - erewrite tag_depth.
          + reflexivity.
          + eapply Hpath1.
          + eapply path_contains_front;eauto.
        - eapply t3_tpath.
        - eapply path_contains_front;eauto. eapply t3_tpath.
      }
      rewrite Hloop.
      replace q3 with (fst (q3,j1)) by (cbn;eauto).
      eapply r2_in_head_q.
      3: eapply Hlc.
      all:eauto.
      destruct r3;[contradiction|]. cbn in Hhd.
      eapply prefix_incl;eauto. left. eauto.
    Qed.

    Lemma last_common_t3_r3
      : last_common' t3 t1 r3 r1 (s,k).
    Proof.
      unfold last_common' in *. destructH. split_conj;eauto.
      - eapply t3_postfix;eauto.
      - eapply Disjoint_sym. eapply disjoint3.
      - contradict Hlc5. eapply prefix_incl;eauto.
    Qed.

    Hint Resolve t3_tpath t3_prefix t3_postfix last_common_t3_r3 q3_eq_loop.

    (** Now all properties of r1 or r3 also hold for r3, 
        we can use eapply3 to apply corresponding lemmas **)
    
    Ltac eapply3 H :=
      eapply H;
      try (lazymatch goal with
           | |- last_common' _ _ _ _ _ =>
             tryif eapply last_common_t3_r3
             then idtac
             else eapply last_common'_sym;eapply last_common_t3_r3
           end
          );
      try eapply Hpath1;try eapply Hpath2;try eapply t3_tpath;
      eauto;
      try (rewrite q3_eq_loop;eauto).
    
    Ltac eapply3' H Q :=
      eapply H in Q;
      try (lazymatch goal with
           | |- last_common' _ _ _ _ _ =>
             tryif eapply last_common_t3_r3
             then idtac
             else eapply last_common'_sym;eapply last_common_t3_r3
           end
          );
      try eapply Hpath1;try eapply Hpath2;try eapply t3_tpath;
      eauto;
      try (rewrite q3_eq_loop;eauto).

    Hint Rewrite q3_eq_loop.
    
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
        eapply ex_entry_r1 in Hlc as Hlc';eauto. cbn in Hlc'. 
        eapply3' ex_entry_r1 Htl';eauto.
        + cbn in Htl'.
          eapply disjoint3;eauto.
        + fold (Basics.flip deq_loop (`e) q3). rewrite q3_eq_loop. eauto.
        + exists e0. fold (Basics.flip deq_loop e0 q3). rewrite q3_eq_loop. eauto. 
    Qed.

    Lemma same_tag_impl3 p i
          (Hel : (p,i) ∈ impl_tlist q1 r3)
      : i = j1.
    Proof.
      eapply3 same_tag_impl1. 
      assert (implode_nodes C q1 s) as Himpl.
      { left. eapply s_eq_q1;eauto. }
      specialize r3_tpath as Hr3.
      eapply (impl_tlist_tpath) in Hr3.
      destructH.
      Unshelve. 4: eapply Himpl. 3: left;rewrite q3_eq_loop;reflexivity. 2:shelve.
      (* this proof could be finished by the use of isomorphism, 
         but it might be simpler to do it analogously to the same_tag_impl1 proof 
         isomorphism proof sketch: 
         show impl_tlist of r3 is a TPath for both q3 & q1 show tpath equivalence on isomorph CFGs
       *)
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
      eapply same_tag_impl1 in Hx1 as Ht. 2: eapply Hpath1. 2:admit.
      eapply same_tag_impl3 in Hx'1 as Ht0. subst.
      eapply disj_inst_impl;eauto.
    Admitted.

    Lemma disj_node
      : Disjoint (map fst r1) (map fst r3).
    Proof.
      specialize (r1_tpath Hpath1 Hlc) as r1_tpath'.
      eapply impl_list_disjoint.
      1: specialize (TPath_CPath r1_tpath') as HQ.
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
    eapply disj_node; [reflexivity| |eauto].
    unfold last_common' in Hlc. destructH.
    eapply postfix_path in Hpath2;eauto. 
    eapply path_front in Hpath2. rewrite Hjeq. eauto.
  Qed. 

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
