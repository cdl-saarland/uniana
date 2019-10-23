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

    Lemma ex_entry_r3 h i
          (Hel : (h,i) ∈ r3)
          (Hndeq : ~ deq_loop q1 h)
          (Hexit : exists e, exited h e /\ deq_loop q1 e)
      : (h,0 :: tl i) ∈ r3.
    Proof.
      specialize t3_tpath as Hpath3.
      eapply ex_entry_elem in Hpath3 as Hentry.
      - enough ((h, 0 :: tl i) ∈ (r3 :r: (s,k))).
        { eapply In_rcons in H. destruct H;[|auto].
          exfalso. inversion H. subst h.
          specialize (s_eq_q1) as Q. destruct Q. contradiction.
        }
        specialize t3_postfix as Hpre3.
        eapply postfix_eq in Hpre3. destructH.
        eapply succ_NoDup_app.
        3: eapply In_rcons;left;reflexivity.
        + setoid_rewrite <-Hpre3. eauto.
        + setoid_rewrite <-Hpre3. eapply tpath_NoDup;eauto.
      - split.
        + eapply loop_contains_self.
          destructH. unfold exited,exit_edge in Hexit0. destructH.
          eapply loop_contains_loop_head;eauto.
        + eapply deq_loop_refl.
      - rewrite s_eq_q1. contradict Hndeq. eapply loop_contains_deq_loop;eauto.
      - eapply lc_succ_rt1;eauto.
        instantiate (1:=r1). instantiate (1:=t1).
        unfold last_common' in *. destructH. split_conj;eauto.
        + eapply t3_postfix;eauto.
        + eapply Disjoint_sym. eapply disjoint3.
        + contradict Hlc5. eapply prefix_incl;eauto.
    Qed.
    
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
    eapply disj_node;[reflexivity|].
    unfold last_common' in Hlc. destructH.
    eapply postfix_path in Hpath2;eauto. 
    eapply path_front in Hpath2. rewrite Hjeq. eauto.
  Qed. 

  Global Instance Prefix_dec (A : eqType) (l l' : list A) : dec (Prefix l l').
  Proof.
    clear.
    revert l;induction l';intros l.
    - destruct l;[left; eapply prefix_nil|]. right. intro N. inversion N.
    - destruct (IHl' l).
      + left. econstructor;eauto.
      + decide (l = a :: l').
        * left. subst. econstructor.
        * right. contradict n. inversion n;subst;[contradiction|].
          eauto.
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
