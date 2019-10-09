Require Export DisjPaths.

Section disj.

  Load X_notations.
  Load X_vars.

  Lemma length_jj
    : | j1 | = | j2 |.
  Proof.
    erewrite tag_depth;cycle 1.
    - eapply Hpath1.
    - eapply path_contains_front;eauto.
    - erewrite tag_depth;cycle 1.
      + eapply Hpath2.
      + eapply path_contains_front;eauto.
      + destruct Hloop.
        eapply Nat.le_antisymm;eapply deq_loop_depth;eauto.
  Qed.

  Lemma tagle_jj
    : j1 ⊴ j2.
  Proof.
    specialize (length_jj) as Hlen.
    clear - Htag Htagleq Hlen.
    destruct j1,j2;cbn in *;subst.
    - reflexivity.
    - omega.
    - omega.
    - eapply Tagle_cons2. auto.
  Qed.
  
  Lemma head_in_both (h : Lab) (l : Tag)
        (Hcont : loop_contains h q1)
        (Hel : (h,l) ∈ r1)
    : (h,l) ∈ r2.
  Proof.
    enough ((h,l) ∈ t2).
    - unfold last_common' in Hlc.
      destructH.
      eapply postfix_eq in Hlc2 as Hlc2. destructH' Hlc2.
      rewrite Hlc2 in H.
      rewrite <-app_cons_assoc in H. eapply in_app_or in H. destruct H;[auto|exfalso].
      clear - Hlc2 Hlc0 Hcont H Hpath1 Hpath2 Hel.
      rewrite <-app_cons_assoc in Hlc2.
      assert (Prefix ((s,k) :: l2') t2) as Hpre.
      { eapply prefix_eq. eexists;eauto. }
      rewrite nlcons_to_list in Hpre. eapply path_prefix_path in Hpath2;eauto.
      rewrite rcons_nl_rcons in Hlc0. eapply path_postfix_path in Hlc0;eauto.
      simpl_nl' Hpath2. simpl_nl' Hlc0.
      eapply path_app in Hlc0;eauto. cbn_nl' Hlc0.
      eapply tpath_NoDup in Hlc0. clear - Hlc0 Hel H.
      rewrite <-nlconc_to_list in Hlc0. simpl_nl' Hlc0.
      unfold rcons in Hlc0. rewrite <-app_assoc in Hlc0.
      eapply NoDup_app;eauto.
    - rewrite Hloop in Hcont.
      assert ((h,l) ∈ t1) as Hel'.
      { eapply postfix_incl;eauto.
        unfold last_common' in Hlc. destructH. eapply postfix_step_left;eauto.
      } 
      eapply loop_tag_dom;eauto.
      + rewrite <-tagle_jj. eapply tagle_monotone;eauto.
        eapply path_to_elem in Hel';eauto. destructH.
        eapply deq_loop_le;eauto.
        eapply loop_contains_deq_loop. rewrite Hloop. eauto.
      + clear Hpath2. eapply tag_depth; eauto.
  Qed.
  
  Lemma r1_in_head_q (* unused *): forall x, x ∈ r1 -> deq_loop (fst x) q1.
  Proof.
    intros (p,i) Hel h Hh.
    eapply loop_contains_innermost in Hh as Hinner. destructH.
    eapply eq_loop_innermost in Hinner as Hinner'; eauto.
    eapply innermost_loop_deq_loop;eauto. 2:eapply Hloop in Hh;auto.
    eapply path_front in Hpath1 as Hfront1.
    eapply path_front in Hpath2 as Hfront2.
    cbn. decide (loop_contains h' p);[auto|exfalso].
    eapply ex_entry with (i0:=i) in Hinner;eauto.
    2: {
      assert (t1 = (q1,j1) :< tl t1).
      { clear - Hpath1. induction Hpath1;cbn;eauto. simpl_nl. reflexivity. }
      rewrite H. simpl_nl.
      econstructor. setoid_rewrite nlcons_to_list at 2. rewrite <-H. clear H.
      eapply splinter_single. 
      unfold last_common' in Hlc. destructH.
      eapply postfix_incl;eauto.
      eapply In_rcons. eauto.
    }
    copy Hlc Hlc'.
    unfold last_common' in Hlc'. destructH.
    assert ((h', 0 :: tl j1) ∈ r1) as Hhel.
    {
      clear - Hinner Hlc'0 Hpath1 Hel.
      eapply splinter_in in Hinner as Hel'.
      eapply postfix_eq in Hlc'0. destructH.
      rewrite <-app_cons_assoc in Hlc'0.
      setoid_rewrite Hlc'0 in Hinner.
      eapply succ_NoDup_app;eauto. Set Printing Coercions.
      rewrite app_cons_assoc in Hlc'0. 
      rewrite rcons_nl_rcons in Hlc'0.
      rewrite nlconc_to_list in Hlc'0.
      eapply ne_to_list_inj in Hlc'0.
      rewrite app_cons_assoc.
      rewrite rcons_nl_rcons.
      rewrite nlconc_to_list. 
      setoid_rewrite <-Hlc'0. Unset Printing Coercions.
      eapply tpath_NoDup;eauto.
    }
    eapply Hlc'1;eauto.
    eapply head_in_both;eauto.
    rewrite Hloop. destruct Hinner';auto.
  Qed.

  Lemma no_head (* unused *): forall h', h' ∈ map fst r1 -> ~ loop_contains h' q1.
  Proof.
    intros h' Hel Hnin.
    eapply in_fst in Hel.
    destructH.
    eapply head_in_both in Hel as Hel';eauto.
    unfold last_common' in Hlc. destructH.
    eapply Hlc1;eauto.
  Qed.

  Lemma only_inner_heads_tag_prefix p i q j l 
        (Hpath : TPath (p, i) (q, j) l)
        (Hnhead : forall (h' : Lab) (k' : Tag), (h',k') ∈ tl (rev l) -> loop_contains h' q -> False)
        (Hdeqq : forall (h' : Lab) (k' : Tag), (h',k') ∈ l -> deq_loop h' q)
    : Prefix j i.
    clear - Hpath Hnhead Hdeqq.
    remember (ne_to_list l) as l' in Hpath.
    assert (Postfix l' l) as Hpost by (rewrite Heql';econstructor;eauto).
    assert ((p,i) ∈ l') as Hel by (rewrite Heql';eapply path_contains_back;eauto).
    remember p as p'. remember i as i'. rewrite Heqp' in Hpath. rewrite Heqi' in Hpath.
    clear Heql' Heqp' Heqi'.
    revert p' i' Hel.
    rinduction l'.
    - contradiction.
    - eapply In_rcons in Hel. destruct Hel.
      + subst a.
        specialize (rcons_destruct l0) as Hl0. destruct Hl0;[|destructH];subst l0.
        * cbn in *.
          inversion Hpath;subst;eapply postfix_hd_eq in Hpost;
            inversion Hpost;subst;cbn.
          -- econstructor;auto.
          -- clear. induction j;cbn;econstructor;auto. 
        * copy Hpost Hpost'.
          eapply postfix_path in Hpost;eauto.
          rewrite rcons_nl_rcons in Hpost.
          simpl_nl' Hpost.
          eapply path_nlrcons_edge in Hpost. simpl_nl' Hpost.
          destruct a.
          exploit' H.
          1: { eapply postfix_step_left;eauto. }
          specialize (H e t). exploit H.
          1: { eapply In_rcons;left;auto. }
          eapply tcfg_edge_destruct in Hpost as Q.
          assert ((p',i') ∈ l) as Helpi.
          { eapply postfix_incl;eauto. eapply In_rcons;eauto. }
          assert ((e,t) ∈ l) as Helet.
          { eapply postfix_incl;eauto.  eapply In_rcons;eauto. right. eapply In_rcons;eauto. }
          destruct Q as [Q|[Q|[Q|Q]]];subst.
          -- auto. (* normal *)
          -- inversion H;subst. (* entry *)
             ++ exfalso.
                specialize (Hdeqq p' i'). exploit Hdeqq.
                eapply deq_loop_depth in Hdeqq.
                assert (|i'| < |0 :: i'|) as Q by (cbn;omega). clear Helet.
                eapply tpath_depth_lt in Q;[| | |eapply path_contains_front];eauto. omega.
             ++ auto.                 
          -- inversion H.  (* back_edge *)
             ++ subst.
                exfalso.
                eapply Hnhead.
                ** eapply postfix_rev_prefix in Hpost'.
                   rewrite rev_rcons in Hpost'.
                   eapply prefix_tl in Hpost'.
                   eapply prefix_incl;eauto. rewrite rev_rcons. left. reflexivity.
                ** eapply tag_back_edge_iff in Q;eauto.
                   assert ((e,t) ∈ l) as Hel.
                   { eapply postfix_incl;eauto.
                     eapply In_rcons. right. eapply In_rcons. left;reflexivity. }
                   eapply deq_loop_head_loop_contains.
                   --- eapply deq_loop_depth_eq.
                       +++ eapply Hdeqq;eauto.
                       +++ 
                           eapply tpath_depth_eq;eauto.
                           eapply path_contains_front;eauto.
                   --- exists p';eauto.
             ++ subst. destruct i';cbn in Q;[contradiction|].
                inversion Q. subst. econstructor. eauto.
          -- clear - H;destruct i';cbn in *;[auto|]. inversion H;subst;econstructor;auto.
      + eapply H;eauto.
        eapply postfix_step_left;eauto.
  Qed.
  
  Lemma j1_prefix_k
    : Prefix j1 k.
  Proof.
    unfold last_common' in Hlc.
    destructH.
    specialize (no_head) as Hnhead.
    specialize (r1_in_head_q) as Hdeqq.
    rewrite rcons_nl_rcons in Hlc0.
    eapply path_postfix_path in Hpath1 as Hpath1';eauto. simpl_nl' Hpath1'.
    eapply only_inner_heads_tag_prefix;eauto.
    { simpl_nl. rewrite rev_rcons. cbn. setoid_rewrite <-in_rev. intros.
      eapply Hnhead. eapply in_map;eauto. cbn. eauto. }
    intros. simpl_nl' H. eapply In_rcons in H. destruct H.
    - inversion H;subst. eapply s_deq_q;eauto.
    - specialize (Hdeqq (h',k')). cbn in Hdeqq. eauto. 
  Qed.

  Lemma tl_j2_prefix_k
    : Prefix (tl j2) k.
  Proof.
    rewrite <-Htag. eapply prefix_trans.
    - eapply tl_prefix.
    - eapply j1_prefix_k.
  Qed.
  
  Lemma r2_in_head_q (* unused *): forall x, x ∈ r2 -> deq_loop (fst x) q2.
  Proof.
    intros (p,i) Hel h Hh.
    eapply loop_contains_innermost in Hh as Hinner. destructH. 
    eapply eq_loop_innermost in Hinner as Hinner'; [|symmetry in Hloop];eauto.
    eapply innermost_loop_deq_loop;eauto. 2:eapply Hloop in Hh;auto.
    eapply path_front in Hpath1 as Hfront1.
    eapply path_front in Hpath2 as Hfront2.
    cbn. decide (loop_contains h' p);[auto|exfalso].
    eapply ex_entry with (i0:=i) in Hinner;eauto.
    2: {
      assert (t2 = (q2,j2) :< tl t2).
      { clear - Hpath2. induction Hpath2;cbn;eauto. simpl_nl. reflexivity. }
      rewrite H. simpl_nl.
      econstructor. setoid_rewrite nlcons_to_list at 2. rewrite <-H. clear H.
      eapply splinter_single. 
      unfold last_common' in Hlc. destructH.
      eapply postfix_incl;eauto.
      eapply In_rcons. eauto.
    }
    assert ((h',0 :: tl j2) ∈ r2) as Hr2.
    {
      eapply lc_succ_rt2;eauto. eapply tpath_NoDup;eauto.
    } 
    eapply ex_back_edge in Hpath2 as Hbacke;cycle 1.
    2: destruct Hinner';eauto.
    - eapply lc_succ_rt1.
      + eapply last_common'_sym. eauto.
      + eauto. 
    - destruct r2;[contradiction|].
      intros N. setoid_rewrite <-N in Hlc. 
      unfold last_common' in Hlc.
      destructH.
      contradiction.
    - destruct Hinner'.
      eapply s_deq_q;cycle 2;eauto.
    - destructH.
      destruct l;[contradiction|].
(*      eapply prefix_tagle in Hbacke0.*)
      eapply PreOrder_Transitive in Hbacke1. exploit Hbacke1.
      { eapply prefix_tagle. eapply tl_j2_prefix_k. }                                   
      eapply tagle_prefix_hd_le in Hbacke0;eauto. 
      omega.
  Qed.

  
End disj.
