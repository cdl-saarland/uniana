Require Export DisjPaths.

Section disj.
  Context `{C : redCFG}.
  
  Infix "⊴" := Tagle (at level 70).
  
  Notation "p '-a>b' q" := (a_edge p q) (at level 55).
  Notation "p '-a>' q" := (p -a>b q = true) (at level 55).
  Notation "p '-->b' q" := (edge p q) (at level 55).
  Notation "p '-->' q" := (p -->b q = true) (at level 55, right associativity).

  Variable (t1 t2 : ne_list (Lab * Tag)) (r1 r2 : list (Lab * Tag)) (q1 q2 s : Lab) (j1 j2 k : Tag).
  Hypotheses (Hpath1 : TPath (root,start_tag) (q1,j1) t1)
             (Hpath2 : TPath (root,start_tag) (q2,j2) t2)
             (Hlc : last_common' t1 t2 r1 r2 (s,k))
             (Hneq : r1 <> r2) (* <-> r1 <> nil \/ r2 <> nil *)
             (Hloop : eq_loop q1 q2)
             (Htag : tl j1 = tl j2)
             (Htagleq : hd 0 j1 <= hd 0 j2).

  Lemma tagle_jj
    : j1 ⊴ j2.
  Admitted.
  
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
  

  Lemma tl_prefix (A : Type) (l : list A)
    : Prefix (tl l) l.
  Proof.
    induction l;cbn;econstructor;eauto. econstructor.
  Qed.

  Lemma ident p i q j l 
        (Hpath : TPath (p, i) (q, j) l)
        (Hnhead : forall (h' : Lab) (k' : Tag), (h',k') ∈ l -> loop_contains h' q -> (h',k') = (p,i))
        (Hdeqq : forall (h' : Lab) (k' : Tag), (h',k') ∈ l -> deq_loop h' q)
    : Prefix j i.
    clear - Hpath Hnhead Hdeqq.
    remember l as l'.
    remember (q,j) as qj.
    remember (p,i) as pi.
    copy Hpath Hpath'.
    rewrite Heql' in Hpath. rewrite Heqqj in Hpath. rewrite Heqpi in Hpath.
    assert (Prefix l' l) as Hpre by (subst l;econstructor;eauto).
    rewrite Heql' in Hnhead,Hdeqq. rewrite Heqpi in Hnhead.
    replace j with (snd qj) by (subst;cbn;eauto).
    assert (deq_loop p (fst qj)) as Hdeqp.
    { rewrite Heqqj. cbn. eapply Hdeqq. eapply path_contains_back;eauto. }
    clear Heql' Heqqj Heqpi.
    revert dependent l.
    revert p i q j Hdeqp.
    induction Hpath';intros;subst.
    - destr_r l.
      eapply prefix_single in Hpre. simpl_nl' Hpre. subst a l.
      eapply path_back in Hpath. simpl_nl' Hpath. subst a0. cbn. constructor.
    - destruct b,c. cbn in IHHpath'. cbn.
      eapply tcfg_edge_destruct in H as Q. destruct Q as [Q|[Q|[Q|Q]]].
      + subst t0. eapply IHHpath';eauto. admit. 
        eapply prefix_cons;eauto.
      + eapply tag_entry_iff in Q;eauto. cbn in Hdeqp. admit.
      + eapply tag_back_edge_iff in Q;eauto. admit.
      + subst t0. eapply prefix_trans;[eapply tl_prefix|]. eapply IHHpath';eauto.
        admit.
        eapply prefix_cons;eauto.        
  Admitted.
  
  Lemma j1_prefix_k
    : Prefix j1 k.
  Proof.
    unfold last_common' in Hlc.
    destructH.
    specialize (no_head) as Hnhead.
    specialize (r1_in_head_q) as Hdeqq.
    rewrite rcons_nl_rcons in Hlc0.
    eapply path_postfix_path in Hpath1 as Hpath1';eauto. simpl_nl' Hpath1'.
    eapply ident;eauto.
    intros. decide ((h',k') = (s,k));[auto|exfalso].
    simpl_nl' H. eapply In_rcons in H. destruct H;[contradiction|].
    eapply Hnhead;eauto. 1,2: intros; replace h' with (fst (h',k')) by (cbn;auto). eapply in_map;auto.
    simpl_nl' H. eapply In_rcons in H. destruct H.
    - rewrite H. cbn. eapply s_deq_q;eauto.
    - eapply Hdeqq. eauto.
  Qed.

  Lemma tl_j2_prefix_k
    : Prefix (tl j2) k.
  Proof.
    rewrite <-Htag. eapply prefix_trans.
    - eapply tl_prefix.
    - eapply j1_prefix_k.
  Qed.

  Lemma prefix_tagle (i j : Tag)
        (Hpre : Prefix i j)
    : i ⊴ j.
  Admitted.

  Lemma tagle_tagle_hd_eq (n m : nat) (i j : Tag)
        (H1 : n :: i ⊴ k)
        (H2 : m :: j ⊴ k)
    : n = m.
  Admitted.
  
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
      eapply prefix_tagle in Hbacke0.
      eapply PreOrder_Transitive in Hbacke1. exploit Hbacke1.
      { eapply prefix_tagle. eapply tl_j2_prefix_k. }
      eapply tagle_tagle_hd_eq in Hbacke0;eauto.
      omega.
  Qed.

  
End disj.
