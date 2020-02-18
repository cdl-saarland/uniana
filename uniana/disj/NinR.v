Require Export DisjPaths.

Section disj.

  Context `{C : redCFG}.

  Infix "⊴" := Tagle (at level 70).

  Notation "p '-a>b' q" := (a_edge p q) (at level 55).
  Notation "p '-a>' q" := (p -a>b q = true) (at level 55).
  Notation "p '-->b' q" := (edge p q) (at level 55).
  Notation "p '-->' q" := (p -->b q = true) (at level 55, right associativity).

  Variable (t1 t2 : list (Lab * Tag)) (r1 r2 : list (Lab * Tag)) (q1 q2 s : Lab) (j1 j2 k : Tag).
  Hypotheses (Hlc : last_common' t1 t2 r1 r2 (s,k))
             (Hpath1 : TPath (root,start_tag) (q1,j1) t1)
             (Hpath2 : TPath (root,start_tag) (q2,j2) t2)
             (*           (Hneq : r1 <> r2) (* <-> r1 <> nil \/ r2 <> nil *)*)
             (Hloop : eq_loop q1 q2)
             (Htag : tl j1 = tl j2)
             (Htagleq : hd 0 j1 <= hd 0 j2). 

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
      eapply path_prefix_path in Hpath2;eauto.
      eapply path_postfix_path in Hlc0;eauto.
      eapply path_app' in Hlc0;eauto. cbn in Hlc0.
      eapply tpath_NoDup in Hlc0. clear - Hlc0 Hel H.
      rewrite <-app_assoc in Hlc0.
      eapply NoDup_app;eauto.
    - rewrite Hloop in Hcont.
      assert ((h,l) ∈ t1) as Hel'.
      { eapply postfix_incl;eauto.
        unfold last_common' in Hlc. destructH. eapply postfix_step_left;eauto.
      } 
      eapply loop_tag_dom;eauto.
      + rewrite <-tagle_jj.
        eapply tcfg_monotone_deq;eauto. rewrite <-Hloop in Hcont. eauto using loop_contains_deq_loop.
      + clear Hpath2. eapply tag_depth; eauto.
  Qed.
  
  Lemma r1_in_head_q : forall x, x ∈ r1 -> deq_loop (fst x) q1.
  Proof.
    intros (p,i) Hel h Hh.
    eapply loop_contains_innermost in Hh as Hinner. destructH.
    eapply eq_loop_innermost in Hinner as Hinner'; eauto.
    eapply innermost_loop_deq_loop;eauto. 2:eapply Hloop in Hh;auto.
    (*eapply path_front in Hpath1 as Hfront1.
    eapply path_front in Hpath2 as Hfront2.*)
    cbn. decide (loop_contains h' p);[auto|exfalso].
    eapply ex_entry with (i0:=i) in Hinner;eauto.
    2: {
      assert (t1 = (q1,j1) :: tl t1).
      { clear - Hpath1. induction Hpath1;cbn;eauto. }
      rewrite H. 
      econstructor. rewrite <-H. clear H.
      eapply splinter_single. 
      unfold last_common' in Hlc. destructH.
      eapply postfix_incl;eauto.
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
      rewrite app_cons_assoc.
      setoid_rewrite <-Hlc'0. Unset Printing Coercions.
      eapply tpath_NoDup;eauto.
    }
    eapply Hlc'1;eauto.
    eapply head_in_both;eauto.
    rewrite Hloop. destruct Hinner';auto.
  Qed.

  Lemma no_head : forall h', h' ∈ map fst r1 -> ~ loop_contains h' q1.
  Proof.
    intros h' Hel Hnin.
    eapply in_fst in Hel.
    destructH.
    eapply head_in_both in Hel as Hel';eauto.
    unfold last_common' in Hlc. destructH.
    eapply Hlc1;eauto.
  Qed.

  (* TODO : move *)
  Lemma path_rcons_rinv
    : forall (L : Type) (edge : L -> L -> Prop) (p q r : L) (π : list L),
      Path edge r p ((π :r: q) :r: r) -> Path edge q p (π :r: q).
  Proof.
    clear.
    intros. revert dependent p. induction π;cbn in *;intros.
    - path_simpl' H. econstructor.
    - path_simpl' H. inversion H;[congruence'|subst].
      econstructor;eauto.
  Qed.
  
  (* TODO: move *)
  Lemma only_inner_heads_tag_prefix p i q j l 
        (Hpath : TPath (p, i) (q, j) l)
        (Hnhead : forall (h' : Lab) (k' : Tag), (h',k') ∈ tl (rev l) -> loop_contains h' q -> False)
        (Hdeqq : forall (h' : Lab) (k' : Tag), (h',k') ∈ l -> deq_loop h' q)
    : Prefix j i.
  Proof.
    clear - Hpath Hnhead Hdeqq.
    remember (l) as l' in Hpath.
    assert (Postfix l' l) as Hpost by (rewrite Heql';econstructor;eauto).
    assert ((p,i) ∈ l') as Hel.
    { (rewrite Heql';eapply path_contains_back;subst;eauto). }
    remember p as p'. remember i as i'. rewrite Heqp' in Hpath. rewrite Heqi' in Hpath.
    clear Heql' Heqp' Heqi'.
    revert p' i' Hel p i Hpath.
    rinduction l'.
    - contradiction.
    - eapply In_rcons in Hel. destruct Hel.
      + subst a. 
        specialize (rcons_destruct l0) as Hl0. destruct Hl0;[|destructH];subst l0.
        * cbn in *.
          inversion Hpath;subst. 2: { inversion H4. }
          destruct l;[inversion Hpost;congruence'|]; eapply postfix_hd_eq in Hpost;
                                   inversion Hpost;subst;cbn.
          econstructor;auto.
        * destruct a.
          unfold TPath in Hpath. 
          assert ((p',i') ∈ l) as Helpi.
          { eapply postfix_incl;eauto. }
          replace i' with (snd (p',i')) by (cbn;auto).
          path_simpl' Hpath. cbn. copy Hpath Hpath'.
          eapply path_nlrcons_edge in Hpath.
          exploit' H.
          1: { eapply postfix_step_left;eauto. }
          specialize (H e t). exploit' H. specialize (H e t). exploit H.
          1: eapply path_rcons_rinv;eauto.
          eapply tcfg_edge_destruct in Hpath as Q.
          assert ((e,t) ∈ l) as Helet.
          { eapply postfix_incl;eauto. }
          destruct Q as [Q|[Q|[Q|Q]]]. all: subst. 
          -- eauto. (* normal *)
          -- inversion H;subst. (* entry *) 
             ++ exfalso.          
                specialize (Hdeqq p i). exploit Hdeqq.
                eapply deq_loop_depth in Hdeqq.
                assert (|i| < |0 :: i|) as Q by (cbn;omega). clear Helet.
                eapply tpath_depth_lt in Q; [| | |eapply path_contains_front];eauto.
                omega.
             ++ auto.                 
          -- inversion H.  (* back_edge *)
             ++ subst.
                destruct i. 1:cbn;econstructor.
                exfalso.
                eapply Hnhead.
                ** eapply postfix_rev_prefix in Hpost.
                   rewrite rev_rcons in Hpost.
                   eapply prefix_tl in Hpost.
                   eapply prefix_incl;eauto. rewrite rev_rcons. left. reflexivity.
                ** specialize (tag_back_edge_iff Hpath) as [Q _]. exploit Q;eauto.
                   eapply deq_loop_head_loop_contains.
                   --- eapply deq_loop_depth_eq.
                       +++ eapply Hdeqq;eauto.
                       +++ eapply tpath_depth_eq;eauto.
                           eapply path_contains_front;eauto.
                   --- exists p;eauto.
             ++ subst. destruct i.
                ** cbn in H0. congruence.
                ** inversion H0. subst. econstructor. eauto.
          -- clear - H;destruct i;cbn in *;[auto|]. inversion H;subst;econstructor;auto. 
      + destruct l0;[cbn in *;contradiction|].
        unfold TPath in Hpath. path_simpl' Hpath. cbn in Hpath. path_simpl' Hpath.
        eapply path_rcons_inv in Hpath. destructH. destruct p0.
        eapply H;eauto.
        eapply postfix_step_left;eauto.
  Qed.
  
  Lemma r1_tpath
    : TPath (s,k) (q1,j1) (r1 :r: (s,k)).
  Proof.
    unfold last_common' in Hlc. destructH.
    eapply postfix_path in Hlc0;eauto.
  Qed.

  Lemma r2_tpath
    : TPath (s,k) (q2,j2) (r2 :r: (s,k)).
  Proof.
    unfold last_common' in Hlc. destructH.
    eapply postfix_path in Hlc2;eauto.
  Qed.

  Lemma postfix_tl_rev (A : Type) (l l' : list A)
        (Hpost : Postfix l l')
    : Postfix (rev (tl (rev l))) (rev (tl (rev l'))).
  Proof.
    clear - Hpost.
    destr_r' l;subst;cbn.
    - eapply postfix_nil.
    - rewrite rev_rcons. cbn. eapply postfix_rev_prefix in Hpost.
      rewrite rev_rcons in Hpost. eapply prefix_tl in Hpost.
      eapply prefix_rev_postfix;eauto.
  Qed.
  
  Lemma prefix_tag_r1 p i
        (Hel : (p,i) ∈ (r1 :r: (s,k)))
    : Prefix j1 i.
  Proof.
    eapply path_from_elem in Hel;cycle 1.
    - eauto.
    - eapply r1_tpath.
    - destructH.
      eapply only_inner_heads_tag_prefix;eauto.
      + intros. eapply no_head;eauto.
        eapply postfix_incl.
        * eapply postfix_map.
          eapply postfix_tl_rev in Hel1. 
          rewrite rev_rcons in Hel1. cbn in Hel1. rewrite rev_involutive in Hel1. eauto.
        * eapply in_map with (f:=fst) in H. cbn in H. rewrite map_rev. rewrite <-in_rev. eauto.
      + intros. eapply postfix_incl in H;eauto.
        eapply In_rcons in H. destruct H.
        * inversion H;subst. eapply s_deq_q;eauto.
        * eapply r1_in_head_q in H. cbn in H. eauto.
  Qed.
  
  Lemma j1_prefix_k
    : Prefix j1 k.
  Proof.
    eapply prefix_tag_r1.
    eapply In_rcons. left. reflexivity.
  Qed.
  
  Lemma tl_j2_prefix_k
    : Prefix (tl j2) k.
  Proof.
    rewrite <-Htag. eapply prefix_trans.
    - eapply tl_prefix.
    - eapply j1_prefix_k.
  Qed.
  
  Lemma r2_in_head_q : forall x, x ∈ r2 -> deq_loop (fst x) q2.
  Proof.
    intros (p,i) Hel h Hh.
    eapply loop_contains_innermost in Hh as Hinner. destructH. 
    eapply eq_loop_innermost in Hinner as Hinner'; [|symmetry in Hloop];eauto.
    eapply innermost_loop_deq_loop;eauto. 2:eapply Hloop in Hh;auto.
    cbn. decide (loop_contains h' p);[auto|exfalso].
    eapply ex_entry with (i0:=i) in Hinner;eauto.
    2: {
      assert (t2 = (q2,j2) :: tl t2).
      { clear - Hpath2. induction Hpath2;cbn;eauto. }
      rewrite H. 
      econstructor. rewrite <-H. clear H.
      eapply splinter_single. 
      unfold last_common' in Hlc. destructH.
      eapply postfix_incl;eauto.
    }
    assert ((h',0 :: tl j2) ∈ r2) as Hr2.
    {
      eapply lc_succ_rt2;eauto. eapply tpath_NoDup;eauto.
    } 
    eapply ex_back_edge in Hpath2 as Hbacke;cycle 1.
    1: destruct Hinner';eauto.
    - eapply splinter_neq_strict.
      + eapply lc_succ_rt1.
        * eapply last_common'_sym. eauto.
        * eauto.
      + destruct r2;[contradiction|].
        intros N. setoid_rewrite <-N in Hlc. 
        unfold last_common' in Hlc.
        destructH.
        contradiction.
    - destruct Hinner'.
      eapply s_deq_q;cycle 2;eauto.
    - destructH.
      destruct l;[contradiction|].
      eapply PreOrder_Transitive in Hbacke1. exploit Hbacke1.
      { eapply prefix_tagle. eapply tl_j2_prefix_k. }                                   
      eapply tagle_prefix_hd_le in Hbacke0;eauto. 
      omega.
  Qed.

  
End disj.
