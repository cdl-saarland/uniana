Require Export DisjDef MaxPreSuffix.

Section disj.
  Context `{C : redCFG}.
  
  Infix "⊴" := Tagle (at level 70).
  
  Notation "p '-a>b' q" := (a_edge p q) (at level 55).
  Notation "p '-a>' q" := (p -a>b q = true) (at level 55).
  Notation "p '-->b' q" := (edge p q) (at level 55).
  Notation "p '-->' q" := (p -->b q = true) (at level 55, right associativity).

  (* TODO: remove *)
  Definition prec_loop_contains (qh q : Lab) (k j : Tag)
    := exists (p : Lab) (π : ne_list Coord),
      p ↪ qh /\ TPath (q,j) (p,k) π /\ qh ∉ tl (rev (map fst π)).

  (* TODO: remove *) 
  Definition prec_loop_contains' (qh q : Lab) (k j : Tag)
    := loop_contains qh q /\ Prefix j k /\
       exists π p i, TPath (root,start_tag) (p,i) π /\ (qh,k) ∈ π /\ (q,j) ∈ π.

  Lemma geq_tag_suffix_deq (p q : Lab) l t i j
        (Hpath : TPath (root,start_tag) (q,j) t)
        (Hpost : Postfix l t)
        (HForall : Forall (DecPred (fun xl => |j| <= |snd xl|)) l)
        (Hel : (p,i) ∈ l)
    : deq_loop p q.
  Proof.
    rewrite Forall_forall in HForall. cbn in HForall.
    revert dependent t. revert dependent p. revert i.
    rinduction l.
    - contradiction.
    - eapply In_rcons in Hel. destruct Hel.
      + subst a.
        specialize (rcons_destruct l0) as Hl0. destruct Hl0;[|destructH];subst l0.
        * cbn in *.
          inversion Hpath;subst;eapply postfix_hd_eq in Hpost;
            inversion Hpost;subst;eapply deq_loop_refl.
        * copy Hpost Hpost'.
          eapply postfix_path in Hpost;eauto.
          rewrite rcons_nl_rcons in Hpost.
          simpl_nl' Hpost.
          eapply path_nlrcons_edge in Hpost. simpl_nl' Hpost.
          destruct a.
          destruct (tag_deq_or_entry Hpost) as [Hdeq|Hentry].
          -- eapply deq_loop_trans;eauto. eapply H;eauto.
             ++ intros;eauto. eapply HForall. eapply In_rcons. right;auto.
             ++ eapply In_rcons;eauto.
             ++ eapply postfix_step_left;eauto.
          -- eapply tag_entry_iff in Hentry;eauto. subst t0.
             assert (|j| <= |i|) as Hleq.
             { specialize (HForall (p,i));cbn in HForall.
               eapply HForall. eapply In_rcons. left;reflexivity.
             }
             intros h Hloop.
             decide (h = e).
             ++ subst h. exfalso.
                assert (|j| < |0 :: i|) as Hleq'.
                { cbn. omega. }
                eapply loop_contains_deq_loop in Hloop.
                eapply deq_loop_depth in Hloop.
                enough (|0 :: i| <= |j|) by omega.
                erewrite tag_depth;eauto.
                erewrite tag_depth;eauto.
                ** inversion Hpath;cbn;auto.
                ** eapply postfix_incl;eauto. eapply In_rcons. right. eapply In_rcons. left;auto.
             ++ eapply preds_in_same_loop;cycle 1;eauto 1.
                ** eapply tcfg_edge_spec in Hpost. destructH. auto.
                ** eapply H;eauto.
                   --- intros;eauto. eapply HForall. eapply In_rcons. right. auto.
                   --- eapply In_rcons. left. auto.
                   --- eapply postfix_step_left;eauto. 
      + eapply H;eauto.
        * intros;eauto. eapply HForall. eapply In_rcons. right;auto.
        * eapply postfix_step_left;eauto.
  Qed.

  Lemma postfix_take (A : Type) (l l' : list A)
    : take ( |l'| ) l = l' <-> Postfix l' l.
  Proof.
    split; intro H.
    - rewrite <-H.
      remember (|l'|) as n. clear.
      revert l. induction n.
      + cbn. eapply postfix_nil.
      + intros l. destruct l.
        * cbn. econstructor;auto.
        * cbn. eapply postfix_cons;eauto.
    - revert dependent l. induction l';intros;cbn;auto.
      destruct l. 1: inversion H;congruence'.
      f_equal.
      + symmetry;eapply postfix_hd_eq;eauto.
      + eapply IHl'. eapply cons_postfix;eauto.
  Qed.      

  Lemma prefix_take_r (A : Type) (l l' : list A)
    : take_r ( |l'| ) l = l' <-> Prefix l' l.
  Proof.
    split; intro H.
    - eapply postfix_rev_prefix'.
      eapply postfix_take.
      eapply rev_rev_eq.
      rewrite rev_involutive.
      rewrite rev_length.
      unfold take_r in H.
      assumption.
    - eapply prefix_rev_postfix in H.
      eapply postfix_take in H.
      eapply rev_rev_eq in H.
      rewrite rev_involutive in H.
      rewrite rev_length in H.
      unfold take_r.
      assumption.
  Qed.
      
  Lemma geq_tag_suffix_tag_tl_eq (p q : Lab) l t i j
        (Hpath : TPath (root,start_tag) (q,j) t)
        (Hpost : Postfix l t)
        (HForall : Forall (DecPred (fun xl => |j| <= |snd xl|)) l)
        (Hel : (p,i) ∈ l)
    : take_r (| tl j |) i = tl j.
  Proof.
    rewrite Forall_forall in HForall. cbn in *.
    eapply prefix_take_r.
    revert dependent t. revert dependent p. revert i.
    rinduction l.
    - contradiction.
    - eapply In_rcons in Hel. destruct Hel.
      + subst a.
        specialize (rcons_destruct l0) as Hl0. destruct Hl0;[|destructH];subst l0.
        * cbn in *.
          inversion Hpath;subst;eapply postfix_hd_eq in Hpost;
            inversion Hpost;subst;cbn.
          -- econstructor;auto.
          -- clear. induction j;cbn;econstructor;auto. econstructor.
        * copy Hpost Hpost'.
          eapply postfix_path in Hpost;eauto.
          rewrite rcons_nl_rcons in Hpost.
          simpl_nl' Hpost.
          eapply path_nlrcons_edge in Hpost. simpl_nl' Hpost.
          destruct a.
          (* everything outside these brackets [ *)
          exploit' H.
          1: { intros;eauto. eapply HForall. eapply In_rcons. right;auto. }
          specialize (H t0 e).
          exploit H.
          1: { eapply In_rcons. left;auto. }
          1: { eapply postfix_step_left;eauto. }
          specialize (tcfg_edge_destruct Hpost) as Hdestr.
          assert (|j| <= |i|) as Hji.
          { specialize (HForall (p,i)). cbn in *. eapply HForall.
            eapply In_rcons;auto. }
          destruct Hdestr as [Hn|[He|[Hb|Hx]]]. all: subst;auto.
          -- assert (|j| < |0 :: i|) by (cbn;omega).
             inversion H.
             ++ exfalso. subst l0. rewrite <-H3 in H0. clear - H0.
                destruct j;cbn in *;omega. 
             ++ subst. auto.
          -- destruct i;cbn in Hb;[contradiction|]. subst t0.
             destruct j. 1: { cbn. eapply prefix_nil. }
             cbn in *.
             assert (|j| < |n :: i|) by (cbn;omega).
             inversion H.
             ++ exfalso. subst l0. subst j. cbn in Hji. omega.
             ++ subst. econstructor. auto. 
          -- eapply prefix_trans;eauto. clear; induction i;cbn;econstructor;eauto. econstructor.
          (* ] could be generalized, it is the same in this and the other geq_tag_suffix lemma *)
      + eapply H;eauto.
        * intros;eauto. eapply HForall. eapply In_rcons. right;auto.
        * eapply postfix_step_left;eauto.
  Qed.

  Lemma while'_front_In (A : Type) (e : A -> A -> bool) (P : decPred A) (l : ne_list A) (a b : A)
        (Hpath : Path e a b l)
        (HP : P b)
    : b ∈ while' P l.
  Proof.
    destruct Hpath;cbn.
    - decide (P a);try contradiction. left. auto.
    - decide (P c);try contradiction. left. auto.
  Qed.
  
  Lemma entry_through_header h p q
        (Hnin : ~ loop_contains h p)
        (Hin : loop_contains h q)
        (Hedge : p --> q)
    : q = h.
  Proof.
    specialize (a_reachability p) as Hreach. destructH.
    eapply path_front in Hreach as Hfront.
    eapply subgraph_path' in Hreach as Hreach'. 2: eapply a_edge_incl.
    eapply PathCons in Hreach';eauto.
    eapply dom_loop in Hreach' as Hdom;eauto.
    cbn in Hdom. decide (q = h);destruct Hdom;auto;try contradiction.
    exfalso.
    contradict Hnin.
    unfold loop_contains in *. destructH.
    eapply path_rcons in Hedge;eauto.
    exists p0. eexists. split_conj;eauto.
    simpl_nl. eapply nin_tl_iff in Hin3;eauto.
    destruct Hin3.
    - simpl_nl. rewrite rev_rcons. cbn. rewrite <-in_rev. auto.
    - eapply path_back in Hin2. rewrite Hin2 in H0. symmetry in H0. contradiction.
  Qed.
  
  Lemma deq_loop_le p i j q t t'
        (Hdeq : deq_loop p q)
        (Hpath : TPath (root,start_tag) (p,i) t)
        (Hpath' : TPath (root,start_tag) (q,j) t')
    : |j| <= |i|.
  Proof.
    eapply tag_depth in Hpath as Hdep'. 2: eapply path_contains_front;eauto.
    eapply tag_depth in Hpath' as Hdep. 2: eapply path_contains_front;eauto.
    rewrite Hdep, Hdep'.
    eapply deq_loop_depth;auto.
  Qed.

  Lemma tagle_monotone p q i j t
    (Hpath : TPath (root,start_tag) (p,i) t)
    (Hel : (q,j) ∈ t)
    (Hlen : |j| <= |i|)
    : j ⊴ i.
  Admitted.
  
  Lemma ex_entry (h p q : Lab) (i j : Tag) t
        (Hin : innermost_loop h q)
        (Hnin : ~ loop_contains h p)
        (Hpath : TPath (root,start_tag) (q,j) t)
        (Hord : (q,j) ≻* (p,i) | t)
    : (h,0 :: tl j) ≻* (p,i) | t.
  Proof.
    remember (while' (DecPred (fun xl => |j| <= |snd xl|)) t) as t'.
    assert (Postfix t' t) as Hpost.
    { eapply while'_postfix;subst t';eauto. }
    assert (forall xl, xl ∈ t' -> loop_contains h (fst xl)) as Hloop.
    { intros. destruct xl as [x l]. eapply geq_tag_suffix_deq in H.
      4: subst t'; eapply while'_Forall.
      all: cbn;eauto;destruct Hin as [Hin _];eauto.
    } 
    inversion Hpost.
    - subst. eapply splinter_cons in Hord. eapply splinter_in in Hord.
      specialize (Hloop (p,i)).
      exploit Hloop.
      + rewrite H0; auto.
      + cbn in Hloop. contradiction.
    - subst l.
      specialize (rcons_destruct t') as Ht'.
      destruct Ht'. (* t' is not empty *)
      { enough ((q,j) ∈ t') as H00 by (rewrite H0 in H00;cbn in H00;contradiction).
        subst.
        eapply while'_front_In;eauto. cbn. omega. }
      destructH.
      destruct a0 as [h' k].
      eapply postfix_ex_cons in H1. destructH. erewrite H in H1.
      assert (h' = h); [|subst h'].
      { (*
         * h' is a header
         * it has an incoming edge from outside of h
         *)
        destruct a'.
        eapply entry_through_header;cycle 1.
        - destruct Hin as [Hin1 Hin2].
          enough (deq_loop h' h).
          { eapply H2. eapply loop_contains_self. eapply loop_contains_loop_head;auto. }
          eapply deq_loop_trans; eauto.
          + eapply geq_tag_suffix_deq. 2:eapply Hpost. all: eauto.
            * rewrite Heqt'. eapply while'_Forall.
            * rewrite H0. eapply In_rcons. left. auto.
          + eapply loop_contains_deq_loop;auto.
        - rewrite H0 in H1. 
          eapply postfix_path in H1;eauto 1.
          instantiate (1:=e).
          rewrite rcons_nl_rcons in H1. simpl_nl' H1.
          eapply path_nlrcons_edge in H1. simpl_nl' H1.
          eapply tcfg_edge_spec in H1. destructH. eauto.
        - eapply while'_max in H1 as H1';eauto. cbn in H1'. contradict H1'.
          eapply loop_contains_deq_loop in H1'.
          eapply innermost_eq_loop in Hin.
          rewrite Hin in H1'.
          eapply postfix_incl in H1.
          eapply path_to_elem in Hpath as Hpath'. 
          2: { eapply H1. eapply In_rcons. left. reflexivity. }
          destructH.
          eapply deq_loop_le;cycle 1;eauto.
      }
      eapply while'_max in H1 as Hmax;[|eauto]. cbn in Hmax.
      destruct a'. cbn in *. assert (|l| < |j|) as Hmax' by omega.
      assert (|j| <= |k|) as Hjk.
      { assert ((h,k) ∈ t') by (rewrite H0;eapply In_rcons;eauto).
        rewrite Heqt' in H2.
        eapply while'_forall in H2. cbn in H2. auto. }
      assert (|l| < |k|) by omega.
      eapply tag_entry_lt in H2.
      + destruct j.
        { exfalso. cbn in Hmax'. omega. }
        assert (j = tl k).
        { replace j with (tl (n :: j)) by (cbn;auto). erewrite <-geq_tag_suffix_tag_tl_eq.
          - rewrite take_r_tl;eauto. cbn. rewrite H2. cbn. cbn in Hmax.
            rewrite H2 in Hjk. cbn in Hjk. omega.
          - eauto.
          - eapply Hpost. 
          - subst t'. eapply while'_Forall.
          - rewrite H0. eapply In_rcons. left. eauto.
        }
        rewrite H2 in H3. cbn in H3. cbn. subst j k.
        clear - Hpost Heqt' H0 H Hpath Hord Hin Hnin.
        eapply postfix_eq in Hpost. destructH.
        rewrite H,Hpost.
        rewrite consAppend. 
        eapply splinter_app; eapply splinter_single.
        * rewrite H0. eapply In_rcons. auto.
        * eapply splinter_cons in Hord. eapply splinter_in in Hord.
          rewrite Hpost in Hord. eapply in_app_or in Hord. destruct Hord;auto.
          exfalso.
          rewrite Heqt' in *.
          eapply geq_tag_suffix_deq in Hpath;cycle 1.
          -- eapply while'_postfix. symmetry. eauto.
          -- rewrite Heqt'. eapply while'_Forall.
          -- rewrite Heqt'. eapply H1.
          -- eapply Hnin. eapply Hpath. eapply Hin.
      + rewrite H0 in H1. eapply postfix_path in H1;eauto.
        rewrite rcons_nl_rcons in H1. simpl_nl' H1.
        eapply path_nlrcons_edge in H1. simpl_nl' H1. eauto.
    (*
     * define t' as the maximal suffix of t with tag dim >= |j|.
     * then forall x ∈ t', deq_loop x q thus x ∈ h
     * by definition t = t' or the maximal suffix starts with a loop enter
       * if t = t', contradiction bc. p ∈ t = t', and p ∈ h
       * else, ne_back t' = (h,0 :: tl j) and p ∉ t'
       *)
  Qed.

  Lemma ex_back_edge (p h q : Lab) (i j k : Tag) t
    (Hpath : TPath (root,start_tag) (p,k) t)
    (Hsucc : (h,0 :: i) ≻* (q,j) | t)
    (Hneq : (h,0 :: i) <> (q,j))
    (Hloop : loop_contains h q)
    : exists l, Prefix l j /\ match l with nil => False | n :: l => S n :: l ⊴ i end.
  Admitted.
  
  Lemma loop_tag_dom (h p : Lab) (i j : Tag) t
    (Hloop : loop_contains h p)
    (Hpath : TPath (root,start_tag) (p,i) t)
    (Htagle : j ⊴ i)
    (Hdep : |j| = depth h)
    : (h,j) ∈ t.
  Admitted.
  

  Lemma succ_NoDup_app (A : Type) (x y : A) (l l' : list A)
        (Hsucc : x ≻* y | l ++ l')
        (Hnd : NoDup (l ++ l'))
        (Hel : y ∈ l)
    : x ∈ l.
    clear - Hsucc Hnd Hel.
    revert dependent l.
    induction l';intros;cbn in *;try rewrite app_nil_r in *.
    - eapply splinter_in. eapply Hsucc.
    - destruct l;[contradiction|].
      admit.
  Admitted.
  
  Lemma lc_succ_rt2 (A : Type) `{EqDec A eq} (l1 l2 l1' l2' : list A) (a b c : A)
        (Hlc : last_common' l1 l2 l1' l2' a)
        (Hnd : NoDup l2)
        (Hsucc : b ≻* c | l2)
        (Hel : c ∈ l2')
    : b ∈ l2'.
  Proof.
    unfold last_common' in Hlc. destructH.
    eapply splinter_in in Hsucc as Hel'.
    eapply postfix_eq in Hlc2. destructH.
    rewrite <-app_cons_assoc in Hlc2.
    setoid_rewrite Hlc2 in Hsucc.
    eapply succ_NoDup_app in Hsucc;eauto. 
    setoid_rewrite <-Hlc2;eauto.
  Qed.

  Load vars.

  Lemma s_deq_q : deq_loop s q1.
  Proof.
    intros h Hh.
    eapply loop_contains_innermost in Hh as Hinner. destructH.
    eapply eq_loop_innermost in Hinner as Hinner'; eauto.
    eapply innermost_loop_deq_loop;eauto. 2:eapply Hloop in Hh;auto.
    eapply path_front in Hpath1 as Hfront1.
    eapply path_front in Hpath2 as Hfront2.
    destruct r1, r2.
    - contradiction.
    - eapply lc_nil1 in Hlc.
      rewrite hd_error_ne_front in Hlc. setoid_rewrite Hfront1 in Hlc. inversion Hlc. subst s k.
      unfold innermost_loop in Hinner. destructH; auto.
    - eapply last_common'_sym in Hlc. eapply lc_nil1 in Hlc.
      rewrite hd_error_ne_front in Hlc. setoid_rewrite Hfront2 in Hlc. inversion Hlc. subst s k.
      unfold innermost_loop in Hinner'. destructH; auto.
    - decide (loop_contains h' s);[auto|exfalso].
      assert (p = (q1,j1)); [|subst p].
      { eapply lc_cons1 in Hlc;rewrite hd_error_ne_front in Hlc;setoid_rewrite Hfront1 in Hlc. inversion Hlc;auto. }
      assert (p0 = (q2,j2)); [|subst p0].
      { eapply last_common'_sym in Hlc.
        eapply lc_cons1 in Hlc;rewrite hd_error_ne_front in Hlc;setoid_rewrite Hfront2 in Hlc. inversion Hlc;auto. }
      copy Hinner Hinner''.
      eapply ex_entry in Hinner;eauto.
      eapply ex_entry in Hinner';eauto.
      2: eapply last_common'_sym in Hlc.
      2,3: eapply lc_succ_rt1;eauto.
      rewrite Htag in Hinner.
      eapply lc_succ_rt_eq_lc in Hlc;eauto.
      2,3: eapply tpath_NoDup;eauto.
      eapply n. inversion Hlc. eapply loop_contains_self. unfold innermost_loop in Hinner''. destructH.
      eapply loop_contains_loop_head;eauto.
  Qed. 
    
  Lemma dep_eq_impl_head_eq (* unused *): depth s = depth q1 -> eq_loop s q1.
  Proof.
    intros Hdep.
    split;[eapply s_deq_q|].
    admit.
  Admitted.
  
End disj.
