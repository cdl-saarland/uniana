Require Export DisjDef MaxPreSuffix.

Section disj.

  Load X_notations.
  
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
  
  Lemma ex_entry_elem (h p q q' : Lab) (i j j' : Tag) t
        (Hin : innermost_loop h q)
        (Hnin : ~ loop_contains h p)
        (Hpath : TPath (root,start_tag) (q',j') t)
        (Hord : (q,j) ≻* (p,i) | t)
    : (h,0 :: tl j) ≻* (p,i) | t.
  Proof.
    copy Hpath Hpath'.
    eapply path_to_elem in Hpath.
    2: { eapply splinter_in. eauto. }
    destructH.
    eapply prefix_eq in Hpath1 as Heq. destructH.
    eapply splinter_prefix;eauto.
    eapply ex_entry;eauto.
    rewrite Heq in Hord.
    clear - Hord Hpath0 Heq Hpath'.
    eapply tpath_NoDup in Hpath'. rewrite Heq in Hpath'. clear Heq.
    induction l2';intros.
    - cbn in Hord. eauto.
    - inversion Hord;subst.
      + exfalso.
        eapply NoDup_app in Hpath';[|left;eauto].
        eapply Hpath'.
        eapply path_contains_front;eauto.
      + eapply IHl2';eauto. inversion Hpath'. subst. eauto.
  Qed.    

  (* misc *)

  Global Instance Path_dec (L : eqType) (e : L -> L -> bool) (x y : L) (π : ne_list L)
    : dec (Path e x y π).
  revert y.
  induction π;intro y;eauto.
  - decide (a = x);decide (a = y);subst. 1: left;econstructor.
    all: right;contradict n;inversion n;reflexivity.
  - destruct (IHπ (ne_front π)).
    1: decide (a = y).
    1: subst; destruct (e (ne_front π) y) eqn:E.
    1: left;econstructor;eauto 1.
    all: right;intro N;inversion N;clear N.
    all: match goal with [ Q : Path _ _ _ _ |- _] => eapply path_front in Q as Hfront end.
    all: cbn in Hfront;subst;try contradiction. congruence.
  Qed.

  Lemma ex_back_edge (p h q : Lab) (i j k : Tag) t
    (Hpath : TPath (root,start_tag) (p,k) t)
    (Hsucc : splinter_strict [(h,0 :: i); (q,j)] t)
    (Hloop : loop_contains h q)
    : exists l, Prefix l j /\ match l with nil => False | n :: l => S n :: l ⊴ i end.
  Proof.
    (*
     * assume there are no *outer* back_edges. <- this could be formulated using APath & loopimplosion
     * then proof by induction on the the path t' from (q,j) to the predecessor of (h,0::i),
     * that (take_r |tl j| k) ⊴ (tl j) holds forall (p,k) ∈ t'.
     * by monotonicity and antisymmetry we have tl j = k forall (p,k) ∈ t', where |k|=|tl j|
     * thus i = tl j.
     * then find entry for q using ex_entry. this gives us another (h,0::i) ∈ t, 
     * contradiction to tpath_NoDup.
     *) 
  Admitted.
  
  Load X_vars.

  Lemma s_deq_q : deq_loop s q1.
  Proof.
    intros h Hh.
    eapply loop_contains_innermost in Hh as Hinner. destructH.
    eapply eq_loop_innermost in Hinner as Hinner'; eauto.
    eapply innermost_loop_deq_loop;eauto. 2:eapply Hloop in Hh;auto.
    eapply path_front in Hpath1 as Hfront1.
    eapply path_front in Hpath2 as Hfront2.
    destruct r1, r2.
    - eapply lc_nil1 in Hlc. rewrite hd_error_ne_front in Hlc. inversion Hlc.
      setoid_rewrite Hfront1 in H0. inversion H0. subst. destruct Hinner. eauto. 
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
    eapply deq_loop_depth_eq;eauto using s_deq_q.
  Qed.
  
End disj.
