Require Export DiamondPaths.
Require Import Lia.

Lemma spath_jj_subtag `(SplitPaths)
      (Hjle : j1 ⊴ j2)
  : sub_tag j1 j2.
Proof.
  split;[|split].
  - eapply Tagle_len;eauto.
  - destruct Hjle;[|subst;eauto].
    destruct H0;cbn;try lia.
    exfalso.
    specialize Stl as Htl. cbn in Htl. subst. eapply Taglt_irrefl;eauto.
  - eapply Stl.
Qed.

Lemma jj_subtag `(DiamondPaths)
      (Hjle : j1 ⊴ j2)
  : sub_tag j1 j2.
Proof.
  eapply diamond_split in H. eapply spath_jj_subtag;eauto.
Qed.

Hint Resolve jj_subtag : diamond.

Hint Resolve Spath1 Spath2 Sdisj Sloop Stl Slen : spath.

Section spath.
  Context `(S : SplitPaths).

  Lemma spath_j_len1
    : | j1 | = depth q1.
  Proof.
    eapply tag_depth_unroot;eauto with spath. eapply Spath1.
  Qed.

  Lemma spath_j_len2
    : | j2 | = depth q2.
  Proof.
    eapply tag_depth_unroot;eauto with spath. eapply Spath2.
  Qed.

  Lemma spath_jj_len
    : |j1| = |j2|.
  Proof.
    erewrite spath_j_len1.
    erewrite spath_j_len2.
    rewrite Sloop. reflexivity.
  Qed.

  Lemma spath_s_deq_q
    : deq_loop s q1.
  Proof.
    intros h Hh.
    eapply loop_contains_innermost in Hh as Hinner. destructH.
    eapply eq_loop_innermost in Hinner as Hinner'. 2: eapply Sloop.
    eapply innermost_loop_deq_loop;eauto. 2:eapply Sloop in Hh;auto.
    decide (loop_contains h' s);[assumption|exfalso].
    copy Hinner Hinner''.
    eapply ex_entry_innermost in Hinner;eauto with spath. 2: eapply Spath1.
    eapply ex_entry_innermost in Hinner';eauto with spath. 2: eapply Spath2.
    rewrite Stl in Hinner.
    eapply In_rcons in Hinner. eapply In_rcons in Hinner'.
    destruct Hinner, Hinner'.
    1-3: lazymatch goal with
         | H: (?h', _ ) = (s,k) |- _ => inv H
         end;
      eapply n;destruct Hinner'';eauto using loop_contains_self.
    eapply Sdisj;eauto.
  Qed.

  Lemma spath_no_head_inst (h : Lab) (l : Tag)
        (Hjle : j1 ⊴ j2)
        (Hcont : innermost_loop h q1)
        (Hel : (h,l) ∈ r1)
    : False.
  Proof.
    specialize (tcfg_reachability Slen) as Hreach.
    specialize Spath1 as Dpath1'.
    destructH.
    specialize Spath1 as Hpath1.
    eapply path_app' in Hpath1. 2: eapply Hreach.
    cbn in Hpath1.
    assert (|j1| = depth h) as Hheq.
    { eapply innermost_eq_loop in Hcont;rewrite Hcont. eapply spath_j_len1;eauto. }
    assert (|j2| = depth h) as Hheq2.
    { rewrite <-spath_jj_len. assumption. }
    eapply loop_tag_dom_eq in Hpath1 as Hin;eauto. 2: destruct Hcont;eauto.
    2: rewrite take_r_geq;rewrite Hheq;eauto.
    rewrite <-app_assoc in Hin.
    eapply in_app_or in Hin.
    rewrite take_r_geq in Hin.
    2: { eapply innermost_eq_loop in Hcont. rewrite Hcont. erewrite <-spath_j_len1;eauto. }
    rewrite <-app_assoc in Hpath1.
    assert ([(s,k)] ++ tl t = t) as Hsktlt.
    { destruct t;[inv Hreach|]. cbn. unfold TPath in Hreach. path_simpl' Hreach. reflexivity. }
    replace ([(s,k)] ++ tl t) with t in Hpath1, Hin by eauto.
    assert ((h,j1) ∉ t) as Hnin.
    - intro N.
      eapply path_from_elem in N;eauto. destructH.
      specialize Spath1 as Spath1'.
      destruct r1;[contradiction|]. cbn in Spath1'. unfold TPath in Spath1'. path_simpl' Spath1'.
      eapply path_rcons_inv' in Spath1' as Sedge.
      destructH.
      eapply path_from_elem in Hel as Helfrom;eauto.
      destructH.
      copy Hel Hel'.
      eapply path_to_elem in Hel;eauto.
      destructH.
      assert (|l| = depth h) as Hhdep.
      { eapply path_to_elem in Dpath1'. 2: rewrite In_rcons;right;eauto. destructH.
        eapply tag_depth_unroot in Dpath1'0;eauto with spath. }
      copy Hel0 Hϕ1.
      eapply path_app in Hel0. 3:eauto. 2: eapply N0.
      copy Hel0 Hel0'.
      eapply tagle_monotone in Hel0;eauto.
      2,3: reflexivity.
      do 2 rewrite take_r_geq in Hel0. all: try rewrite Hheq;eauto.
      2: rewrite <-Hhdep;eauto.
      eapply tagle_monotone in Helfrom0;eauto.
      2: reflexivity.
      2: eapply loop_contains_deq_loop;destruct Hcont;eauto.
      do 2 rewrite take_r_geq in Helfrom0;eauto. all: try rewrite Hheq;try rewrite Hhdep;eauto.
      assert (j1 = l) as Heq.
      + eapply partial_order_antisym;eauto.
      + eapply tcfg_fresh in Hel0';eauto.
        * subst l. eapply Taglt_irrefl;eauto.
        * inv_path N0; inv_path Hϕ1;cbn;try rewrite app_length;cbn;lia.
    - destruct Hin as [Hin|Hin]. 2: eapply Hnin;eauto.
      enough (Hin2 : (h, j1) ∈ r2).
      { eapply Sdisj;eauto. }
      specialize Spath2 as Hpath2.
      eapply path_app' in Hpath2. 2: eapply Hreach.
      rewrite <-app_assoc in Hpath2.
      rewrite Hsktlt in Hpath2.
      enough ((h,j1) ∈ (r2 ++ t)).
      { eapply in_app_or in H. destruct H as [H1|Hin2];[eauto|exfalso;eapply Hnin;eauto]. }
      cbn in Hpath2.
      eapply loop_tag_dom;eauto.
      + rewrite <-Sloop. destruct Hcont;eassumption.
      + rewrite take_r_geq;[|rewrite <-Hheq2;eauto].
        eapply spath_jj_subtag;eauto.
  Qed.

End spath.

Lemma spath_r1_incl_head_q' `(S : SplitPaths)
      (Hjle : j1 ⊴ j2)
  : forall x, x ∈ map fst r1 -> deq_loop x q1.
  intros x Hel h Hh.
  eapply loop_contains_innermost in Hh as Hinner1. destructH.
  eapply eq_loop_innermost in Hinner1 as Hinner2. 2: eapply Sloop.
  eapply innermost_loop_deq_loop;eauto. 2: rewrite <-Sloop;eauto.
  decide (loop_contains h' x);[auto|exfalso].
  eapply in_fst in Hel as Hfst.
  destruct Hfst as [b Hfst].
  destruct r1;[contradiction|].
  specialize Spath1 as Spath1'. cbn in Spath1'. unfold TPath in Spath1'. path_simpl' Spath1'.
  eapply path_rcons_inv in Spath1'. destructH.
  eapply path_from_elem in Hfst. destructH. 2:eauto. 2: eapply Spath1'.
  eapply ex_entry_innermost in Hfst0 as Hentry;eauto.
  2: { eapply tag_depth_unroot2;eauto with spath. eapply spath_j_len1;eauto. }
  eapply postfix_incl in Hfst1. eapply Hfst1 in Hentry. exfalso.
  eapply spath_no_head_inst in Hentry as Hentry2;eauto.
Qed.

Lemma spath_r2_incl_head_q' `(S : SplitPaths)
      (Hjle : j1 ⊴ j2)
  : forall x, x ∈ map fst r2 -> deq_loop x q1.
Proof.
  intros x Hel h Hh.
  eapply loop_contains_innermost in Hh as Hinner. destructH.
  eapply eq_loop_innermost in Hinner as Hinner'; [|eapply Sloop];eauto.
  eapply innermost_loop_deq_loop;eauto. 2:eapply Sloop in Hh;auto.
  cbn. decide (loop_contains h' x);[auto|exfalso].
  eapply in_fst in Hel. destructH.
  destruct r2;[contradiction|].
  specialize Spath2 as Dpath2'. cbn in Dpath2'. unfold TPath in Dpath2'.
  path_simpl' Dpath2'. eapply path_rcons_inv' in Dpath2'. destructH.
  eapply path_from_elem in Hel as Hϕ;eauto.
  destructH.
  assert (|b| = depth x) as Hbx.
  { eapply tag_depth_unroot2;eauto with spath. eapply spath_j_len2;eauto. }
  eapply ex_entry_innermost in Hinner';eauto.
  erewrite <-Stl in Hinner';eauto.
  specialize (tcfg_reachability Slen) as Hproot. destructH.
  specialize Spath1 as Hπ.
  eapply path_app' in Hπ. 2: eapply Hproot.
  assert ([(s,k)] ++ tl t = t) as Hsktlt.
  { destruct t;[inv Hproot|]. cbn. unfold TPath in Hproot. path_simpl' Hproot. reflexivity. }
  rewrite <-app_assoc in Hπ.
  rewrite Hsktlt in Hπ.
  assert ((h', 0 :: tl j1) ∉ t) as Hnin.
  - intro N.
    eapply path_from_elem in N;eauto. destructH.
    eapply postfix_incl in Hinner';eauto.
    eapply path_to_elem in Hinner';eauto. destructH.
    eapply path_app in Hinner'0 as Hel0'. 3: eauto. 2:eapply N0.
    eapply tcfg_fresh in Hel0'.
    + eapply Taglt_irrefl;eauto.
    + eapply innermost_eq_loop in Hinner. rewrite Hinner. setoid_rewrite <-spath_j_len1. 2:eauto.
      destruct j1;cbn;eauto.
      exfalso. eapply loop_contains_depth_lt in Hh. setoid_rewrite <-spath_j_len1 in Hh;eauto.
      cbn in Hh. lia.
    + destruct ϕ1,ϕ0;try rewrite app_length;cbn;try lia;inv Hinner'0;inv N0.
  - specialize Spath1 as Spath1'. destruct r1.
    + cbn in Spath1'. eapply path_single in Spath1'. destructH. inv Spath1'0. inv Spath1'1.
      eapply ex_entry_innermost in Hproot;cbn;eauto.
      * rewrite depth_root. eauto.
      * eapply root_no_loop.
    + cbn in Spath1'. unfold TPath in Spath1'. path_simpl' Spath1'. inv_path Spath1'. congruence'.
      eapply ex_entry_innermost in Hπ;cbn;eauto.
      * eapply in_app_or in Hπ. destruct Hπ;[|contradiction].
        eapply Sdisj;eauto. eapply postfix_incl;eauto.
      * rewrite depth_root. eauto.
      * eapply root_no_loop.
Qed.

Lemma spath_no_back `(S : SplitPaths)
      (Hjle : j1 ⊴ j2)
  : forall x : Lab, x ∈ (map fst r1) -> ~ loop_contains x q1.
Proof. (* Hjle needed *)
  intros h' Hel Hnin.
  eapply in_fst in Hel.
  destructH.
  decide (innermost_loop h' q1).
  - eapply spath_no_head_inst in Hel as Hel';eauto.
  - simpl_dec' n.
    destruct n;[contradiction|]. eapply H.
    eapply spath_r1_incl_head_q';eauto. eapply in_map with (f:=fst) in Hel. cbn in Hel. assumption.
Qed.

Lemma SplitPaths_sym `(S : SplitPaths)
  : SplitPaths s q2 q1 k j2 j1 r2 r1.
Proof.
  econstructor.
  3: eapply Disjoint_sym.
  4,5: symmetry.
  all: eauto with spath.
Qed.

Lemma spath_r1_incl_head_q `(S : SplitPaths)
  : forall x, x ∈ map fst r1 -> deq_loop x q1.
Proof.
  specialize (spath_jj_len S) as Hlen.
  eapply tagle_or in Hlen.
  destruct Hlen.
  - eapply spath_r1_incl_head_q';eauto.
  - setoid_rewrite Sloop.
    eapply spath_r2_incl_head_q';eauto.
    eapply SplitPaths_sym;eauto.
Qed.

Lemma spath_r2_incl_head_q `(S : SplitPaths)
  : forall x, x ∈ map fst r2 -> deq_loop x q1.
Proof.
  setoid_rewrite Sloop.
  eapply spath_r1_incl_head_q.
  eapply SplitPaths_sym;eauto.
Qed.

Lemma spath_tag_eq1 `(S : SplitPaths)
      (Hjle : j1 ⊴ j2)
  : forall j, j ∈ map snd r1 -> take_r (depth q1) j = j1.
Proof.
  intros. destruct r1;[contradiction|].
  specialize Spath1 as Hpath1.
  unfold TPath in Hpath1. cbn in Hpath1. path_simpl' Hpath1.
  eapply in_snd in H. destructH.
  eapply path_rcons_inv' in Hpath1 as Hpath1'. destructH. destruct p0 as [u1 l1].
  eapply path_to_elem in H as Hϕ;eauto. destructH.
  eapply tpath_deq_no_haed_tag_eq in Hϕ0.
  - eapply tpath_deq_no_haed_tag_eq in Hpath1'0;eauto with spath.
    + erewrite <-take_r_geq.
      * rewrite Hpath1'0. eapply Hϕ0.
      * erewrite spath_j_len1;eauto.
    + eapply tcfg_edge_depth_iff in Hpath1'1. eapply Hpath1'1;eauto with spath.
    + intros. eapply spath_r1_incl_head_q;eauto.
    + intros. eapply spath_no_back;eauto.
  - eapply tcfg_edge_depth_iff in Hpath1'1. eapply Hpath1'1;eauto with spath.
  - intros. eapply spath_r1_incl_head_q;eauto. eapply prefix_incl;eauto.
    eapply prefix_map_fst;eauto.
  - intros. eapply spath_no_back;eauto. eapply prefix_incl;eauto. eapply prefix_map_fst;eauto.
Qed.

Lemma spath_tag_eq2 `(S : SplitPaths)
  : forall j, j ∈ map snd r2 -> take_r (depth q1 - 1) j = tl j1.
Proof.
  intros.
  specialize Spath2 as Hpath2.
  copy Hpath2 Hpath3.
  eapply in_snd in H as Hin. destructH.
  eapply path_to_elem in Hpath2. 2: eapply In_rcons;right;eauto. destructH.
  eapply tag_depth_unroot in Hpath0 as Hdep;eauto with spath.
  destruct r2. 1: contradiction. unfold TPath in Hpath3. destruct p.
  cbn in Hpath3. path_simpl' Hpath3. eapply path_rcons_inv in Hpath3. destructH.
  eapply path_from_elem in Hpath3. 2: eauto. 2: eauto.
  destructH.
  erewrite tpath_tag_take_r_eq with (i:=j2).
  - rewrite Stl. rewrite Sloop. erewrite <-spath_j_len2;eauto.
    symmetry. eapply take_r_tl_eq.
  - eauto.
  - eauto.
  - intros. eapply spath_r2_incl_head_q;eauto. eapply postfix_map with (f:=fst) in Hpath4.
    eapply postfix_incl;eauto.
  - reflexivity.
Qed.

Lemma SplitPaths_Prefix `(S : SplitPaths) q2' j2' r2'
      (Hpre : Prefix ((q2',j2') :: r2') r2)
      (Heq : eq_loop q1 q2')
  : SplitPaths s q1 q2' k j1 j2' r1 ((q2',j2') :: r2').
Proof.
  copy S S'.
  destruct S.
  assert (TPath (s, k) (q2', j2') (((q2', j2') :: r2') :r: (s, k))) as Hpath2.
  { cbn. eapply path_prefix_path;eauto. rewrite app_comm_cons. eapply prefix_rcons;eauto. }
  econstructor;eauto.
  - eapply disjoint_subset. 1:reflexivity. 1: eapply prefix_incl;eauto. eauto.
  - erewrite <-spath_tag_eq2;eauto;cycle 1.
    + eapply prefix_incl in Hpre. eapply incl_map with (f:=snd) in Hpre. cbn in Hpre.
      eapply Hpre. left. auto.
    + destruct j2';[|].
      * eapply tag_depth_unroot in Hpath2;eauto. cbn in Hpath2. cbn.
        rewrite take_r_geq;cbn;eauto. lia.
      * cbn. rewrite take_r_cons_drop.
        -- rewrite take_r_geq;eauto. eapply tag_depth_unroot in Hpath2. rewrite Heq. rewrite <-Hpath2.
           cbn. lia. eauto.
        -- eapply tag_depth_unroot in Hpath2;eauto. rewrite Heq. rewrite <-Hpath2. cbn. lia.
Qed.
