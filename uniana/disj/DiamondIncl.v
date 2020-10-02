Require Export DiamondPaths.
Require Import Lia.

Definition sub_tag i j := |i| = |j| /\ hd 0 i <= hd 0 j /\ tl i = tl j.

Lemma Tagle_len: forall [i j : Tag], i ⊴ j -> | i | = | j |.
Proof.
  intros. destruct H.
  - eapply Taglt_len;eauto.
  - subst. reflexivity.
Qed.

Lemma jj_subtag `(DiamondPaths)
      (Hjle : j1 ⊴ j2)
  : sub_tag j1 j2.
Proof.
  split;[|split].
  - eapply Tagle_len;eauto.
  - destruct Hjle;[|subst;eauto].
    destruct H0;cbn;try lia.
    exfalso.
    eapply tl_eq in H. cbn in H. subst. eapply Taglt_irrefl;eauto.
  - eapply tl_eq;eauto.
Qed.

Hint Resolve jj_subtag : diamond.

Lemma loop_tag_dom_eq `(C : redCFG) (h p : Lab) (i j : Tag) t
      (Hloop : loop_contains h p)
      (Hpath : TPath (root,start_tag) (p,i) t)
      (Htagle : j = take_r (depth h) i)
      (Hdep : |j| = depth h)
  : (h,j) ∈ t.
Proof.
  subst j.
  clear Hdep.
  revert h p i Hloop Hpath.
  induction t;intros.
  + inv Hpath.
  + unfold TPath in Hpath. path_simpl' Hpath. destruct t.
    {
      eapply path_single in Hpath. destruct Hpath.
      inversion H. subst p i. eapply root_no_loop in Hloop. contradiction.
    }
    inv_path Hpath. destruct c as [q j].
    specialize (IHt) with (p:=q) (i:=j).
    eapply tcfg_edge_destruct' in H0.
    destruct H0 as [H0|[H0|[H0|H0]]].
    all: destruct H0 as [Htag Hedge].
    * subst. right.
      eapply IHt. all:cycle 1.
      -- eapply H.
      -- eapply basic_edge_eq_loop in Hedge. rewrite Hedge. assumption.
    * eapply deq_loop_entry_or in Hedge;eauto.
      destruct Hedge.
      -- subst. right.
         rewrite take_r_cons_drop.
         2: {
           eapply loop_contains_deq_loop in H0.
           eapply tag_depth' in H. rewrite H.
           eapply deq_loop_depth;eauto.
         }
         eapply IHt;eauto.
      -- subst p. left. rewrite take_r_geq;eauto.
         eapply tag_depth' in Hpath. lia.
    * destruct j.
      {
        eapply tag_depth' in H. cbn in H. eapply loop_contains_depth_lt in Hloop.
        eapply back_edge_eq_loop in Hedge. rewrite Hedge in H. lia.
      }
      cbn in Htag. subst i.
      decide (h = p).
      -- subst p. left. rewrite take_r_geq;eauto.
         eapply tag_depth' in Hpath. lia.
      -- right. rewrite take_r_cons_replace with (b:=n).
         2: {
           copy Hedge Hedge'.
           eapply back_edge_eq_loop in Hedge.
           copy Hloop Hloop'.
           eapply loop_contains_deq_loop in Hloop.
           eapply eq_loop1 in Hloop;eauto. 2: symmetry;eauto.
           eapply tag_depth' in H.
           enough (depth h < S (| j |)).
           { cbn in H. rewrite H in H0. lia. }
           eapply deq_loop_depth in Hloop.
           eapply le_lt_or_eq in Hloop.
           destruct Hloop.
           ++ cbn in H. lia.
           ++ exfalso. rewrite Hedge in H0.
              eapply loop_contains_deq_loop in Hloop' as Hdeq.
              eapply deq_loop_depth_eq in H0;eauto.
              eapply n0. eapply head_unique;eauto.
              ** eapply loop_contains_ledge;eauto.
              ** split;eauto.
         }
         eapply IHt;eauto.
         eapply back_edge_eq_loop in Hedge. rewrite Hedge. eauto.
    * subst.
      destruct j.
      {
        eapply tag_depth' in H. cbn in H. eapply loop_contains_depth_lt in Hloop.
        destruct Hedge. eapply deq_loop_exited in H0. eapply deq_loop_depth in H0. lia.
      }
      right. rewrite <-take_r_cons_drop with (a:=n).
      all: cbn.
      2: {
        eapply tag_depth' in H. cbn in H.
        enough (depth h < S (|j|)) by lia.
        rewrite H.
        eapply depth_exit in Hedge.
        eapply loop_contains_deq_loop in Hloop. eapply deq_loop_depth in Hloop.
        lia.
      }
      eapply IHt;eauto.
      destruct Hedge. eapply deq_loop_exited in H0. eapply H0. eauto.
Qed.

Lemma loop_tag_dom_same `(C : redCFG) (h : Lab) (i j : Tag) t
      (Hloop : loop_head h)
      (Hpath : TPath (root,start_tag) (h,i) t)
      (Htagle : sub_tag j i)
  : (h,j) ∈ t.
Proof.
  destruct Htagle as [Hlen [Hhd Htl]].
  destruct i,j;cbn in *;[|congruence|congruence|].
  { eapply tag_depth' in Hpath. cbn in Hpath. eapply depth_loop_head in Hloop. lia. }
  subst j. clear Hlen.
  revert t Hpath.
  induction Hhd;intros.
  - eapply path_contains_front;eauto.
  - destruct t;[inv Hpath|].
    unfold TPath in Hpath. path_simpl' Hpath.
    inversion Hpath. subst.
    destruct b as [q j].
    eapply tcfg_edge_destruct' in H3.
      destruct H3 as [H3|[H3|[H3|H3]]].
      all: destruct H3 as [Htag Hedge].
      * eapply basic_edge_no_loop2 in Hedge. contradiction.
      * inv Htag.
      * destruct j;cbn in Htag;[congruence|].
        inv Htag.
        right.
        eapply loop_tag_dom_eq in H0 as Hel2;cycle 1.
        -- eapply loop_contains_ledge;eassumption.
        -- rewrite take_r_geq;eauto. eapply tag_depth' in H0. rewrite H0.
           eapply back_edge_eq_loop in Hedge. rewrite Hedge. eauto.
        -- eapply back_edge_eq_loop in Hedge. rewrite <-Hedge. eapply tag_depth' in H0. eauto.
        -- eapply path_to_elem in Hel2;eauto. destructH.
           eapply prefix_incl;[eauto|].
           eapply IHHhd;eassumption.
      * destruct j;cbn in Htag;[congruence|]. subst j. destruct Hedge.
        eapply no_exit_head in H. contradiction.
Qed.

(* could be generalized with sub_tag _ _  -> sub_tag _ _ \/ Prefix _ _ *)
Lemma loop_tag_dom `(C : redCFG) (h p : Lab) (i j : Tag) t
      (Hloop : loop_contains h p)
      (Hpath : TPath (root,start_tag) (p,i) t)
      (Hstag : sub_tag j (take_r (depth h) i))
      (Hdep : |j| = depth h)
  : (h,j) ∈ t.
Proof.
  assert (depth h <= | i |) as Hdepi.
  {
    eapply tag_depth' in Hpath. rewrite Hpath.
    eapply deq_loop_depth.
    eapply loop_contains_deq_loop;eauto.
  }
  eapply loop_tag_dom_eq in Hpath as Hel2.
  3: reflexivity.
  2: eauto.
  2: rewrite take_r_length_le;eauto.
  eapply path_to_elem in Hel2;eauto.
  destructH.
  eapply prefix_incl;eauto.
  eapply loop_tag_dom_same;eauto.
  eapply loop_contains_loop_head;eauto.
Qed.

Section disj.

  Infix "-->" := edge__P.


  Context `(D : DiamondPaths).
  Hypothesis (Hjle : j1 ⊴ j2).

  Lemma s_deq_q
    : deq_loop s q1.
  Proof.
    clear Hjle.
    intros h Hh.
    eapply loop_contains_innermost in Hh as Hinner. destructH.
    eapply eq_loop_innermost in Hinner as Hinner'. 2: eapply Dloop.
    eapply innermost_loop_deq_loop;eauto. 2:eapply Dloop in Hh;auto.
    destruct r1, r2; inv_Dpaths D.
    1-3: lazymatch goal with
         | H : innermost_loop ?h' s |- _ => destruct H;eauto
         end.
    decide (loop_contains h' s);[assumption|exfalso].
    copy Hinner Hinner''.
    eapply Dpath_sq1 in D as Hsq1.
    eapply Dpath_sq2 in D as Hsq2.
    eapply ex_entry_innermost in Hinner;eauto.
    2: eapply Dlen.
    eapply ex_entry_innermost in Hinner';eauto.
    2: eapply Dlen.
    eapply tl_eq in D as Htl.
    rewrite Htl in Hinner.
    eapply In_rcons in Hinner.
    eapply In_rcons in Hinner'.
    destruct Hinner, Hinner'.
    1-3: lazymatch goal with
         | H: (?h', _ ) = (s,k) |- _ => inv H
         end;
      eapply n;destruct Hinner'';eauto using loop_contains_self.
    eapply Ddisj;eauto.
  Qed.

  Lemma no_head_inst (h : Lab) (l : Tag)
        (Hcont : innermost_loop h q1)
        (Hel : (h,l) ∈ r1)
    : False.
  Proof.
    specialize (tcfg_reachability Dlen) as Hreach.
    specialize Dpath1 as Dpath1'.
    destructH.
    specialize Dpath1 as Hpath1.
    eapply path_app in Hpath1. 2: eapply Hreach. 2: eapply Dsk1.
    cbn in Hpath1.
    destruct r1;[contradiction|].
    inv_Dpaths D.
    inv_path Hpath1.
    assert (|j1| = depth h) as Hheq.
    { eapply innermost_eq_loop in Hcont;rewrite Hcont. eapply j_len1;eauto. }
    assert (|j2| = depth h) as Hheq2.
    { eapply jj_len in D. rewrite <-D. assumption. }
    eapply loop_tag_dom_eq in H as Hin;eauto. 2: destruct Hcont;eauto.
    2: rewrite take_r_geq;rewrite Hheq;eauto.
    rewrite app_comm_cons in Hin.
    eapply in_app_or in Hin.
    rewrite take_r_geq in Hin.
    2: { eapply innermost_eq_loop in Hcont. rewrite Hcont. erewrite <-j_len1;eauto. }
    assert ((h,j1) ∉ t) as Hnin.
    - intro N.
      eapply path_from_elem in N;eauto. destructH.
      inv_path Dpath1'.
      eapply path_from_elem in Hel as Helfrom;eauto. destructH.
      eapply path_to_elem in Hel;eauto.
      destructH.
      eapply tag_depth_unroot in Hel0 as Hhdep;eauto with diamond.
      copy Hel0 Hϕ1.
      eapply path_app in Hel0. 3: eapply Dsk1. 2: eapply N0.
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
      { eapply Ddisj;eauto. }
      specialize Dpath2 as Hpath2.
      eapply path_app in Hpath2. 2: eapply Hreach. 2: eapply Dsk2.
      enough ((h,j1) ∈ (r2 ++ t)).
      { eapply in_app_or in H1. destruct H1 as [H1|Hin2];[eauto|exfalso;eapply Hnin;eauto]. }
      cbn in Hpath2.
      inversion Hpath2.
      { subst p2 i. subst a. symmetry in H5. eapply app_eq_nil in H5. destructH. subst t. inv Hreach. }
      subst.
      assert (b = (q2,j2)).
      { destruct b as [q j]. destruct r2.
        - setoid_rewrite <-Dqj2. cbn. cbn in H2. inv_path Hreach;inv H2;eauto.
        - setoid_rewrite <-Dqj2. cbn. cbn in H2; inv_path H2;eauto.
      }
      subst b.
      eapply loop_tag_dom;eauto.
      + rewrite <-Dloop. destruct Hcont;eassumption.
      + rewrite take_r_geq;[|rewrite <-Hheq2;eauto].
        eauto with diamond.
  Qed.

  Lemma r1_incl_head_q' : forall x, x ∈ map fst r1 -> deq_loop x q1.
    intros x Hel h Hh.
    eapply loop_contains_innermost in Hh as Hinner1. destructH.
    eapply eq_loop_innermost in Hinner1 as Hinner2. 2: eapply Dloop.
    eapply innermost_loop_deq_loop;eauto. 2: rewrite <-Dloop;eauto.
    decide (loop_contains h' x);[auto|exfalso].
    eapply in_fst in Hel as Hfst.
    destruct Hfst as [b Hfst].
    eapply path_from_elem in Hfst. destructH. 2:eauto. 2: eapply Dpath_uq1;eauto.
    2: intro N;rewrite N in Hel; cbn in Hel;contradiction.
    eapply ex_entry_innermost in Hfst0 as Hentry;eauto.
    2: { eapply tag_depth_unroot2;eauto with diamond. eapply j_len1;eauto. }
    eapply postfix_incl in Hfst1. eapply Hfst1 in Hentry. exfalso.
    eapply no_head_inst in Hentry as Hentry2;eauto.
  Qed.

  Lemma r2_incl_head_q' : forall x, x ∈ map fst r2 -> deq_loop x q1.
  Proof.
    intros x Hel h Hh.
    eapply loop_contains_innermost in Hh as Hinner. destructH.
    eapply eq_loop_innermost in Hinner as Hinner'; [|eapply Dloop];eauto.
    eapply innermost_loop_deq_loop;eauto. 2:eapply Dloop in Hh;auto.
    cbn. decide (loop_contains h' x);[auto|exfalso].
    eapply in_fst in Hel. destructH.
    destruct r2;[contradiction|].
    inv_Dpaths D.
    specialize Dpath2 as Dpath2'; inv_path Dpath2'.
    eapply path_from_elem in Hel as Hϕ;eauto.
    destructH.
    assert (|b| = depth x) as Hbx.
    { eapply path_to_elem in Hel;eauto. destructH. eapply tag_depth_unroot;eauto with diamond. }
    eapply ex_entry_innermost in Hinner';eauto.
    erewrite <-tl_eq in Hinner';eauto.
    specialize (tcfg_reachability Dlen) as Hproot. destructH.
    specialize Dpath1 as Hπ.
    eapply path_app in Hπ. 3: eapply Dsk1. 2:eauto.
    assert ((h', 0 :: tl j1) ∉ t) as Hnin.
    - intro N.
      eapply path_from_elem in N;eauto. destructH.
      eapply postfix_incl in Hinner';eauto.
      eapply path_to_elem in Hinner';eauto. destructH.
      eapply path_app in Hinner'0 as Hel0'. 3: eapply Dsk2. 2:eapply N0.
      eapply tcfg_fresh in Hel0'.
      + eapply Taglt_irrefl;eauto.
      + eapply innermost_eq_loop in Hinner. rewrite Hinner. setoid_rewrite <-j_len1. 2:eauto.
        destruct j1;cbn;eauto.
        exfalso. eapply loop_contains_depth_lt in Hh. setoid_rewrite <-j_len1 in Hh;eauto.
        cbn in Hh. lia.
      + destruct ϕ1,ϕ0;try rewrite app_length;cbn;try lia;inv Hinner'0;inv N0.
    - specialize Dqj1 as Hqj1.
      cbn in Hπ.
      destruct r1;cbn in Hqj1.
      + inv Hqj1. eapply ex_entry_innermost in Hproot;cbn;eauto.
        * rewrite depth_root. eauto.
        * eapply root_no_loop.
      + subst p. inv_path Hπ.
        eapply ex_entry_innermost in H1;cbn;eauto.
        * rewrite app_comm_cons in H1. eapply in_app_or in H1. destruct H1;[|contradiction].
          eapply Ddisj;eauto. eapply postfix_incl;eauto.
        * rewrite depth_root. eauto.
        * eapply root_no_loop.
  Qed.

  Lemma no_back : forall x : Lab, x ∈ (map fst r1) -> ~ loop_contains x q1.
  Proof. (* Hjle needed *)
    intros h' Hel Hnin.
    eapply in_fst in Hel.
    destructH.
    decide (innermost_loop h' q1).
    - eapply no_head_inst in Hel as Hel';eauto.
    - simpl_dec' n.
      destruct n;[contradiction|]. eapply H.
      eapply r1_incl_head_q'. eapply in_map with (f:=fst) in Hel. cbn in Hel. assumption.
  Qed.

End disj.

Lemma tpath_deq_no_haed_tag_eq `(C : redCFG) p q q0 i j t
      (Hlen : | j | = depth q)
      (Hpath : TPath (q,j) (p,i) t)
      (Hincl : forall x, x ∈ map fst t -> deq_loop x q0)
      (Hnback : forall x : Lab, x ∈ (map fst t) -> ~ loop_contains x q0)
  : take_r (depth q0) i = take_r (depth q0) j.
Proof.
  revert q p i j Hpath Hlen.
  induction t;intros;inv_path Hpath.
  - reflexivity.
  - exploit' IHt.
    { intros. eapply Hincl. cbn. right;eauto. }
    exploit' IHt.
    { intros. eapply Hnback. cbn. right. eauto. }
    destruct x as [e l].
    eapply tcfg_edge_destruct' in H0.
    destruct H0 as [H0|[H0|[H0|H0]]].
    all: destruct H0 as [Htag Hedge];subst.
    + eapply IHt;eauto.
    + rewrite take_r_cons_drop.
      * eapply IHt;eauto.
      * eapply tag_depth_unroot in H as Hdep;eauto. rewrite Hdep.
        eapply deq_loop_depth. eapply Hincl. cbn. right.
        eapply path_contains_front in H. eapply in_map with (f:=fst) in H. eauto.
    + destruct l;[exfalso|].
      * eapply loop_contains_ledge in Hedge. eapply loop_contains_depth_lt in Hedge.
        eapply tag_depth_unroot in H;eauto. cbn in H. lia.
      * cbn in Hpath. cbn.
        erewrite take_r_cons_replace.
        -- eapply IHt;eauto.
        -- specialize (Hnback p). exploit Hnback. 1: cbn;left;auto.
           decide (S (|l|) <= depth q0);[exfalso|lia].
           eapply tag_depth_unroot in H as Hdep;eauto. cbn in Hdep. rewrite Hdep in l0.
           assert (deq_loop e q0) as Hdeq.
           {
             eapply Hincl. cbn. right. eapply path_contains_front in H.
             eapply in_map with (f:=fst) in H. cbn in H. assumption.
           }
           eapply deq_loop_depth_leq in l0;eauto.
           eapply Hnback. eapply deq_loop_head_loop_contains;eauto.
           ++ eapply back_edge_eq_loop in Hedge. rewrite <-Hedge. eauto.
           ++ eexists;eauto.
    + destruct l;[exfalso|].
      * eapply tag_depth_unroot in H;eauto. cbn in H. eapply depth_exit in Hedge. lia.
      * cbn. cbn in Hpath.
        erewrite <-take_r_cons_drop.
        -- eapply IHt;eauto.
        -- eapply tag_depth_unroot in Hpath;eauto. rewrite Hpath.
           eapply deq_loop_depth. eapply Hincl;cbn. eauto.
Qed.

Lemma in_snd
  : forall (A B : Type) (b : B) (l : list (A * B)), b ∈ map snd l -> exists a : A, (a, b) ∈ l.
Proof.
  intros.
  induction l.
  - contradiction.
  - destruct a. cbn in H. destruct H.
    + subst. eexists. left. eauto.
    + exploit IHl. destructH. eexists. right. eassumption.
Qed.

Lemma tag_eq1 `(D : DiamondPaths)
      (Hjle : j1 ⊴ j2)
    : forall j, j ∈ map snd r1 -> take_r (depth q1) j = j1.
  Proof.
    intros. destruct r1;[contradiction|].
    inv_Dpaths D.
    specialize Dpath1 as Hpath1.
    inv_path Hpath1.
    eapply in_snd in H. destructH.
    eapply path_to_elem in H as Hϕ;eauto. destructH.
    eapply tpath_deq_no_haed_tag_eq in Hϕ0.
    - eapply tpath_deq_no_haed_tag_eq in H0 as Hpath1';eauto with diamond.
      + erewrite <-take_r_geq.
        * rewrite Hpath1'. eapply Hϕ0.
        * erewrite j_len1;eauto.
      + intros. eapply r1_incl_head_q';eauto.
      + intros. eapply no_back;eauto.
    - eauto with diamond.
    - intros. eapply r1_incl_head_q';eauto. eapply prefix_incl;eauto.
      eapply prefix_map_fst;eauto.
    - intros. eapply no_back;eauto. eapply prefix_incl;eauto. eapply prefix_map_fst;eauto.
  Qed.

  Lemma tag_eq_kj1 `(D : DiamondPaths)
        (Hjle : j1 ⊴ j2)
    : take_r (depth q1) k = j1.
  Proof.
    destruct r1;inv_Dpaths D.
    - rewrite take_r_geq;eauto. rewrite Dlen. eauto.
    - assert (l1 ∈ map snd ((q1,j1) :: r1)) as Hin.
      {
        destruct D. inv_path Dpath1. eapply path_contains_back in H.
        eapply in_map with (f:=snd) in H. unfold snd in H at 1. eauto.
      }
      assert (depth q1 <= | k |) as Hdep.
      {
        erewrite Dlen. eapply deq_loop_depth. eapply s_deq_q;eauto.
      }
      specialize (tcfg_edge_destruct' Dsk1) as Dsk1.
      destruct Dsk1 as [H|[H|[H|H]]].
      all: destruct H as [Htag Hedge].
      + rewrite <-Htag. eapply tag_eq1;eauto.
      + destruct l1;[congruence|]. inv Htag.
        setoid_rewrite <-tag_eq1 at 3. 2,3,4:eauto.
        rewrite take_r_cons_drop;eauto.
      + decide (loop_contains u1 q1).
        * exfalso.
          eapply no_back;eauto.
          destruct D. inv_path Dpath1. eapply path_contains_back in H.
          eapply in_map with (f:=fst) in H. cbn in H. cbn. eauto.
        * setoid_rewrite <-tag_eq1 at 3. 2,3,4:eauto.
          destruct k;[exfalso|].
          {
            cbn in *. eapply loop_contains_ledge in Hedge. eapply loop_contains_depth_lt in Hedge.
            destruct D. cbn in Dlen. lia.
          }
          assert (depth q1 < depth u1) as Hlt.
          {
            eapply le_lt_or_eq in Hdep.
            destruct Hdep.
            - cbn in H. cbn in Htag. eapply u_len1 in D. rewrite Htag in D. cbn in D. lia.
            - exfalso. eapply n. cbn in *. eapply u_len1 in D as Hlen. rewrite Htag in Hlen.
              cbn in Hlen.
              eapply deq_loop_head_loop_contains.
              + eapply deq_loop_depth_eq. eapply r1_incl_head_q';eauto. 2:lia.
                destruct D. inv_path Dpath1. eapply path_contains_back in H0.
                eapply in_map with (f:=fst) in H0. cbn in *. eauto.
              + eexists;eauto.
          }
          destruct l1;[cbn in *;congruence|]. inv Htag.
          erewrite take_r_cons_replace;eauto.
          eapply back_edge_eq_loop in Hedge. rewrite <-Hedge in Hlt. cbn in Hdep.
          destruct D. cbn in Dlen. lia.
      + setoid_rewrite <-tag_eq1 at 3. 2-4:eauto.
        destruct k;[exfalso|].
        * destruct D. cbn in Dlen. eapply depth_exit in Hedge. lia.
        * cbn. cbn in Htag.
          erewrite take_r_cons_drop.
          -- subst. reflexivity.
          -- eapply u_len1 in D as Hlen. subst k. rewrite Hlen. eapply deq_loop_depth.
             eapply r1_incl_head_q';eauto.
             destruct D. inv_path Dpath1. eapply path_contains_back in H.
             eapply in_map with (f:=fst) in H. cbn in *. eauto.
  Qed.

  Lemma k_eq_j `(D : DiamondPaths)
        (Hdeq : deq_loop q1 s)
        (Hjle : j1 ⊴ j2)
    : k = j1.
  Proof.
    rewrite <-take_r_geq at 1. eapply tag_eq_kj1;eauto. erewrite Dlen.
    eapply deq_loop_depth. eauto.
  Qed.

  Section disj_eqdep.
    Context `(C : redCFG).
    Variables (s u1 u2 p1 p2 q1 q2 : Lab)
              (k i l1 l2 j1 j2 : Tag)
              (r1 r2 : list (Lab * Tag)).
    Hypothesis (Hdeq : deq_loop q1 s).
    Hypothesis (Hjle : j1 ⊴ j2).

    Lemma lj_eq1 (D : DiamondPaths s u1 u2 p1 p2 q1 q2 k i l1 l2 j1 j2 ((q1,j1) :: r1) r2)
      : l1 = j1 \/ l1 = 0 :: j1.
    Proof. (* Hjle needed *)
      specialize (tcfg_edge_destruct' Dsk1) as Dsk1.
      destruct Dsk1 as [Dsk1|[Dsk1|[Dsk1|Dsk1]]].
      all: destruct Dsk1 as [Htag Hedge].
      - left. rewrite Htag. eapply k_eq_j;eauto.
      - right. rewrite Htag. f_equal. eapply k_eq_j;eauto.
      - exfalso. eapply no_back;eauto;cycle 1.
        + eapply loop_contains_ledge in Hedge. eapply Hdeq in Hedge. eauto.
        + destruct D. inv_path Dpath1. eapply path_contains_back in H.
          eapply in_map with (f:=fst) in H. unfold fst in H at 1. eauto.
      - exfalso. destruct Hedge. eapply exit_not_deq in H;eauto.
        eapply eq_loop_exiting in H. rewrite H. transitivity q1;eauto.
        eapply r1_incl_head_q';eauto.
        destruct D. inv_path Dpath1. eapply path_contains_back in H0.
        eapply in_map with (f:=fst) in H0. unfold fst in H0 at 1. eauto.
    Qed.

    Lemma lj_eq2 (D : DiamondPaths s u1 u2 p1 p2 q1 q2 k i l1 l2 j1 j2 r1 ((q2,j2) :: r2))
      : l2 = j1 \/ l2 = 0 :: j1 \/ loop_contains u2 q1.
    Proof. (* Hjle needed *)
      specialize (tcfg_edge_destruct' Dsk2) as Dsk2.
      destruct Dsk2 as [Dsk1|[Dsk1|[Dsk1|Dsk1]]].
      all: destruct Dsk1 as [Htag Hedge].
      - left. rewrite Htag. eapply k_eq_j;eauto.
      - right. left. rewrite Htag. f_equal. eapply k_eq_j;eauto.
      - right. right. eapply loop_contains_ledge in Hedge. eapply Hdeq;eauto.
      - exfalso. destruct Hedge. eapply exit_not_deq in H;eauto.
        eapply eq_loop_exiting in H. rewrite H. transitivity q1;eauto.
        eapply r2_incl_head_q';eauto.
        destruct D. inv_path Dpath2. eapply path_contains_back in H0.
        eapply in_map with (f:=fst) in H0. unfold fst in H0 at 1. eauto.
    Qed.

  End disj_eqdep.


Lemma no_back2 `(D : DiamondPaths)
      (Htageq : j1 = j2)
  : forall x : Lab, x ∈ (map fst r2) -> ~ loop_contains x q1.
Proof.
  setoid_rewrite Dloop.
  eapply no_back.
  - eapply DiamondPaths_sym;eauto.
  - subst. reflexivity.
Qed.

Lemma r1_incl_head_q `(D : DiamondPaths)
  : forall x, x ∈ map fst r1 -> deq_loop x q1.
Proof.
  specialize (jj_len D) as Hlen.
  eapply tagle_or in Hlen.
  destruct Hlen.
  - eapply r1_incl_head_q';eauto.
  - setoid_rewrite Dloop.
    eapply r2_incl_head_q';eauto.
    eapply DiamondPaths_sym;eauto.
Qed.

Lemma r2_incl_head_q `(D : DiamondPaths)
  : forall x, x ∈ map fst r2 -> deq_loop x q1.
Proof.
  setoid_rewrite Dloop.
  eapply r1_incl_head_q.
  eapply DiamondPaths_sym;eauto.
Qed.

Lemma u1_deq_q `(D : DiamondPaths)
      (Hnnil : r1 <> [])
  : deq_loop u1 q1.
Proof.
  eapply r1_incl_head_q;eauto.
  destruct r1;[contradiction|].
  destruct D.
  inv_path Dpath1.
  eapply path_contains_back in H.
  fold (fst (u1,l1)).
  eapply in_map;eauto.
Qed.

Lemma u2_deq_q `(D : DiamondPaths)
      (Hnnil : r2 <> [])
  : deq_loop u2 q1.
Proof.
  rewrite Dloop.
  eapply u1_deq_q;eauto using DiamondPaths_sym.
Qed.

Lemma diamond_teq `(C : redCFG)
      (s u1 u2 p1 p2 q1 q2 : Lab) (k i l1 l2 j1 j2 : Tag) r1 r2
      (Hdeq : deq_loop q1 s)
      (Hjle : j1 ⊴ j2)
      (D : DiamondPaths s u1 u2 p1 p2 q1 q2 k i l1 l2 j1 j2 ((q1,j1) :: r1) ((q2,j2) :: r2))
  : TeqPaths u1 u2 q1 q2 l1 l2 j1 j2 (r1) (r2).
Proof.
  copy D D'.
  destruct D.
  inv_path Dpath1. inv_path Dpath2.
  econstructor; eauto using tl_eq, lj_eq1, lj_eq2, jj_len, j_len1.
Qed.

Lemma diamond_qj_eq1 `(C : redCFG) s u1 u2 p1 p2 q1 q2 k i l1 l2 j1 j2 qj1 r1 r2
      (D : DiamondPaths s u1 u2 p1 p2 q1 q2 k i l1 l2 j1 j2 (qj1 :: r1) r2)
  : qj1 = (q1,j1).
Proof.
  destruct D. cbn in Dqj1. auto.
Qed.

Lemma diamond_qj_eq2 `(C : redCFG) s u1 u2 p1 p2 q1 q2 k i l1 l2 j1 j2 qj2 r1 r2
      (D : DiamondPaths s u1 u2 p1 p2 q1 q2 k i l1 l2 j1 j2 r1 (qj2 :: r2))
  : qj2 = (q2,j2).
Proof.
  destruct D. cbn in Dqj2. auto.
Qed.
