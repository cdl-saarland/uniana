Require Export TcfgqMonotone Precedes TcfgDet.
Require Import Lia.

Definition sub_tag i j := |i| = |j| /\ hd 0 i <= hd 0 j /\ tl i = tl j.

Definition pre_sub_tag i j := exists j', Prefix j' j /\ sub_tag i j'.

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

Global Instance sub_tag_refl : Reflexive sub_tag.
Proof.
  unfold Reflexive. intros.
  unfold sub_tag. split_conj;eauto.
Qed.

Lemma tcfg_prefix_no_back `(C : redCFG) (h p q : Lab) (i j k : Tag) t
      (Hdeq : deq_loop p q)
      (Hpath : TPath (q,j) (p,i) t)
      (Hstag : Prefix j i)
      (Hdep : |j| = depth q)
      (Hin : (h,k) ∈ (r_tl t))
  : ~ loop_contains h q.
Proof.
  specialize (tcfg_reachability Hdep) as Hreach.
  destructH. intro Hloop.
  eapply loop_contains_deq_loop in Hloop as Hdeqqh.
  assert (| take_r (depth h) j | = depth h) as Hheq.
  { rewrite take_r_length_le;auto. rewrite Hdep. eapply deq_loop_depth. eauto. }
  eapply loop_tag_dom in Hreach as Hdom;eauto. 2:reflexivity.
  destr_r' t;subst. 1: cbn in Hin;contradiction.
  unfold TPath in Hpath. path_simpl' Hpath. rewrite r_tl_rcons in Hin.
  eapply path_from_elem in Hpath as Hϕ. 2: eauto.
  2: eapply In_rcons;right;eauto. destructH.
  eapply tag_depth_unroot in Hdep as Hdepp;eauto.
  eapply tag_depth_unroot2 in Hϕ0 as Hdeph;eauto.
  eapply tagle_monotone in Hϕ0 as Hmon0. 3,5:reflexivity. all:eauto. 2: transitivity q;eauto.
  eapply path_to_elem in Hpath as Hπ. 2: eapply In_rcons;right;eauto. destructH.
  eapply tagle_monotone in Hπ0 as Hmon1;eauto. 2: reflexivity.
  rewrite take_r_geq in Hmon0. 2:lia.
  setoid_rewrite take_r_geq in Hmon1 at 2. 2:lia.
  destruct Hmon1.
  - eapply taglt_tagle_trans in H;eauto.
    clear - H Hstag Hdeph Hdep Hdeqqh.
    eapply taglt_leq with (n:=|j|) in H.
    + eapply prefix_take_r in Hstag. rewrite Hstag in H. rewrite take_r_self in H.
      eapply Taglt_irrefl;eauto.
    + rewrite Hdep. eapply deq_loop_depth;eauto.
    + eapply prefix_len_leq;eauto.
    + reflexivity.
  - subst k. eapply path_from_elem in Hdom;eauto. destructH.
    destruct l;[contradiction|]. cbn in Hpath. path_simpl' Hpath. eapply path_rcons_inv' in Hpath.
    destructH. destruct p0.
    eapply path_to_elem in Hin;eauto. destructH.
    eapply Taglt_irrefl. eapply tcfg_fresh.
    + eapply path_app in Hpath1;eauto.
    + eauto.
    + destruct ϕ1;[inv Hdom0|];destruct ϕ2;[inv Hin0|]. cbn. rewrite app_length. cbn. lia.
Qed.

Lemma tcfg_subtag_deq `(C : redCFG) (x p q : Lab) (i j : Tag) t
      (Hdeq : deq_loop p q)
      (Hpath : TPath (q,j) (p,i) t)
      (Hstag : sub_tag j (take_r (depth q) i))
      (Hdep : |j| = depth q)
      (Hin : x ∈ map fst t)
  : deq_loop x q.
Proof.
  decide (deq_loop x q);[eauto|exfalso].
  do 2 simpl_dec' n. destructH.
  eapply in_fst in Hin. destructH.
  eapply path_from_elem in Hin as Hϕ;eauto. destructH.
  eapply tag_depth_unroot in Hpath as Hdepp;eauto.
  eapply tag_depth_unroot2 in Hϕ0 as Hdepx;eauto.
  assert (depth x0 <= depth p) as Hdep_leq.
  { eapply loop_contains_deq_loop in n0. rewrite n0 in Hdeq. eapply deq_loop_depth in Hdeq;eauto. }
  specialize (@take_take_r _ i (|i| - (depth x0 - 1)) (depth x0 - 1)) as Hi. exploit Hi. 1: lia.
  copy n1 n1'.
  eapply ex_entry in n1. 3:rewrite Hi in Hϕ0;eauto. all:eauto.
  2: { rewrite take_r_length_le;eauto. lia. }
  destr_r' t;subst. 1:contradiction. eapply In_rcons in Hin. destruct Hin.
  - subst x1. unfold TPath in Hpath. eapply path_back in Hpath. inversion Hpath. subst x.
    contradiction.
  - destr_r' ϕ;subst. 1:contradiction. path_simpl' Hϕ0.
    eapply In_rcons in n1. destruct n1.
    + inv H0. eapply n1'. eauto using loop_contains_self, loop_contains_loop_head.
    + specialize (tcfg_reachability Hdep) as Hreach.
      destructH.
      eapply loop_tag_dom with (j0:=0 :: take_r (depth x0 - 1) i) in Hreach as Hdom. 2: eapply n0.
      * unfold TPath in Hpath. path_simpl' Hpath.
        eapply path_app' in Hpath. 2: eapply Hreach. eapply tpath_NoDup in Hpath.
        rewrite <-app_assoc in Hpath.
        eapply NoDup_app in Hpath.
        -- eapply Hpath. destruct t;[contradiction|]. unfold TPath in Hreach. path_simpl' Hreach.
           cbn. eauto.
        -- eapply postfix_incl;eauto using postfix_rcons_rcons.
      * unfold sub_tag. split_conj.
        -- cbn. rewrite take_r_length_le. 2: rewrite Hdepp;lia.
           rewrite take_r_length_le. 2:rewrite Hdep;eauto using deq_loop_depth, loop_contains_deq_loop.
           eapply loop_contains_loop_head in n0. eapply depth_loop_head in n0. lia.
        -- cbn. lia.
        -- cbn. rewrite take_r_tl_eq.
           rewrite take_r_length_le. 2: rewrite Hdep;eauto using deq_loop_depth,loop_contains_deq_loop.
           rewrite take_r_take_r_leq. 2:lia.
           destruct j. 1: { cbn in Hdep. eapply loop_contains_depth_lt in n0. lia. }
           assert (depth x0 > 0 ) as Hx0.
           { cbn in Hdepp. eapply loop_contains_loop_head in n0. eapply depth_loop_head in n0. auto. }
           destruct i. 1:{ cbn in Hdepp. lia. }
           cbn in Hdep, Hdepp.
           assert (depth x0 - 1 <= | j |) as Hx0j.
           { eapply loop_contains_deq_loop in n0. eapply deq_loop_depth in n0. lia. }
           rewrite take_r_cons_drop. 2:lia. rewrite take_r_cons_drop. 2:auto.
           destruct Hstag as [_ [_ Hstag]]. cbn in Hstag.
           rewrite take_r_tl_eq in Hstag.
           eapply deq_loop_depth in Hdeq as Hdepleq.
           rewrite take_r_length_le in Hstag. 2:cbn;lia.
           rewrite take_r_take_r_leq in Hstag. 2:lia.
           rewrite take_r_cons_drop in Hstag. 2:lia. rewrite Hstag.
           rewrite take_r_take_r_leq. 2:lia. reflexivity.
      * cbn. rewrite take_r_length_le. 2:lia. eapply loop_contains_loop_head in n0.
        eapply depth_loop_head in n0. lia.
Qed.

Lemma tcfg_prefix_deq `(C : redCFG) (x p q : Lab) (i j : Tag) t
      (Hdeq : deq_loop p q)
      (Hpath : TPath (q,j) (p,i) t)
      (Hstag : Prefix j i)
      (Hdep : |j| = depth q)
      (Hin : x ∈ map fst t)
  : deq_loop x q.
Proof.
  decide (deq_loop x q);[eauto|exfalso].
  do 2 simpl_dec' n. destructH.
  eapply in_fst in Hin. destructH.
  eapply path_from_elem in Hin as Hϕ;eauto. destructH.
  eapply tag_depth_unroot in Hpath as Hdepp;eauto.
  eapply tag_depth_unroot2 in Hϕ0 as Hdepx;eauto.
  assert (depth x0 <= depth p) as Hdep_leq.
  { eapply loop_contains_deq_loop in n0. rewrite n0 in Hdeq. eapply deq_loop_depth in Hdeq;eauto. }
  specialize (@take_take_r _ i (|i| - (depth x0 - 1)) (depth x0 - 1)) as Hi. exploit Hi. 1: lia.
  copy n1 n1'.
  eapply ex_entry in n1. 3:rewrite Hi in Hϕ0;eauto. all:eauto.
  2: { rewrite take_r_length_le;eauto. lia. }
  destr_r' t;subst. 1:contradiction. eapply In_rcons in Hin. destruct Hin.
  - subst x1. unfold TPath in Hpath. eapply path_back in Hpath. inversion Hpath. subst x.
    contradiction.
  - destr_r' ϕ;subst. 1:contradiction. path_simpl' Hϕ0.
    eapply In_rcons in n1. destruct n1.
    + inv H0. eapply n1'. eauto using loop_contains_self, loop_contains_loop_head.
    + eapply tcfg_prefix_no_back. 2: eapply Hpath. all:eauto.
      eapply postfix_rcons_rcons in Hϕ1. eapply postfix_incl in H0;eauto.
      rewrite r_tl_rcons. eauto.
Qed.

Lemma loop_tag_dom_prec `(C : redCFG) (h p : Lab) (i j : Tag) t
      (Hloop : loop_contains h p)
      (Hpath : TPath (root,start_tag) (p,i) t)
      (Hstag : Prefix j i)
      (Hdep : |j| = depth h)
  : Precedes fst t (h,j).
Proof.
  eapply loop_tag_dom in Hpath as Hdom;eauto.
  - eapply path_from_elem in Hdom as Hϕ;eauto. destructH.
    destr_r' ϕ;subst. 1: inv Hϕ0.
    path_simpl' Hϕ0.
    eapply postfix_eq in Hϕ1. destructH. subst t.
    eapply loop_contains_deq_loop in Hloop as Hdeq.
    assert (forall k, (h,k) ∉ l).
    { intros. intro N.
      eapply tcfg_prefix_no_back;eauto.
      - rewrite r_tl_rcons. eauto.
      - eauto using loop_contains_self,loop_contains_loop_head.
    }
    clear - H.
    induction l;cbn.
    + econstructor.
    + destruct a.
      econstructor.
      * cbn. intro N. subst. eapply H. left;eauto.
      * eapply IHl;eauto. intros k Hk. eapply H;eauto.
  - eapply prefix_eq in Hstag. destructH. subst i.
    rewrite take_r_app_eq;eauto.
    unfold sub_tag. split_conj;eauto.
Qed.

Lemma tpath_deq_no_haed_tag_eq' `(C : redCFG) p q q0 i j t
      (Hlen : | j | = depth q)
      (Hpath : TPath (q,j) (p,i) t)
      (Hincl : forall x, x ∈ map fst t -> deq_loop x q0)
      (Hnback : forall x : Lab, x ∈ (map fst (r_tl t)) -> ~ loop_contains x q0)
  : take_r (depth q0) i = take_r (depth q0) j.
Proof.
  revert q p i j Hpath Hlen.
  induction t;intros;inv_path Hpath.
  - reflexivity.
  - exploit' IHt.
    { intros. eapply Hincl. cbn. right;eauto. }
    exploit' IHt.
    { intros. eapply Hnback.
      eapply incl_map. 2: eapply H1.
      destr_r' t;subst;cbn;eauto. rewrite app_comm_cons. do 2 rewrite r_tl_rcons. eauto.
    }
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
        -- specialize (Hnback p). exploit Hnback.
           {
             destr_r' t;subst. 1: inv H. rewrite app_comm_cons. rewrite r_tl_rcons.
             cbn. left;eauto.
           }
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

Lemma tpath_deq_no_haed_tag_eq `(C : redCFG) p q q0 i j t
      (Hlen : | j | = depth q)
      (Hpath : TPath (q,j) (p,i) t)
      (Hincl : forall x, x ∈ map fst t -> deq_loop x q0)
      (Hnback : forall x : Lab, x ∈ (map fst t) -> ~ loop_contains x q0)
  : take_r (depth q0) i = take_r (depth q0) j.
Proof.
  eapply tpath_deq_no_haed_tag_eq';eauto.
  intros;eapply Hnback.
  eapply incl_map. 2:eauto.
  destr_r' t;subst;cbn;eauto. rewrite r_tl_rcons. eauto.
Qed.

Lemma head_precedes_no_back `(C : redCFG) h p k i t
      (Hloop : loop_contains h p)
      (Hpath : TPath (h,k) (p,i) t)
      (Hprec : Precedes fst t (h,k))
  : forall x : Lab, x ∈ (map fst (r_tl t)) -> ~ loop_contains x h.
Admitted.

Lemma head_precedes_deq `(C : redCFG) h p k i t
      (Hloop : loop_contains h p)
      (Hpath : TPath (h,k) (p,i) t)
      (Hprec : Precedes fst t (h,k))
  : forall x, x ∈ map fst t -> deq_loop x h.
Admitted.
