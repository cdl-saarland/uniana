Require Export TcfgqMonotone.
Require Import Lia.

Definition sub_tag i j := |i| = |j| /\ hd 0 i <= hd 0 j /\ tl i = tl j.

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
