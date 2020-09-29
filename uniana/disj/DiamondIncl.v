Require Export DiamondPaths.
Require Import Lia.


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
      (Htagle : j ⊴ i)
  : (h,j) ∈ t.
Proof.
  destruct Htagle.
  2: { subst. eapply path_contains_front;eauto. }
  revert h Hloop Hpath.
  induction H;intros.
  - induction H.
    + induction t.
      * inv Hpath.
      *
Admitted.

Lemma loop_tag_dom `(C : redCFG) (h p : Lab) (i j : Tag) t
      (Hloop : loop_contains h p)
      (Hpath : TPath (root,start_tag) (p,i) t)
      (Htagle : j ⊴ take_r (depth h) i)
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

  Lemma head_in_both (h : Lab) (l : Tag)
        (Hcont : loop_contains h q1)
        (Hel : (h,l) ∈ r1)
    : (h,l) ∈ r2.
  Proof.
    specialize (Dpath1) as Dpath1'.
    specialize (Dpath2) as Dpath2'.
    specialize (Dsk1) as Dsk1'.
    specialize (Dsk2) as Dsk2'.
    assert (loop_contains h s) as Hloops.
    { eapply s_deq_q;eauto. }
    specialize (tcfg_reachability Dlen) as Hreach.
    destructH.
    specialize (Dpath2) as Hpath2.
    eapply path_app in Hpath2. 2: eapply Hreach. 2: eauto with diamond.
    specialize (Dpath1) as Hpath1.
    eapply path_app in Hpath1. 2: eapply Hreach. 2: eauto with diamond.
    cbn in Hpath1,Hpath2.
    assert (|l| = depth h) as Hdeph.
    {
      eapply tag_depth_unroot_elem. 1:eapply Hpath1. 1: cbn;symmetry;eapply depth_root.
      right. eapply in_or_app. left. assumption.
    }
    destruct r1,r2;inv_Dpaths D.
    1,2: contradiction.
    - exfalso.
      inv_path Dpath1'. clear Dpath1'. rename H into Dpath1'.
      assert (| take_r (depth h) k | = depth h) as Htakeh.
      {
        rewrite take_r_length_le;[reflexivity|].
        rewrite Dlen;eapply deq_loop_depth;eapply loop_contains_deq_loop;eauto.
      }
      assert (l ⊴ take_r (depth h) j1) as Hkj.
      {
        rewrite <-take_r_geq with (n:=depth h) at 1.
        2: rewrite <-Hdeph;eauto.
        eapply path_from_elem in Hel;eauto. destructH.
        eapply tagle_monotone;eauto.
        1: reflexivity.
        eapply loop_contains_deq_loop;eauto.
      }
      eapply loop_tag_dom in Hreach as Hentry. 2:eauto. 2:reflexivity. 2: eauto.
      eapply path_from_elem in Hreach;eauto.
      destructH.
      eapply path_to_elem in Hel. 2: eapply Dpath1'.
      destructH.
      eapply path_app in Hel0 as Happ. 2: eapply Hreach0. 2: eapply Dsk1'.
      eapply tcfg_fresh in Happ. 2:eauto.
      + eapply tagle_take_r with (n:=depth h) in Hjle.
        eapply taglt_tagle_trans in Happ;eauto.
        eapply tagle_taglt_trans in Happ;eauto.
        eapply Taglt_irrefl;eauto.
      + inv_path Hel0;inv_path Hreach0;cbn.
        all: try rewrite app_length;cbn;lia.
    - cbn in Hpath2. inv_path Hpath2.
      inv_path Dpath1'. clear Dpath1'. rename H1 into Dpath1'.
      enough ((h,l) ∈ (((q2,j2) :: l3) ++ t)).
      + eapply in_app_or in H1.
        destruct H1;[assumption|exfalso].
        eapply path_from_elem in H1;eauto.
        destructH.
        eapply path_to_elem in Hel as Hel;eauto. destructH.
        eapply path_app in Hel0 as Happ. 2: eapply H3. 2: eapply Dsk1'.
        eapply Taglt_irrefl. eapply tcfg_fresh;eauto.
        inv_path Hel0;inv_path H3.
        all: try rewrite app_length;cbn;lia.
      + eapply loop_tag_dom. 2:eauto.
        * rewrite <-Dloop. assumption.
        * eapply tagle_take_r with (n:=depth h) in Hjle. rewrite <-Hjle.
          eapply path_from_elem in Hel;eauto. destructH.
          erewrite <-take_r_geq with (n:=depth h) at 1.
          2: rewrite Hdeph. 2:lia.
          eapply tagle_monotone.
          all: eauto with diamond.
          -- reflexivity.
          -- eapply loop_contains_deq_loop;eauto.
        * eapply tag_depth_unroot_elem. 1:eapply Hpath1. 1: cbn;symmetry;eapply depth_root.
          right. eapply in_or_app. left. assumption.
  Qed.

  Lemma r1_incl_head_q : forall x, x ∈ map fst r1 -> deq_loop x q1.
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
    eapply postfix_incl in Hfst1. eapply Hfst1 in Hentry. eapply head_in_both in Hentry as Hentry2.
    2: destruct Hinner1;eauto.
    eapply Ddisj;eauto.
  Qed.

  Lemma u1_deq_q
        (Hnnil : r1 <> [])
    : deq_loop u1 q1.
  Proof.
    eapply r1_incl_head_q.
    destruct r1;[contradiction|].
    destruct D.
    inv_path Dpath1.
    eapply path_contains_back in H.
    fold (fst (u1,l1)).
    eapply in_map;eauto.
  Qed.

  Lemma r2_incl_head_q : forall x, x ∈ map fst r2 -> deq_loop x q1.
  Proof.
  Admitted.

  Lemma u2_deq_q
        (Hnnil : r2 <> [])
    : deq_loop u2 q1.
  Proof.
    clear Hjle.
  Admitted.

  Lemma no_back : forall x : Lab, x ∈ (q1 :: map fst r1) -> ~ loop_contains x q1.
  Proof. (* Hjle needed *)
  Admitted.

  Lemma no_back2
        (Htageq : j1 = j2)
    : forall x : Lab, x ∈ (q2 :: map fst r2) -> ~ loop_contains x q1.
  Proof.
    clear Hjle.
  Admitted.

  Lemma tag_eq_take_r
    : forall h q' k', (q',k') ∈ r1 -> deq_loop q' h -> deq_loop s h -> take_r (depth h) k' = take_r (depth h) k.
  Proof.
  Admitted.


  Section disj_eqdep.
    Hypothesis (Hdeq : deq_loop q1 s).

    Lemma lj_eq1
      : l1 = j1 \/ l1 = 0 :: j1.
    Proof. (* Hjle needed *)
    Admitted.

    Lemma lj_eq2
      : l2 = j1 \/ l2 = 0 :: j1 \/ loop_contains u2 q1.
    Proof. (* Hjle needed *)
    Admitted.

  End disj_eqdep.

End disj.

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
