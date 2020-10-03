Require Export SpathIncl.
Require Import Lia.

Section disj.

  Infix "-->" := edge__P.

  Context `(D : DiamondPaths).
  Hypothesis (Hjle : j1 ⊴ j2).

  Lemma s_deq_q
    : deq_loop s q1.
  Proof.
    clear Hjle.
    eapply diamond_split in D. eapply spath_s_deq_q;eauto.
  Qed.

  Lemma no_head_inst (h : Lab) (l : Tag)
        (Hcont : innermost_loop h q1)
        (Hel : (h,l) ∈ r1)
    : False.
  Proof.
    eapply diamond_split in D. eapply spath_no_head_inst;eauto.
  Qed.

  Lemma no_back : forall x : Lab, x ∈ (map fst r1) -> ~ loop_contains x q1.
  Proof. (* Hjle needed *)
    eapply diamond_split in D. eapply spath_no_back;eauto.
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

Lemma r1_incl_head_q `(D : DiamondPaths)
  : forall x, x ∈ map fst r1 -> deq_loop x q1.
Proof.
  eapply diamond_split in D.
  eapply spath_r1_incl_head_q. eassumption.
Qed.

Lemma r2_incl_head_q `(D : DiamondPaths)
  : forall x, x ∈ map fst r2 -> deq_loop x q1.
Proof.
  eapply diamond_split in D.
  eapply spath_r2_incl_head_q. eassumption.
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
      + intros. eapply r1_incl_head_q;eauto.
      + intros. eapply no_back;eauto.
    - eauto with diamond.
    - intros. eapply r1_incl_head_q;eauto. eapply prefix_incl;eauto.
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
              + eapply deq_loop_depth_eq. eapply r1_incl_head_q;eauto. 2:lia.
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
             eapply r1_incl_head_q;eauto.
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
        eapply r1_incl_head_q;eauto.
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
        eapply r2_incl_head_q;eauto.
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
