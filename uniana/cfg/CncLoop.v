Require Export CFGinnermost CFGancestor.
Require Import Lia.

(** cnc & ocnc **)

Definition cnc_loop `{C : redCFG} h p q
  := loop_contains h p /\ ~ deq_loop q h.

Definition ocnc_loop `{C : redCFG} h p q
  := cnc_loop h p q /\ forall h', cnc_loop h' p q -> deq_loop h' h.

(*
(* the ocnc loop has an exit such that q is deeper or equal to the exit *)
Lemma ocnc_loop_exit `(C : redCFG) s q s'
      (Hocnc : ocnc_loop s q s')
  : exists e : Lab, exited s' e /\ deq_loop q e.
Admitted.
 *)

Lemma LPath_deq_loop `(C : redCFG) p q π
      (Hpath : LPath p q π)
  : deq_loop q p.
Proof.
  induction Hpath.
  - reflexivity.
  - transitivity b;eauto.
    destruct H. eapply loop_contains_deq_loop;eauto.
Qed.

Lemma LPath_loop_contains `(C : redCFG) p q π
      (Hpath : LPath p q (q :: π))
      (Hlen : π <> [])
  : loop_contains p q.
Proof.
  inv_path Hpath. 1: contradiction.
  revert dependent p.
  rinduction π.
  - contradiction.
  - destruct l.
    + cbn in H1. eapply path_single in H1. inv H1. cbn in Hpath. inv_path Hpath.
      destruct H2. eauto.
    + path_simpl' H1. cbn in H1. path_simpl' H1. eapply path_rcons_inv' in H1.
      destructH.
      specialize H with (p:=p0).
      exploit H.
      * congruence.
      * econstructor;eauto.
      * destruct H3. eapply loop_contains_trans;eauto.
Qed.

Lemma ex_ocnc_loop `(C : redCFG) p q
      (Hndeq : ~ deq_loop q p)
  : exists h, ocnc_loop h p q .
Proof.
  specialize (ex_near_ancestor p q) as Hanc.
  destructH.
  destruct Hanc as [Hanc Hnear].
  destruct Hanc as [[Hp Hq] | Hroot].
  - eapply loop_LPath in Hp as HL.
    destructH.
    inv_path HL.
    + exfalso.
      eapply Hndeq. eapply loop_contains_deq_loop;eauto.
    + destr_r' π0;subst. 1: inv H.
      path_simpl' H.
      copy HL HL'.
      eapply path_rcons_inv' in HL.
      destructH.
      exists p0. unfold ocnc_loop.
      assert (loop_contains p0 p) as Hlpp.
      {
        destruct HL1.
        destruct l.
        - eapply path_single in HL0. inv HL0.
          cbn in H. eapply path_single in H. inv H.
          decide (loop_head p). 1: eapply loop_contains_self;eauto.
          exfalso.
          do 2 simpl_dec' Hndeq. destructH. destructH.
          eapply Hndeq1.
          eapply H6 in Hndeq0 as QQ. destruct QQ.
          + eapply loop_contains_trans;eauto.
          + subst x1. exfalso. eapply n. eapply loop_contains_loop_head;eauto.
        - eapply LPath_loop_contains;eauto. congruence.
      }
      split.
      * unfold cnc_loop.
        split. 1:eauto.
        destruct HL1. destructH.
        contradict Hndeq.
        specialize (Hnear p0). exploit Hnear.
        { split;eauto. eapply deq_loop_head_loop_contains;eauto using loop_contains_loop_head. }
        eapply loop_contains_Antisymmetric in Hnear. exploit Hnear. subst p0. contradiction.
      * intros. destruct H1.
        destruct HL1.
        intros h Hh. destruct H4. eapply H5 in Hh.
        assert (loop_contains h p) as Hhp.
        { destruct Hh.
          - eauto using loop_contains_trans.
          - subst h. eauto.
        }
        eapply loop_contains_either in Hhp as Hpp. 2:eapply H1.
        destruct Hpp as [Hpp|Hpp]; [|eapply Hpp].
        destruct Hh.
        -- contradict H2. eapply loop_contains_deq_loop.
           eauto using loop_contains_trans.
        -- subst h.
           eapply H5 in Hpp. destruct Hpp.
           ++ contradict H2. eapply loop_contains_deq_loop.
              eauto using loop_contains_trans.
           ++ subst h'. eauto using loop_contains_self,loop_contains_loop_head.
  - subst a.
    do 2 simpl_dec' Hndeq. destructH.
    eapply loop_contains_outermost in Hndeq0. destructH.
    exists h'.
    split.
    + destruct Hndeq0.
      split.
      * eauto.
      * intro N. eapply deq_loop_head_loop_contains in N. 2:eauto using loop_contains_loop_head.
        specialize (Hnear h'). exploit Hnear.
        eapply root_no_loop;eauto.
    + intros. destruct H.
      destruct Hndeq0.
      eapply loop_contains_deq_loop.
      eapply H2;eauto.
Qed.

Lemma ocnc_depth `(C : redCFG) h p q
      (Hocnc : ocnc_loop h p q)
      (Hdeq : deq_loop p q)
  : depth h = S (depth q).
Proof.
  unfold ocnc_loop,cnc_loop in *. destructH.
  assert (deq_loop h q) as Hhq.
  {
    intros h0 Hh0.
    eapply Hdeq in Hh0 as Hh0p.
    eapply loop_contains_either in Hh0p as Heith. 2:eapply Hocnc2. destruct Heith;[exfalso|eauto].
    eapply Hocnc3. eapply loop_contains_deq_loop. eapply loop_contains_trans;eauto.
  }
  assert (S (depth q) <= depth h) as Hqs.
  {
    assert (~ depth h <= depth q) as Q.
    {
      contradict Hocnc3.
      eapply deq_loop_depth_leq;eauto.
    }
    lia.
  }
  eapply Nat.le_antisymm;[|eauto].
  eapply loop_contains_deq_loop in Hocnc2 as Hqp.
  eapply deq_loop_depth in Hqp. setoid_rewrite <-Hqs in Hqp.
  eapply ex_depth_head' in Hqp as Hhead. destructH.
  specialize (Hocnc1 h0).
  exploit Hocnc1.
  - split;eauto.
    intro N.
    eapply deq_loop_depth in N. lia.
  - eapply deq_loop_depth in Hocnc1. rewrite <-Hhead1. eauto.
Qed.
