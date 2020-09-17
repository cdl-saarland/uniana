Require Export TcfgLoop.
Require Import Lia.

Section cfg.

  Context `(C : redCFG).

  Notation "pi -t> qj" := (tcfg_edge pi qj) (at level 50).
  Fixpoint zero_tag n
    := match n with
       | 0 => nil
       | S n => 0 :: zero_tag n
       end.

  Lemma tcfg_zero_reach q
    : exists t, TPath (root,start_tag) (q,zero_tag (depth q)) t.
  Proof.
    specialize (a_reachability q) as Hreach.
    destructH.
    revert q Hreach.
    induction π; intros.
    - inv Hreach.
    - destruct π.
      + path_simpl' Hreach.
        rewrite depth_root. cbn.
        eexists;econstructor;eauto.
      + inv_path Hreach.
        eapply a_edge_incl in H0 as H0'.
        specialize (IHπ e).
        exploit IHπ.
        destructH.
        exists ((q, zero_tag (depth q)) :: t).
        destruct (edge_Edge H0');econstructor;eauto.
        * copy b b'.
          destruct b'. rewrite H1 at 2.
          eapply tcfg_basic_edge;eauto.
        * exfalso. destruct b. contradiction.
        * copy e0 e0'.
          eapply depth_entry in e0. rewrite <- e0.
          replace (zero_tag (S (depth e))) with (0 :: zero_tag (depth e)) by (cbn;auto).
          eapply tcfg_entry_edge;eauto.
        * copy e0 e1.
          eapply depth_exit in e0.
          rewrite e0.
          replace (zero_tag (S (depth q))) with (0 :: zero_tag (depth q)) by (cbn;auto).
          eapply tcfg_exit_edge;eauto.
  Qed.

  (* this is true but way more complicate than what I need
  Lemma tcfg_reach_iter q i j
        (Hlen : | i | = depth q)
        (Htagle : i ⊴ j)
    : exists t, TPath (q,i) (q,j) t.
   *)

  Lemma tcfg_zero_iter q j
        (Hlen : | j | = depth q)
    : exists t, TPath (q, zero_tag (depth q)) (q,j) t.
  Proof.
    revert dependent q.
    induction j;intros.
    - cbn in Hlen.
      rewrite <-Hlen. cbn. eexists;econstructor.
    - cbn in Hlen.
      induction a.
      +
  Admitted.

  Lemma depth_zero_iff q
    : depth q = 0 <-> forall h, loop_contains h q -> False.
  Admitted.

  Lemma loop_head_acyclic_entry p h
        (Hloop : loop_head h)
        (Hedge : a_edge__P p h)
    : entry_edge p h.
  Proof.
    copy Hedge Hedge'.
    eapply a_edge_incl in Hedge.
    destruct (edge_Edge Hedge).
    all:auto;exfalso.
    - eapply basic_edge_no_loop2;eauto.
    - destruct b. contradiction.
    - destruct e. eapply no_exit_head;eauto.
  Qed.

  Lemma member_reachs_innermost_latch_acyclic h q
        (Hloop : loop_contains h q)
    : exists p, p ↪ h /\ q -a>* p.
  Admitted.

  Lemma tcfg_path_acyclic p q π i
        (Hpath : APath p q π)
        (Heq : eq_loop p q)
        (Hlen : | i | = depth p)
    : exists t, TPath (p,i) (q,i) t.
  Admitted.

  Lemma tcfg_reachability q j
        (Hlen : | j | = depth q)
    : exists t, TPath (root,start_tag) (q,j) t.
  Proof.
    revert dependent q.
    induction j;intros.
    - cbn in Hlen.
      cbn. fold (zero_tag 0). rewrite Hlen.
      eapply tcfg_zero_reach.
    - specialize (get_innermost_loop_spec q) as Hinner.
      destruct (get_innermost_loop q).
      2: { exfalso. eapply depth_zero_iff in Hinner. cbn in Hlen. lia. }
      induction a.
      + specialize (a_reachability e) as Hreach.
        destructH.
        destruct π. 1: inv Hreach.
        destruct π.
        * path_simpl' Hreach. eapply innermost_eq_loop in Hinner. rewrite <-Hinner in Hlen.
          rewrite depth_root in Hlen. cbn in Hlen. lia.
        * inv_path Hreach. specialize (IHj e1).
          eapply loop_head_acyclic_entry in H0 as Hentry;
              [|destruct Hinner;eauto using loop_contains_loop_head].
          exploit IHj.
          {
            eapply depth_entry in Hentry. eapply innermost_eq_loop in Hinner. rewrite <-Hinner in Hlen.
            cbn in Hlen.
            lia.
          }
          destructH. copy Hinner Hinner'.
          destruct Hinner. eapply loop_reachs_member in H1.
          destruct H1.
          eapply tcfg_path_acyclic in H1. 2: eapply innermost_eq_loop;auto.
          2: eapply innermost_eq_loop in Hinner';rewrite Hinner';eassumption.
          destructH.
          exists (t0 ++ t).
          eapply path_app;eauto.
          eapply tcfg_entry_edge;eauto.
      + exploit IHa. destructH.
        copy Hinner Hinner'.
        destruct Hinner'. copy H H'.
        eapply member_reachs_innermost_latch_acyclic in H.
        destructH.
        eapply tcfg_path_acyclic with (i := a :: j) in H2.
        2: { eapply back_edge_eq_loop in H1. rewrite H1. symmetry. eapply innermost_eq_loop;eauto. }
        2: { cbn in Hlen. cbn. eassumption. }
        destructH.
        eapply loop_reachs_member in H'.
        destruct H'.
        eapply tcfg_path_acyclic in H.
        2: { eapply innermost_eq_loop;auto. }
        2: { eapply innermost_eq_loop in Hinner. rewrite Hinner. eassumption. }
        destructH.
        exists (t1 ++ (t0 ++ tl t)).
        eapply path_app;eauto.
        * eapply path_app';eauto.
        * eapply tcfg_back_edge;auto.
  Qed.

  Lemma tag_depth_unroot p q i j t
        (Hpath : TPath (q,j) (p,i) t)
        (Hlen : |j| = depth q)
    : |i| = depth p.
  Proof.
    eapply tcfg_reachability in Hlen.
    destructH.
    eapply path_app' in Hpath;eauto.
    eapply tag_depth';eauto.
  Qed.

End cfg.
