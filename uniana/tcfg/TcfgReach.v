Require Export TcfgLoop CFGloopcutting.
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

  Lemma tcfg_path_acyclic_deq p q π i j
        (Hpath : APath p q π)
        (Hdeq : deq_loop q p)
        (Hlenp : | i | = depth p)
        (Hj : j = zero_tag (depth q - depth p) ++ i)
    : exists t, TPath (p,i) (q,j) t.
  Proof.
    revert q j Hpath Hj Hdeq.
    induction π;intros;[|destruct π];inv_path Hpath.
      - replace (depth a - depth a) with 0 by lia. cbn.
        eexists;econstructor.
      - eapply a_edge_incl in H0 as Hedge.
        remember (zero_tag (depth e - depth p) ++ i) as j.
        specialize (IHπ e j).
        do 2 exploit' IHπ.
        destruct (edge_Edge Hedge).
        + copy b b'.
          destruct b.
          exploit IHπ.
          * eapply eq_loop1;eauto. symmetry;eauto.
          * destructH. exists ((a,j) :: t). rewrite H1 in Heqj. subst j. econstructor;eauto.
            eapply tcfg_basic_edge;eauto.
        + exfalso.
          destruct b. contradiction.
        + decide (deq_loop p a).
          * exfalso.
            assert (loop_contains a p) as Hloop.
            { eapply deq_loop_head_loop_contains;eauto. destruct e0. auto. }
            eapply loop_reachs_member in Hloop. destruct Hloop as [π' Hloop].
            eapply path_app' in H;eauto. cbn in H.
            eapply a_edge_acyclic;eauto.
          * exploit IHπ.
            -- intros h Hh. eapply deq_loop_entry_or in e0.
               ++ destruct e0;[eauto|]. subst a. exfalso. eapply loop_contains_deq_loop in Hh. contradiction.
               ++ eapply Hdeq;eauto.
            -- eapply depth_entry in e0 as Hdep. rewrite <-Hdep.
               assert (depth p < depth a) as Hlt.
               {
                 copy Hdeq Hdeq'.
                 eapply deq_loop_depth in Hdeq. eapply le_lt_or_eq in Hdeq. destruct Hdeq;[auto|].
                 exfalso. eapply n. eapply deq_loop_depth_leq;auto. rewrite H1. reflexivity.
               }
               replace (S (depth e) - depth p) with (S (depth e - depth p)) by lia.
               cbn.
               destructH.
               exists ((a,0 :: j) :: t).
               subst j. econstructor;eauto.
               eapply tcfg_entry_edge;eauto.
        + exploit IHπ.
          { destruct e0. transitivity a;eauto. eapply deq_loop_exited;eauto. }
          eapply depth_exit in e0 as Hdep. rewrite Hdep in Heqj.
          rewrite Nat.sub_succ_l in Heqj. 2: eapply deq_loop_depth;assumption.
          cbn in Heqj.
          destructH.
          exists ((a,tl j) :: t).
          subst j. cbn.
          econstructor;eauto.
          eapply tcfg_exit_edge;eauto.
  Qed.

  Lemma tcfg_path_acyclic p q π i
        (Hpath : APath p q π)
        (Heq : eq_loop p q)
        (Hlen : | i | = depth p)
    : exists t, TPath (p,i) (q,i) t.
  Proof.
    eapply tcfg_path_acyclic_deq;eauto.
    - destruct Heq;auto.
    - rewrite Heq. replace (depth q - depth q) with 0 by lia. cbn. reflexivity.
  Qed.

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
        eapply member_reachs_innermost_latch_acyclic in Hinner' as H.
        destruct Hinner'. copy H0 H'.
        destructH.
        eapply tcfg_path_acyclic with (i := a :: j) in H3.
        2: { eapply back_edge_eq_loop in H2. rewrite H2. symmetry. eapply innermost_eq_loop;eauto. }
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

  Lemma tag_depth_unroot2 p q i j t
        (Hpath : TPath (p,i) (q,j) t)
        (Hdep : | j | = depth q)
    : | i | = depth p.
  Proof.
    revert q j Hdep Hpath.
    induction t;intros;inv_path Hpath.
    - assumption.
    - destruct x. specialize (IHt e t0). exploit IHt.
      + eapply tcfg_edge_depth_iff;eauto.
      + assumption.
  Qed.

  Lemma tag_depth_unroot_elem p q i j t x k
        (Hpath : TPath (q,j) (p,i) t)
        (Hlen : |j| = depth q)
        (Hin : (x,k) ∈ t)
    : |k| = depth x.
  Proof.
    eapply path_to_elem in Hin;eauto.
    destructH.
    eapply tag_depth_unroot;eauto.
  Qed.

  Lemma tcfg_enroot p q i j t
        (Hpath : TPath (p,i) (q,j) t)
        (Hlen  : | i | = depth p)
    : exists t', TPath (root,start_tag) (q,j) (t ++ t').
  Proof.
    eapply tcfg_reachability in Hlen.
    destructH.
    eexists.
    eapply path_app';eauto.
  Qed.

End cfg.
