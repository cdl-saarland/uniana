Require Export CFGloopcutting.
Require Import Lia.

Section cfg.
  Context `(C : redCFG).
  (** ** p p ex head **)

  Lemma loop_contains_all_ex_pre p q π ϕ
        (Hpath : CPath p q ϕ)
        (Hpre : Prefix ϕ π)
        (Hae : forall x, x ∈ π -> exists h, h ∈ π /\ loop_contains h x)
    : exists h, h ∈ π /\ forall x, x ∈ ϕ -> loop_contains h x.
  Proof.
    induction Hpath.
    - specialize (Hae a). exploit Hae. 1:eapply prefix_incl;eauto.
      destructH. exists h. split;eauto. intros. destruct H;[subst|contradiction]. eauto.
    - exploit IHHpath.
      + eapply prefix_cons;eauto.
      + destructH.
        specialize (IHHpath1 b) as Hb. exploit Hb. 1: eapply path_contains_front;eauto.
        destruct (edge_Edge H).
        * exists h. split;eauto. intros. destruct H0;eauto. subst.
          eapply basic_edge_eq_loop in b0. rewrite <-b0. eauto.
        * exists h. split;eauto. intros. destruct H0;eauto. subst.
          eapply back_edge_eq_loop in b0. rewrite <-b0. eauto.
        * exists h. split;eauto. intros. destruct H0;eauto. subst.
          eapply deq_loop_entry;eauto.
        * destruct e. eapply deq_loop_exited in H0.
          specialize (Hae c). exploit Hae.
          -- eapply prefix_incl;eauto.
          -- destructH. eapply loop_contains_either in Hb. 2: eapply H0;eauto.
             destruct Hb.
             ++ exists h0. split;eauto. intros.
                destruct H2;eauto.
                ** subst. eauto.
                ** eapply loop_contains_trans;eauto.
             ++ exists h. split;eauto. intros. destruct H2.
                ** subst. eapply loop_contains_trans;eauto.
                ** eauto.
  Qed.


  Lemma loop_contains_all_ex p q π
        (Hpath : CPath p q π)
        (Hae : forall x, x ∈ π -> exists h, h ∈ π /\ loop_contains h x)
    : exists h, h ∈ π /\ forall x, x ∈ π -> loop_contains h x.
  Proof.
    eapply loop_contains_all_ex_pre;eauto.
    econstructor.
  Qed.

  Lemma p_p_ex_head (p : Lab) π
        (Hpath : CPath p p π)
        (Hlen : | π | >= 2)
    : exists h, h ∈ π /\ forall x, x ∈ π -> loop_contains h x.
  Proof.
    eapply loop_contains_all_ex;eauto.
    decide (exists x, x ∈ π /\ forall h, h ∈ π -> ~ loop_contains h x).
    - exfalso.
      destructH.
      eapply rotate_find in Hpath;eauto. destructH.
      inv_path Hpath0.
      + cbn in Hpath3. lia.
      + destruct Hpath2.
        eapply loop_cutting in H;eauto.
        * destructH.
          eapply a_edge_acyclic;eauto.
          destruct (edge_Edge H0).
          -- destruct b. eauto.
          -- exfalso. eapply e1;eauto. eapply loop_contains_self. eexists;eauto.
          -- eapply entry_edge_acyclic;eauto.
          -- eapply exit_edge_acyclic;eauto.
        * intros. intro N. eapply e1. 2:eapply H3. eapply H2. right. eauto.
    - do 3 simpl_dec' n. intros.
      specialize (n x).
      destruct n;[contradiction|].
      destructH.
      exists x0.
      eapply dec_DM_impl in H0;eauto.
      destructH. split;eauto. eapply dec_DN;eauto.
  Qed.

End cfg.
