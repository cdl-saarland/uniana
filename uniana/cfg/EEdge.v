Require Export CFGinnermost.
Require Import PropExtensionality Lia.

(** * Kinds of edges in a redCFG **)

Section cfg.
  Context `{C : redCFG}.

  Infix "-->" := edge__P.

  Inductive Edge (p q : Lab) : Type :=
  | Enormal : basic_edge p q -> Edge p q
  | Eback : back_edge p q -> Edge p q
  | Eentry : entry_edge p q -> Edge p q
  | Eexit : eexit_edge p q -> Edge p q.

  Lemma Edge_disj (p q : Lab) (H Q : Edge p q)
    : H = Q.
  Proof.
    destruct H,Q.
    all: match goal with
         | |- ?x _ = ?x _ => f_equal;eapply proof_irrelevance
         | |- _ => exfalso
         end.
    all: unfold back_edge,entry_edge, eexit_edge, exit_edge, basic_edge in *.
    all: unfold_edge_op' b; unfold_edge_op' b0; repeat destructH;
      try contradiction.
    7,10:eapply no_exit_head;unfold exit_edge;eauto.
    4,8:exfalso;eapply no_exit_head;eexists;eauto; unfold back_edge; unfold_edge_op; eauto.
    all: lazymatch goal with
         | H : ~ loop_contains ?q ?p,
               Q : eq_loop ?p ?q |- _ => eapply H; rewrite Q; eapply loop_contains_self;eauto
         | H : eq_loop ?p ?q,
               Q : ~ loop_contains _ ?q |- _ => rewrite <-H in Q; contradiction
         | _ : loop_head ?q,
               H : ~ loop_contains ?q ?p,
                   _ : ~ a_edge__P ?p ?q |- _
           => eapply H; specialize (back_edge_eq_loop (p:=p) (h:=q)) as Q;
               exploit Q;[firstorder|rewrite Q;eapply loop_contains_self;eauto]
         | _ => idtac
         end.
  Qed.

  Lemma edge_Edge : forall (p q : Lab), edge__P p q -> Edge p q.
  Proof.
    intros ? ? Hedge.
    decide (deq_loop p q).
    - decide (deq_loop q p).
      + decide (a_edge__P p q).
        * econstructor;eauto;split;eauto;split;eauto.
        * eapply Eback. refine (conj Hedge n).
      + eapply Eexit.
        simpl_dec' n. simpl_dec' n. destructH.
        exists x. split;eauto.
    - eapply Eentry.
      unfold entry_edge. split_conj;eauto.
      + simpl_dec' n. simpl_dec' n. destructH.
        enough (x = q).
        * subst. eapply loop_contains_loop_head;eauto.
        * eapply dom_loop_contains in n1 as Hdom;eauto.
          specialize (PathSingle edge__P p) as Hpath.
          eapply PathCons in Hedge;eauto.
          eapply Hdom in Hedge. destruct Hedge;subst;auto.
          exfalso. cbn in H; destruct H;[|auto]. subst.
          eapply n1. eapply loop_contains_self;eapply loop_contains_loop_head;eauto.
      + contradict n. eapply loop_contains_deq_loop;auto.
  Defined.

  Lemma Edge_eq (p q : Lab)
        (H : edge__P p q)
        (Q : edge__P p q)
    : edge_Edge H = edge_Edge Q.
  Proof.
    erewrite Edge_disj. reflexivity.
  Qed.


  Lemma basic_edge_loop_contains a b x
        (Hedge : basic_edge a b)
        (Hinner : loop_contains x a)
    : loop_contains x b.
  Proof.
    specialize (loop_contains_loop_head Hinner) as Hhead.
    destruct Hedge as [Hedge _].
    eauto using loop_contains_deq_loop, deq_loop_head_loop_contains, eq_loop1.
  Qed.

  Lemma enter_exit_same e h b c
        (Hentry : entry_edge e h)
        (Hexit: exit_edge h b c)
    : eq_loop c e.
  Proof.
    enough (forall h, loop_contains h e <-> loop_contains h c).
    - unfold eq_loop, deq_loop.
      firstorder 0.
    - intros h'. split; intros.
      + eapply exit_edge_in_loop; try eassumption.
        * eapply deq_loop_entry in Hentry. unfold deq_loop in Hentry. eauto.
        * intro. subst. eapply Hentry. assumption.
      + specialize (deq_loop_exited' Hexit) as Hdeq. unfold deq_loop in Hdeq.
        edestruct (deq_loop_entry_or Hentry); eauto.
        subst. unfold exit_edge in Hexit.
        exfalso. destruct Hexit as [_ [Hexit _]]. contradiction.
  Qed.

  Lemma not_deq_edge_is_exit a b h
        (Edge : a --> b)
        (Hinner : innermost_loop h a)
        (Hndeq : ~ deq_loop b a)
    : exit_edge h a b.
  Proof.
    eapply edge_Edge in Edge.
    inv Edge.
    - exfalso. destruct H as [H _]. eapply Hndeq. eapply eq_loop1. eapply H. reflexivity.
    - exfalso. eapply back_edge_eq_loop in H. eapply Hndeq. eapply eq_loop1. eapply H. reflexivity.
    - exfalso. eapply deq_loop_entry in H. contradiction.
    - destruct H as [h' Hexit].
      enough (h = h').
      + subst h'. eassumption.
      + eauto using exit_edge_innermost, innermost_unique.
  Qed.

  Lemma ncont_cont_is_entry_edge h a b
        (Hcont : loop_contains h b)
        (Hncont : ~ loop_contains h a)
        (Hedge : a --> b)
    : entry_edge a b /\ b = h.
  Proof.
    eapply edge_Edge in Hedge.
    inv Hedge.
    - destruct H as [H _]. rewrite H in Hncont. contradiction.
    - eapply back_edge_eq_loop in H. rewrite H in Hncont. contradiction.
    - split; try eassumption. unfold entry_edge in H.
      destruct H as [_ [Hncontba Hedge]].
      eauto using entry_through_header.
    - destruct H as [h' Hexit].
      eapply deq_loop_exited in Hexit.
      exfalso. unfold deq_loop in Hexit. eauto.
  Qed.

End cfg.

Ltac edge_excl
  := let He := fresh "Hexcleexit" in
     match goal with
     | H : exit_edge ?h ?p ?q |- _
       => assert (eexit_edge p q) as He;
         [eexists;eauto|]
     | _ => idtac
     end;
     match goal with
     | H : basic_edge ?p ?q |- _
       => let tac
             := eapply depth_basic in H
           in
             lazymatch goal with
             | Q : entry_edge p q |- _
               => eapply depth_entry in Q;tac;lia
             | Q : eexit_edge p q |- _
               => eapply depth_exit in Q;tac;lia
             | Q : back_edge p q |- _
               => destruct H, Q; firstorder
             end
     | H : entry_edge ?p ?q |- _
       => let tac
             := eapply depth_entry in H
           in
             lazymatch goal with
             | Q : basic_edge p q |- _
               => eapply depth_basic in Q;tac;lia
             | Q : eexit_edge p q |- _
               => eapply depth_exit in Q;tac;lia
             | Q : back_edge p q |- _
               => eapply depth_back in Q;tac;lia
             end
     | H : eexit_edge ?p ?q |- _
       => let tac
             := eapply depth_exit in H
           in
             lazymatch goal with
             | Q : basic_edge p q |- _
               => eapply depth_basic in Q;tac;lia
             | Q : entry_edge p q |- _
               => eapply depth_entry in Q;tac;lia
             | Q : back_edge p q |- _
               => eapply depth_back in Q;tac;lia
             end
     | H : back_edge ?p ?q |- _
       => let tac
             := eapply depth_back in H
           in
             lazymatch goal with
             | Q : basic_edge p q |- _
               => destruct H, Q; firstorder
             | Q : entry_edge p q |- _
               => eapply depth_entry in Q;tac;lia
             | Q : back_edge p q |- _
               => eapply depth_back in Q;tac;lia
             end
     end;
     try clear He.

Lemma entry_edge_acyclic `(C : redCFG) p q
      (Hentry : entry_edge p q)
  : a_edge__P p q.
Proof.
  decide (back_edge p q).
  - edge_excl.
  - simpl_dec' n. simpl_dec' n. unfold entry_edge in Hentry. destruct n;firstorder.
Qed.

Lemma exit_edge_acyclic `(C : redCFG) p q
      (Hexit : eexit_edge p q)
  : a_edge__P p q.
Proof.
  decide (back_edge p q).
  - edge_excl.
  - do 2 simpl_dec' n. destruct Hexit. destruct H. destruct H0. destruct n;firstorder.
Qed.
