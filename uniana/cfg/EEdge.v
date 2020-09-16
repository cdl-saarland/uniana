Require Export CFGinnermost.
Require Import PropExtensionality.

(** * Kinds of edges in a redCFG **)

Section cfg.
Context `{C : redCFG}.

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
(*    all: lazymatch goal with
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
 *)
Admitted.

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
End cfg.
