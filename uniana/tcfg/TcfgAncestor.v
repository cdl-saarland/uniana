Require Import CFGancestor.

Section cfg.
  Context `{C : redCFG}.
  Definition ancestor' a p q := deq_loop p a /\ deq_loop q a.

  Lemma ancestor_ancestor' a p q
    : ancestor a p q -> ancestor' a p q.
    intros. unfold ancestor',ancestor in *. destruct H.
    - destruct H. split;eauto using loop_contains_deq_loop.
    - subst. split;eapply deq_loop_root.
  Qed.


  Global Instance ancestor'_sym : forall a, Symmetric (ancestor' a).
  Proof.
    intros.
    econstructor;unfold ancestor' in *;destructH;eauto.
  Qed.

  Global Instance ancestor'_eq_loop a p
    : Proper (eq_loop ==> Basics.impl) (ancestor' a p).
  Proof.
    econstructor;unfold ancestor' in *;destructH;eauto.
    destruct H. transitivity x;auto.
  Qed.
End cfg.
