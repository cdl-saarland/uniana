Require Import CFGgeneral.
Require Export ImplodeCFG.

Section cfg.
  Context `{C : redCFG}.
  
  Notation "p '-a>b' q" := (a_edge p q) (at level 55).
  Notation "p '-a>' q" := (p -a>b q = true) (at level 55).
  Notation "p '-->b' q" := (edge p q) (at level 55).
  Notation "p '-->' q" := (p -->b q = true) (at level 55, right associativity).
  
  (** loop_CFG: remove everything outside the loop **)

  Lemma loop_contains_ledge_head (* unused *)h h' p
    : loop_contains h p -> p ↪ h' -> loop_contains h h'.
  Proof.
  Admitted.
  
    
(*  Lemma restrict_edge_intersection_ex (* unused *)(A : finType) (f : A -> A -> bool) (p : decPred A) x y
  : (f ∩ (fun a _ => if decision (p a) then true else false) ∩ (fun _ b => to_bool (decision (p b)))) x y = true
    -> exists x' y', restrict_edge f (p:=p) x' y' = true /\ (`x') = x /\ (`y') = y.
    cbn.
  Admitted.*)

(*  Lemma loop_edge_h_invariant (h : Lab) (H : loop_head h) : loop_nodes h h.
  Proof.
    unfold loop_nodes. cbn. now eapply loop_contains_self. 
  Qed.*)

End cfg.





Definition top_level (* unused *)`{redCFG} q := forall h, loop_contains h q -> (h = root \/ h = q).


Arguments exit_edge {_ _ _ _ _}.

(** implode CFG **)
(* assuming no exit-to-heads *)


Definition if_transfm (* unused *): forall (X Y : Type) (A B : Prop) (b : {A} + {B}), (if b then X -> X -> bool else Y -> Y -> bool)
                             -> (if b then X else Y)
                             -> (if b then X else Y)
                             -> bool.
  intros. destruct b. all: exact (X0 X1 X2).
Defined.

Arguments head_exits_CFG {_ _ _ _} _.
Arguments implode_CFG {_ _ _ _} _.

Definition local_impl_CFG `(C : redCFG) (h : Lab)
  := implode_CFG (head_exits_CFG C h) h (head_exits_property_satisfied (C:=C) (qh:=h)).

Arguments redCFG : clear implicits.
Arguments implode_nodes {_ _ _ _} _.
Definition local_impl_CFG_type `(C : redCFG) (h : Lab)
  := (finType_sub_decPred (implode_nodes (head_exits_CFG C h) h)).
Arguments redCFG : default implicits.
Arguments implode_nodes : default implicits.

Definition impl_of_original (* unused *)`(C : redCFG) (h : Lab)
  : Lab -> option (local_impl_CFG_type C h).
Proof.
  intro p.
  decide (implode_nodes (head_exits_CFG C h) h p).
  - apply Some. econstructor. eapply purify;eauto.
  - exact None.
Defined.


Arguments loop_contains {_ _ _ _} _.

Lemma head_exits_loop_contains_iff `(C : redCFG) (h p q : Lab)
  : loop_contains C h q <-> loop_contains (head_exits_CFG C p) h q.
Proof.
  setoid_rewrite <-loop_contains'_basic at 2.
  eapply head_exits_loop_equivalence.
Qed.          

Lemma head_exits_deq_loop_inv1 `(C : redCFG) (h p q : Lab)
  : deq_loop (C:=C) p q -> deq_loop (C:=head_exits_CFG C h) p q.
Proof.
  intros.
  unfold deq_loop in *.
  setoid_rewrite <-head_exits_loop_contains_iff.
  eauto.
Qed.

Lemma head_exits_deq_loop_inv2 `(C : redCFG) (h p q : Lab)
  : deq_loop (C:=head_exits_CFG C h) p q -> deq_loop (C:=C) p q.
Proof.
  unfold deq_loop.
  setoid_rewrite <-head_exits_loop_contains_iff.
  eauto.
Qed.

Lemma head_exits_exited_inv1 `(C : redCFG) (qh h p : Lab)
  : exited (C:=C) h p -> exited (C:=head_exits_CFG C qh) h p.
Proof.
  unfold exited, exit_edge.
  setoid_rewrite <-head_exits_loop_contains_iff.
  intros. destructH.
  exists p0. split_conj;eauto.
  eapply union_subgraph1;auto.
Qed.

Lemma head_exits_exited_inv2 `(C : redCFG) (qh h p : Lab)
  : exited (C:=head_exits_CFG C qh) h p -> exited (C:=C) h p.
Proof.
  unfold exited, exit_edge.
  setoid_rewrite <-head_exits_loop_contains_iff.
  intros. destructH.
  unfold_edge_op' H3. destruct H3.
  - exists p0. split_conj;eauto.
  - eapply head_exits_edge_spec in H. destructH. exists p1.
    replace p0 with h in *.
    + unfold exit_edge in H. destructH. split_conj; eauto.
    + eapply exit_edge_unique_diff_head;eauto.
Qed.

Arguments loop_contains {_ _ _ _ _}.

Lemma head_exits_implode_nodes_inv1 `(C : redCFG) (h p : Lab)
  : implode_nodes C h p -> implode_nodes (head_exits_CFG C h) h p.
Proof.
  intro Himpl.
  cbn in Himpl. destruct Himpl.
  - left. eapply head_exits_deq_loop_inv1. eauto.
  - right. destructH. exists e. split; eauto using head_exits_exited_inv1, head_exits_deq_loop_inv1.
Qed.      

Definition impl_of_original' `(C : redCFG) (h p : Lab) (H : implode_nodes C h p)
  : local_impl_CFG_type C h.
Proof.
  econstructor. eapply purify;eauto.
  eapply head_exits_implode_nodes_inv1;eauto.
Defined.

Arguments local_impl_CFG {_ _ _ _} _.

Lemma Lab_dec' `{redCFG} : forall (l l' : Lab), { l = l' } + { l <> l'}.
Proof.
  apply Lab_dec.
Qed.