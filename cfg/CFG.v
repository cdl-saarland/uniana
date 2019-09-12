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
