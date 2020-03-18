Require Export CFGdef.

Open Scope prg.

Ltac to_loop_contains' :=
  match goal with
  | [C : redCFG ?edge ?root ?a_edge |- context [loop_contains ?h ?p]]
    => unfold loop_contains,back_edge;
      fold (loop_contains' edge a_edge h p)
  end.

Instance decide_decPred_bool (A : Type) (f : A -> bool) a : dec (if f a then True else False).
Proof.
  cbn. destruct (f a); eauto.
Qed.

Definition decPred_bool (A : Type) (f : A -> bool) := DecPred (fun a => if f a then True else False).

Definition finType_sub_decPred {X : finType} (p : decPred X) : finType.
Proof.
  eapply (@finType_sub X p). eapply decide_pred. 
Defined.

Ltac fold_lp_cont' :=
  repeat lazymatch goal with
         | [H : context [exists _ _, (?edge ∖ ?a_edge) _ ?h /\ Path ?edge ?q _ _ /\ ?h ∉ tl (rev _) ] |- _]
           => unfold finType_sub_decPred in H;
             fold (loop_contains' edge a_edge h q) in H
         | [H : context [loop_contains' ?edge ?a_edge ?h ?p
                         /\ ~ loop_contains' ?edge ?a_edge ?h ?q /\ ?edge ?p ?q] |- _]
           => fold (exit_edge' edge a_edge h p q) in H
         | [ |- context [loop_contains' ?edge ?a_edge ?h ?p
                        /\ ~ loop_contains' ?edge ?a_edge ?h ?q
                        /\ ?edge ?p ?q]]
           => fold (exit_edge' edge a_edge h p q)
         | |- context [exists _ _, (?edge ∖ ?a_edge) _ ?h /\ Path ?edge ?q _ _ /\ ?h ∉ tl (rev _)]
           => unfold finType_sub_decPred;
             fold (loop_contains' edge a_edge h q)
         end.

Ltac unfold_edge_op := repeat unfold intersection_edge,restrict_edge',minus_edge,union_edge; conv_bool.
Ltac unfold_edge_op' H := repeat (unfold intersection_edge,restrict_edge',minus_edge,union_edge in H);
                          conv_bool.

