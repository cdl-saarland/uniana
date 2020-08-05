Require Export CFGinnermost CFGgeneral.

Section hr_cfg.
  Context `{C : redCFG}.

  Definition head_rewired_edge q p : Prop
    := edge__P q p /\ ~ loop_head q \/ exited q p.

  Lemma subgraph_refl {L : Type} [edge1 : L -> L -> Prop]
    : sub_graph edge1 edge1.
  Proof.
    unfold sub_graph. intros; tauto.
  Qed.

  (* the head rewired DAG is not a redCFG (because of unreachability) *)

  Definition HPath := Path head_rewired_edge.

  Lemma acyclic_head_rewired_edge
    : acyclic head_rewired_edge.
  Admitted.

  Lemma acyclic_HPath p q π
        (Hpath : HPath p q π)
    : NoDup π.
  Proof.
  Admitted.

End hr_cfg.
