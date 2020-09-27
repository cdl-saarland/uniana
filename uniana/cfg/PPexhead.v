Require Export CFGinnermost.

Section cfg.
  Context `(C : redCFG).
  (** ** p p ex head **)

  Lemma p_p_ex_head' (p q : Lab) π ϕ
        (Hpath : CPath p q π)
        (Hdeq : forall x, x ∈ π -> deq_loop p x)
        (Hacy : APath q p ϕ)
        (Hlen : | π | >= 2)
  : exists h, h ∈ π /\ forall x, x ∈ π -> loop_contains h x.
  Proof.
  (* by induction on π:
   * * if nil,singleton: contradiction
   * * if doubleton: easy style: h=q, bc of APath p-->q must be a back_edge, thus loop_contains q p
   * * else:
   * * edge distinction for ? --> q:
   *   * if back_edge then: we have found h
   *   * otw. IH
   *)
  Admitted.

  Lemma p_p_ex_head (p : Lab) π
        (Hpath : CPath p p π)
        (Hlen : | π | >= 2)
    : exists h, h ∈ π /\ forall x, x ∈ π -> loop_contains h x.
  Proof.
    (* implode π wrt. p then Hdeq of p_p_ex_head' holds and the conclusion is extendable from there *)
    eapply p_p_ex_head';eauto.
    - admit.
    - econstructor.
  Admitted.

End cfg.
