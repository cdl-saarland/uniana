Require Export DisjDef.


Arguments loop_head {_ _ _ _} _.
Arguments loop_head_dec {_ _ _ _} _.
Arguments get_innermost_loop_strict {_ _ _ _} _.

Local Arguments deq_loop {_ _ _ _} _.
Local Arguments depth {_ _ _ _} _.
Local Arguments exited {_ _ _ _} _.

Definition thrice (A B : Type) (f : A -> B) (xyz : A*A*A) : B*B*B
  := match xyz with (x,y,z) => (f x, f y, f z) end.
    

Program Definition path_splits__imp' `{C : redCFG} (p : Lab)
  := let D := (local_impl_CFG C (get_innermost_loop' p)) in
     (@path_splits _ _ _ _ D _).
Next Obligation.
  eapply implode_CFG_elem.
  left. eapply head_exits_deq_loop_inv1. 
  eapply deq_loop_innermost'. 
Defined.

Arguments exited {_ _ _ _ _} _.

Definition path_splits__imp `{C : redCFG} (p : Lab)
  := map (thrice (@proj1_sig Lab _)) (path_splits__imp' p).

Lemma exited_head `{C : redCFG} (h e : Lab)
      (H : exited h e)
  : loop_head C h.
Proof.
  unfold exited in H. destructH. unfold exit_edge in H. destructH. eapply loop_contains_loop_head;eauto.
Qed.

Program Definition loop_splits__imp' `{C : redCFG} (h e : Lab)
  := match decision (exited h e) with
     | left H => (@loop_splits _ _ _ _ (local_impl_CFG C h) _ _)
     | _ => nil
     end.
Next Obligation.
  eapply implode_CFG_elem.
  left. eapply head_exits_deq_loop_inv1.
  eapply deq_loop_refl.
Defined.
Next Obligation.
  eapply implode_CFG_elem.
  left. eapply head_exits_deq_loop_inv1.
  unfold exited in H. destructH.
  eapply deq_loop_exited';eauto.
Defined.


Definition loop_splits__imp `{C : redCFG} (h e : Lab)
  := let d := match decision (loop_head C h) with
              | left H => Some (exist _ h H)
              | right _ => None
              end in
     map (thrice (@proj1_sig Lab _)) (loop_splits__imp' h e).

Lemma splits'_loop_splits__imp `(C : redCFG) (h' : Lab) (h e s' qq qq' : local_impl_CFG_type C h')
      (Heq :  eq_loop (`h) h')
      (Hsp : (s', qq, qq') ∈ @loop_splits _ _ _ _ (local_impl_CFG C h') h e)
  : (` s', ` qq, ` qq') ∈ loop_splits__imp (`h) (`e).
Proof.
  unfold loop_splits__imp.
  eapply in_map_iff.
  (* FIXME *)
Admitted.

Parameter splits'_spec
  : forall `{redCFG} h e sp, sp ∈ splits' h e
                        <-> sp ∈ loop_splits h e
                          \/ exists br q q', (br,q,q') ∈ loop_splits__imp h e
                                       /\ (sp ∈ splits' br q
                                          \/ sp ∈ splits' br q').

Parameter rel_splits_spec 
  : forall `{redCFG} p q sp, sp ∈ rel_splits p q
                        <-> exists h e, e -a>* p (* acyclic, bc. otw. path could use back_edge of outer loop *)
                                 /\ loop_contains h q
                                 /\ sp ∈ splits' h e.
(* sp ∈ loop_splits h e. <--- deprecated,
   because: assume h_q is the innermost loop of q and h the next loop strictly containing h_q.
   now if h_q & q dominate the only exit of h and if there is a loop h' with q ∉ h' 
   which is has loop split and has one exit towards h_q and another to a latch of h, 
   then this is a glsplit of h and q can be reached with different tags because of that.
 *)

Parameter splits_spec
  : forall `{redCFG} p sp, sp ∈ splits p
                      <-> sp ∈ path_splits p (* usual split *)
                        \/ (exists h, (* lsplits of exited loops: *)
                              sp ∈ splits' h p)
                        \/ exists br q q',(br,q,q') ∈ path_splits__imp p
                                    (* loop_split of splitting heads *)
                                    /\ (sp ∈ splits' br q
                                       \/ sp ∈ splits' br q').

Arguments loop_splits : default implicits.

Lemma splits'_sym `(C : redCFG) (s h e q q' : Lab)
              (Hsp : (s,q,q') ∈ splits' h e)
  : (s,q',q) ∈ splits' h e.
Admitted.


Lemma splits_path_splits__imp `(C : redCFG) (p' : Lab) (p s' qq qq' : local_impl_CFG_type C p')
      (Heq : deq_loop C (`p) p')
      (Hsp : (s', qq, qq') ∈ @path_splits _ _ _ _ (local_impl_CFG C p') p)
  : (`s', `qq, `qq') ∈ path_splits__imp (`p).
Admitted.
