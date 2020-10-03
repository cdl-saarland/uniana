Require Export CFGinnermost.

(** cnc & ocnc **)

Definition cnc_loop `{C : redCFG} h p q
  := loop_contains h p /\ ~ deq_loop q h.

Definition ocnc_loop `{C : redCFG} h p q
  := cnc_loop h p q /\ forall h', loop_contains h' p -> deq_loop h' h.

(*
(* the ocnc loop has an exit such that q is deeper or equal to the exit *)
Lemma ocnc_loop_exit `(C : redCFG) s q s'
      (Hocnc : ocnc_loop s q s')
  : exists e : Lab, exited s' e /\ deq_loop q e.
Admitted.
 *)

Lemma ex_ocnc_loop `(C : redCFG) p q
      (Hndeq : ~ deq_loop q p)
  : exists h, ocnc_loop h p q .
Admitted.

Lemma ocnc_depth `(C : redCFG) h p q
      (Hocnc : ocnc_loop h p q)
  : depth h = S (depth q).
Admitted.
