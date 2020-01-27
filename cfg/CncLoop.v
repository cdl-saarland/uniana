Require Export CFGinnermost.

(** cnc & ocnc **)

Definition cnc_loop `{C : redCFG} s q s'
  := loop_contains s' s /\ ~ deq_loop q s'.

Definition ocnc_loop `{C : redCFG} s q s'
  := cnc_loop s q s' /\ forall x, cnc_loop s q s' -> deq_loop x s'.

(* the ocnc loop has an exit such that q is deeper or equal to the exit *)
Lemma ocnc_loop_exit `(C : redCFG) s q s'
      (Hocnc : ocnc_loop s q s')
  : exists e : Lab, exited s' e /\ deq_loop q e.
Admitted.

Lemma ex_ocnc_loop `(C : redCFG) s q
      (Hndeq : ~ deq_loop q s)
      (Hsdeq : deq_loop s q) (* <-- is this assumption really necessary ? *)
  : exists s', ocnc_loop s q s'.
Admitted.
 
