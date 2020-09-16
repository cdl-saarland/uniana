Require Export SplitsT.

Parameter rel_splits : forall `{redCFG}, Lab -> Lab -> list Lab.

Parameter rel_splits_spec
  : forall `{redCFG} p u s, s ∈ rel_splits p u <->
                       exists h e, e -a>* p /\ loop_contains h u /\ exited h e /\ s ∈ splitsT e.
