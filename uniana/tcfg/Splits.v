Require Export HeadRewire Tagged Disjoint.

Section splits.

  Context `{C : redCFG}.

  Parameter splits : Lab -> list Lab.
  Parameter splits_spec
    : forall p sp, sp ∈ splits p <->
              exists (π ϕ : list (Lab * Tag)) (u u' : Lab),
                HPath u p (map fst π)
                /\ HPath u' p (map fst ϕ)
                /\ Disjoint (r_tl π) (r_tl ϕ)
                /\ edge__P sp u
                /\ edge__P sp u'
                /\ (r_tl π <> nil \/ r_tl ϕ <> nil).

End splits.
