Require Export HeadRewire Tagged Disjoint.

Section splits.

  Context `{C : redCFG}.

  Parameter splits : Lab -> list Lab.
  Parameter splits_spec
    : forall p sp, sp ∈ splits p <->
              exists (π ϕ : list Lab) (u u' : Lab),
                HPath u p π
                /\ HPath u' p ϕ
                /\ Disjoint (tl π) (tl ϕ)
                /\ edge__P sp u
                /\ edge__P sp u'
                /\ (tl π <> nil \/ tl ϕ <> nil).

End splits.
