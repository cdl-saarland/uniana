Require Export Splits SplitsT.

Section splits_complete.

  Context `{C : redCFG}.

  Theorem splits_complete p
    : splits p ⊆ splitsT p.
  Admitted.

End splits_complete.
