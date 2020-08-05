Require Export Splits SplitsT.

Section splits_sound.

  Context `{C : redCFG}.

  Theorem splits_sound p
    : splitsT p ⊆ splits p.
  Admitted.

End splits_sound.
