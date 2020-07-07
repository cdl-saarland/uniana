Require Export Tagged Disjoint.


Parameter splitsT : forall `{redCFG}, Lab -> list Lab.

Definition inner (A : Type) (l : list A) := tl (rev (tl (rev l))).

Parameter splitsT_spec
  : forall `{C : redCFG} p sp, sp ∈ splitsT p <->
                          exists (π ϕ : list (Lab * Tag)) (k i : Tag),
                            TPath (sp,k) (p,i) π
                            /\ TPath (sp,k) (p,i) ϕ
                            /\ Disjoint (inner π) (inner ϕ)
                            /\ (inner π <> nil \/ inner ϕ <> nil).
