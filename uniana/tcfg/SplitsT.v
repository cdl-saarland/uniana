Require Export Tagged Disjoint.


Parameter splitsT : forall `{redCFG}, Lab -> list Lab.

Definition inner (A : Type) (l : list A) := tl (rev (tl (rev l))).

Parameter splitsT_spec
  : forall `{C : redCFG} p sp, sp ∈ splitsT p <->
                          exists (π ϕ : list (Lab * Tag)) (u1 u2 : Lab) (k i l1 l2: Tag),
                            TPath (u1,l1) (p,i) π
                            /\ TPath (u2,l2) (p,i) ϕ
                            /\ Disjoint (tl π) (tl ϕ)
                            /\ tcfg_edge (sp,k) (u1,l1)
                            /\ tcfg_edge (sp,k) (u2,l2)
                            /\ (tl π <> nil \/ tl ϕ <> nil).
