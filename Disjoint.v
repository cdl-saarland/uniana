Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Utils.
Require Import Coq.Logic.Classical.
Require Import List.
Require Import Nat.
Require Import Bool.Bool.
Require Import Coq.Logic.Eqdep_dec.

Require Evaluation Util.

Module Disjoint.
  Import Evaluation.Evaluation Util.

  Parameter branch: Lab -> list Var.

  Definition is_branch br x := x ∈ branch br.

  Parameter val_true : Val -> bool.

  Parameter branch_spec :
    forall b, exists (d : list Val -> Lab), forall s, match (eff' (b, s)) with
                                      | Some (q,_) => q = d (map s (branch b))
                                      | None => True
                                      end.
  
  Definition DisjointBranch `{redCFG} (s : Lab) (xl : list Var) (qt qf : Lab) (π ϕ : list Lab) :=
    CPath s qt (π >: s) /\ CPath s qf (ϕ >: s) /\ branch s =' xl /\ Disjoint π ϕ.

  Parameter path_splits : forall `{redCFG}, Lab -> list (Lab * Lab * Lab * list Var).

  Parameter loop_splits : forall `{redCFG}, Lab -> Lab -> list (Lab * Lab * Lab * list Var).

  Definition pl_split `{redCFG} (qh qe q1 q2 br : Lab) (xl : list Var) :=
      (exists π ϕ, CPath br qh (π >: q1 :>: br)
              /\ CPath br qe (ϕ >: q2 :>: br)
              /\ Disjoint (tl π :r: q1) (tl ϕ :r: q2)
              /\ branch br =' xl).

  Parameter path_splits_spec : forall `{redCFG} p q1 q2 br xl,
      pl_split p p q1 q2 br xl <->
      (br, q1, q2, xl) ∈ path_splits p.
  
  Parameter loop_splits_spec : forall `{redCFG} qh qe q1 q2 br xl,
      loop_contains qh br /\ (* otherwise some splits would be considered as loop splits *)
      pl_split qh qe q1 q2 br xl <->
      (br, q1, q2, xl) ∈ loop_splits qh qe.  

  Parameter splits' : forall `{redCFG}, Lab -> Lab -> list (Lab * Lab * Lab * list Var).
  Parameter splits  : forall `{redCFG}, Lab -> list (Lab * Lab * Lab * list Var).

  Definition path_splits__imp `{C : redCFG} := @path_splits _ _ _ (implode_CFG C).
  Definition loop_splits__imp `{C : redCFG} := @loop_splits _ _ _ (implode_CFG C).

  Definition splits'_spec `{redCFG} := forall h e sp, sp ∈ splits' h e
                                                 <-> sp ∈ loop_splits__imp h e
                                                   \/ exists br q q' xl, (br,q,q',xl) ∈ loop_splits__imp h e
                                                                   /\ (sp ∈ splits' br q
                                                                      \/ sp ∈ splits' br q').

  Definition splits_spec `{redCFG} := forall p sp, sp ∈ splits p
                                              <-> sp ∈ path_splits__imp p
                                                \/ exists br q q' xl, (br,q,q',xl) ∈ path_splits__imp p
                                                                /\ (sp ∈ splits' br q
                                                                   \/ sp ∈ splits' br q').

  Lemma lc_join_split `{redCFG} t1 t2 (p q1 q2 s qq qq' : Lab) (i j1 j2 k : Tag) xl
        (Hlc : last_common t1 t2 (s,k))
        (Hneq : q1 <> q2 \/ j1 <> j2)
        (Hpath1 : TPath' ((p,i) :<: (q1,j1) :< t1))
        (Hpath2 : TPath' ((p,i) :<: (q2,j2) :< t2))
    : (s,qq,qq',xl) ∈ splits p.
  Admitted.
  
End Disjoint.