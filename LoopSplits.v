Require Import Coq.Classes.EquivDec.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.Decidable.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Utils.
Require Import Lists.ListSet.
Require Import List.
Require Import Nat.

Require Util Graph Evaluation Unchanged Disjoint.

Module LoopSplits.
  Import Util Evaluation.Evaluation Disjoint.Disjoint.

  Lemma lc_loop_split p p0 p0' i0 i0' q1 q2 j1 j2 br' i i' l1 l2 l1' l2' :
    l1' = nlcons (q1,j1) l1
    -> l2' = nlcons (q2,j2) l2
    -> TPath (p0,i0) (p,i) ((p,i) :<: l1')
    -> TPath (p0',i0') (p,i) ((p,i) :<: l2')
    -> q1 =/= q2
    -> i =/= i'
    -> last_common l1' l2' (br',i')
    -> exists x', In (br',x') (loop_splits p).
  Admitted.
  
End LoopSplits.
