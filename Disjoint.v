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
    forall b, exists (d : list Var -> Lab), forall s, match (eff' (b, s)) with
                                      | Some (q,_) => q = d (branch b)
                                      | None => True
                                      end.

(*  Parameter in_out_spec :
    forall p q q', (exists x, is_branch p x) -> q --> p -> q' --> p -> q = q'.*)

  
  Definition DisjointBranch (s : Lab) (xl : list Var) (qt qf : Lab) (π ϕ : list Lab) :=
    CPath s qt (π >: s) /\ CPath s qf (ϕ >: s) /\ branch s =' xl /\ Disjoint π ϕ.

  Parameter path_splits : Lab -> list (Lab * Lab * Lab * list Var).

  Parameter loop_splits : Lab -> Lab -> list (Lab * Lab * Lab * list Var).

  Definition pl_split `{Graph Lab} (qh qe q1 q2 br : Lab) (xl : list Var) :=
      (exists π ϕ, Path br qh (π >: q1 :>: br)
              /\ Path br qe (ϕ >: q2 :>: br)
              /\ Disjoint (tl π :r: q1) (tl ϕ :r: q2)
              /\ branch br =' xl).

  Set Printing All.

  Parameter path_splits_spec : forall `{Graph Lab} p q1 q2 br xl,
      pl_split p p q1 q2 br xl <->
      (br, q1, q2, xl) ∈ path_splits p.
  
  Parameter loop_splits_spec : forall `{Graph Lab} qh qe q1 q2 br xl,
      in_loop br qh /\ (* otherwise some splits would be considered as loop splits *)
      pl_split qh qe q1 q2 br xl <->
      (br, q1, q2, xl) ∈ loop_splits qh qe.
  
(*  Parameter preceding_loops : Lab -> Lab -> list (Lab * Lab).

  Parameter preceding_loops_spec : forall s p qh qe, (qh, qe) ∈ preceding_loops p s
                                              <-> loop_head qh
                                                /\ qh ∈ loop_exit qe
                                                /\ in_loop s qh
                                                /\ ~ in_loop p qh
                                                /\ qe --> p.*)
  
  Lemma last_common_split s x p q1 q2 l1 l2 :
    Path root p (p :<: l1)
    -> Path root p (p :<: l2)
    -> last_common l1 l2 s
    -> In (s,q1,q2,x) (path_splits p).
  Admitted.
  
(*  Lemma last_common_split_loopsplit s x s' l1 l2 k :
    Tr (k :<: l1)
    -> Tr (k :<: l2)
    -> In (s,x) (splits (lab_of k))
    -> last_common (ne_map fst l1) (ne_map fst l2) s'
    -> In (fst s') (map fst (loop_splits s)).
  Admitted.*)
  
  Lemma disjoint_map_fst {A B : Type} (l1 l2 : list (A*B)) (l1' l2' : list A) :
    l1' = map fst l1
    -> l2' = map fst l2
    -> Disjoint l1' l2'
    -> Disjoint l1 l2.
  Admitted.

  Definition innermost_loop p qh :=
    in_loop p qh /\ forall qh', in_loop p qh' -> in_loop qh qh'.
  
  Lemma tag_eq_ex_innermost_lh q q' j l p i :
    TPath' ((q',j) :<: nl_rcons l (q,j))
    -> In (p,i) l
    -> i = j \/ exists lh, innermost_loop p lh /\ In lh (map fst l).
  Admitted.

  
  Hint Unfold CPath.
    
  Lemma disj_loopheads p i q l1 l2 qh :
    TPath' ((p,i) :<: nl_rcons l1 (q,i))
    -> TPath' ((p,i) :<: nl_rcons l2 (q,i))
    -> Disjoint l1 l2
    -> loop_head qh
    -> In qh (map fst l1)
    -> ~ In qh (map fst l2).
  Admitted.

  (* This is wrong! This holds only for the FIRST header.
  Lemma loop_head_tag_cases l q i qh j :
    TPath' (nl_rcons l (q,i))
    -> loop_head qh
    -> In (qh,j) l
    -> j = O :: i
      \/ match i with
        | nil => False
        | m :: i' => j = S m :: i'
        end.
  Admitted.
  *)

  Lemma lab_tag_same_length c0 c c' p i j l l' :
    TPath c0 c l (* the paths need to have the same origin *)
    -> TPath c0 c' l'
    -> (p,i) ∈ l
    -> (p,j) ∈ l'
    -> length i = length j.
  Admitted.

  Lemma tag_length_inbetween p i l q q' j :
    TPath' ((p,i) :<: nl_rcons l (q,i))
    -> (q',j) ∈ l
    -> length i <= length j.
    (* because if we would exit a loop, we could never achieve to get the same tag again *)
  Admitted.
  
End Disjoint.