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

  Parameter branch: Lab -> option (Lab * Lab * Var * Var).

  Definition is_branch br x := exists tt ff xb, branch br = Some (tt, ff, x, xb).

  Parameter val_true : Val -> bool.

  Parameter branch_spec :
    forall b, match branch b with
              | Some (t, f, x, xb) => t =/= f /\
                                      forall i s k, eff (b, i, s) = Some k ->
                                                    lab_of k = (if val_true (s x) then t else f)
              | None => forall i i' s s' k k', eff (b, i, s) = Some k ->
                                               eff (b, i', s') = Some k' ->
                                               lab_of k = lab_of k'
              end.

  Parameter branch_spec_var : 
    forall b t f x xb, branch b = Some (t, f, x, xb) -> is_def xb b t = true /\ is_def xb b f = true /\
                                                        forall b', b =/= b' -> forall p, is_def xb b' p = false.

  Parameter in_out_spec :
    forall p q q', (exists x, is_branch p x) -> q --> p -> q' --> p -> q = q'.

  Definition DisjointBranch (s : Lab) (x : Var) (qt qf : Lab) (π ϕ : list Lab) :=
    CPath s qt (nl_rcons π s) /\ CPath s qf (nl_rcons ϕ s) /\ is_branch s x /\ Disjoint π ϕ.

  Parameter splits : Lab -> list (Lab * Var).

  Parameter splits_spec : forall conv br x,
      (exists qt qf π ϕ, qt --> conv /\ qf --> conv /\ qt =/= qf /\
                    DisjointBranch br x qt qf π ϕ) <->
      List.In (br, x) (splits conv).

  Parameter loop_splits : Lab -> list (Lab * Var).

  Parameter loop_splits_spec : forall p br x,
      (exists qh π ϕ, in_loop br qh /\ qh <> p /\ DisjointBranch br x qh p π ϕ)
      <-> In (br, x) (loop_splits p).

  Lemma split_last_common s x p l1 l2 :
    Path root p (p :<: l1)
    -> Path root p (p :<: l2)
    -> In (s,x) (splits p)
    -> last_common l1 l2 s.
  Admitted.
  
  Lemma last_common_split s x p l1 l2 :
    Path root p (p :<: l1)
    -> Path root p (p :<: l2)
    -> last_common l1 l2 s
    -> In (s,x) (splits p).
  Admitted.
  
  Lemma last_common_split_loopsplit s x s' l1 l2 k :
    Tr (k :<: l1)
    -> Tr (k :<: l2)
    -> In (s,x) (splits (lab_of k))
    -> last_common (ne_map fst l1) (ne_map fst l2) s'
    -> In (fst s') (map fst (loop_splits s)).
  Admitted.
  
  Lemma disjoint_map_fst {A B : Type} (l1 l2 : list (A*B)) (l1' l2' : list A) :
    l1' = map fst l1
    -> l2' = map fst l2
    -> Disjoint l1' l2'
    -> Disjoint l1 l2.
  Admitted.

  Definition innermost_loop p qh :=
    in_loop p qh /\ forall qh', in_loop p qh -> in_loop qh qh'.
  
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