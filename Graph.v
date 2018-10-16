
Require Import Coq.Logic.Decidable.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Bool.Bool.
Require Import Lists.ListSet.
Require Import Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Utils.

Require NeList.

Module Graph.

  Import NeList.NeList.
    
  Parameter Var : Type.
  Parameter Lab : Type.

  Parameter Var_dec : EqDec Var eq.
  Parameter Lab_dec' : forall (l l' : Lab), { l = l' } + { l <> l'}.
  Parameter Lab_dec : EqDec Lab eq.

  Parameter all_lab : set Lab.
  Parameter all_lab_spec : forall l, set_In l all_lab.

  Parameter loop_exit : Lab -> list Lab.
  Parameter is_back_edge : Lab -> Lab -> bool.

  Parameter preds : Lab -> list Lab.
  Notation "p --> q" := (List.In p (preds q)) (at level 70, right associativity).
  Notation "p -->? q" := (p === q \/ p --> q) (at level 70, right associativity).
  
  Definition loop_head p : Prop :=
    exists q, q --> p /\ is_back_edge q p = true.

  Parameter loop_head_dec : forall p, {loop_head p} + {~ loop_head p}.

  Parameter root : Lab.
  Parameter root_no_pred : forall p, ~ p --> root.

  Parameter is_def : Var -> Lab -> Lab -> bool.

  Parameter def_edge :
    forall p q x, is_def x p q = true -> p --> q.

  Definition is_def_lab x p := exists q, is_def x q p = true.

  Lemma Lab_var_dec :
    forall (x y : (Lab * Var)), { x = y } + { x <> y }.
  Proof.
    intros.
    destruct x as [xa xb], y as [ya yb].
    destruct ((xa, xb) == (ya, yb)); firstorder.
  Qed.
  Program Instance lab_var_eq_eqdec : EqDec (Lab * Var) eq := Lab_var_dec.

  (** Paths **)

  Inductive Path : Lab -> Lab -> ne_list Lab -> Prop :=
  | PathSingle a : Path a a (ne_single a)
  | PathCons {a b c π} : Path a b π -> b --> c -> Path a c (c :<: π).

  Notation "p '-->*' q" := (exists π, Path p q π) (at level 70, right associativity).

  Notation "p '-a>' q" := (In p (preds q) /\ is_back_edge p q = false) (at level 70).
      
  Lemma acyclic_edge_has_edge : forall p q, p -a> q -> p --> q.
  Proof.
    intros. firstorder. 
  Qed.

  Inductive AcyPath : Lab -> Lab -> ne_list Lab -> Prop :=
  | AcyPathSingle : forall p : Lab, AcyPath p p (ne_single p)
  | AcyPathCons : forall (p q r : Lab) π, AcyPath p q π -> q -a> r -> AcyPath p r (r :<: π).

  Notation "p '-a>*' q" := (exists π, AcyPath p q π) (at level 70).
  
  (* Reducibility *)
  Parameter reach_acy : forall (p : Lab), root -a>* p.

  Definition Dom p q := forall π, Path root q π -> In p π.
  
  Parameter loop_head_dom : forall ql qh, is_back_edge ql qh = true -> Dom qh ql.

  Definition in_loop q qh : Prop :=
    exists p, q -a>* p /\ p --> qh /\ is_back_edge p qh = true.
  
  Parameter loop_exit_spec : forall qh qe,
      In qh (loop_exit qe) <-> exists q, q --> qe /\ in_loop q qh /\ ~ in_loop qe qh.


(*  Lemma path_last_common r a b π π' :
    Path r a π -> Path r b π' -> a <> b
    -> exists s ϕ ϕ', Postfix (ϕ :>: s) π /\ Postfix (ϕ' :>: s) π' /\ Disjoint ϕ ϕ'.
  Proof.*)

(*  Lemma Path_in_dec {z a} x (p: Path a z) :
    {PathIn x p} + {~ PathIn x p}.
  Proof.
    induction p.
    + destruct (x == p); firstorder.
    + simpl in *. destruct (x == to); firstorder.
  Qed. 

  Lemma path_first_in {a} b (p : Path a b) :
    PathIn a p.
  Proof.
    induction p.
    + constructor.
    + simpl. eauto.
  Qed.

  Lemma path_last_in {a} b (p : Path a b) :
    PathIn b p.
  Proof.
    induction p.
    + constructor.
    + simpl. left. reflexivity.
  Qed.

  Fixpoint acyclic {a c} (p : Path a c) : Prop :=
    match p with
    | PathInit p => True
    | PathStep a b c p' e => acyclic p' /\ ~ PathIn c p'
    end.

  Lemma path_in_single_acyclic {a} (p : Path a a) :
    acyclic p -> forall q, PathIn q p -> q = a.
  Proof.
    intros Hacyc q Hin.
    dependent induction p; simpl in Hin; [ eauto |].
    simpl in Hacyc.
    exfalso. apply Hacyc. eapply path_first_in.
  Qed.

  Lemma acyclic_prefix {a b c} (p : Path a b) (e : b --> c) :
    acyclic (PathStep a b c p e) -> acyclic p.
  Proof.
    intros.
    destruct p; simpl in *; firstorder.
  Qed.

    Lemma path_exists_pred {a b} (p : Path a b) :
    a <> b -> exists q (p' : Path a q) (e : q --> b),  p = (PathStep a q b p' e).
  Proof.
    intros.
    induction p; [ firstorder |].
    destruct (from == p).
    - rewrite e in *. eauto.
    - eapply IHp in c. eauto. 
  Qed.

  Lemma path_acyclic_pred {a q} (p : Path a q) b e :
    acyclic (PathStep a q b p e) -> acyclic p.
  Proof.
    intros.
    dependent induction p; simpl in *; firstorder.
  Qed.

  Lemma path_acyclic_next {a q p} (π : Path a q) (edge : q --> p) :
        acyclic π -> acyclic (PathStep a q p π edge) \/ exists (π' : Path a p), acyclic π' /\ forall q, PathIn q π' -> PathIn q π.
  Proof.
    intros.
    simpl.
    destruct (Path_in_dec p π).
    - right.
      clear edge.
      induction π.
      + inject p0. exists (PathInit p1). simpl. eauto.
      + inject p0.
        * exists (PathStep from p1 to π i). split; try eauto.
        * eapply path_acyclic_pred in H. destruct (IHπ H H0) as [π' [Hacyc Hin]].
          exists π'. split; [ assumption |]. intros. simpl. eauto.
    - left. eauto.
  Qed.
  
  Fixpoint path_concat {a b c} (π : Path a b) (π' : Path b c) : Path a c.
    refine ((match π' as y in (Path b' c) return
                  (b' = b -> Path a c) with
    | PathInit _ => _
    | PathStep b c c' π' e => _
    end) (eq_refl b)); intros; subst.
    - apply π.
    - eapply (PathStep _ _ _ (path_concat _ _ _ π π') e).
  Defined.
  
  Lemma concat_in1 {a b c} (π : Path a b) (π' : Path b c) :
    forall q, PathIn q π -> PathIn q (path_concat π π').
  Proof.
    intros. induction π'; simpl; eauto.
  Qed.

  Lemma path_pred {a b} (p : Path a b) :
    a = b \/ exists pred, pred --> b.
  Proof.
    induction p; eauto.
  Qed.

  Lemma path_nodes_neq {a b} (p : Path a b) r s :
    PathIn r p ->
    ~ PathIn s p ->
    r <> s.
  Proof.
    intros Hin Hnin.
    induction p.
    - inject Hin. intro. apply Hnin. subst. constructor.
    - intro. subst. apply Hnin. assumption.
  Qed.

  (*
  Definition disjoint {a b c d} (p : Path a b) (p' : Path c d) :=
    (forall q, PathIn q p -> ~ PathIn q p') /\ (forall q, PathIn q p' -> ~ PathIn q p).
  *)

  Definition deciabable_PathIn a b (p : Path a b) q :
    decidable (PathIn q p).
  Proof.
    unfold decidable.
    induction p.
    + simpl. destruct (q == p); firstorder.
    + simpl. destruct IHp; firstorder.
      destruct (q == to); firstorder.
  Qed.*)


  (*Parameter finite_Lab : 
    exists (n : nat) (f : Lab -> nat), forall x, f x <= n /\ forall y, f x = f y -> x = y.*) 
  
  (*Parameter dec_path : forall p q, Path p q + (Path p q -> False).

  Definition reaches (p q : Lab) : bool
    := if dec_path p q then true else false.*)

  Parameter no_self_loops :
    forall q p, q --> p -> q =/= p.

  (*Definition DisjPaths {a b c d} (π : Path a b) (π' : Path c d) :=
    forall p, (PathIn p π -> ~ PathIn p π') /\ (PathIn p π' -> ~ PathIn p π).*)


End Graph.