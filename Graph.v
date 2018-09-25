
Require Import Coq.Logic.Decidable.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Bool.Bool.
Require Import Lists.ListSet.
Require Import Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Utils.


Module Graph.

    
  Parameter Var : Type.
  Parameter Lab : Type.

  Parameter Var_dec : EqDec Var eq.
  Parameter Lab_dec' : forall (l l' : Lab), { l = l' } + { l <> l'}.
  Parameter Lab_dec : EqDec Lab eq.

  Parameter all_lab : set Lab.
  Parameter all_lab_spec : forall l, set_In l all_lab.

  Parameter loop_head : Lab -> nat.
  Parameter loop_exit : Lab -> nat.
  Parameter is_back_edge : Lab -> Lab -> bool.

  Parameter preds : Lab -> list Lab.
  Notation "p --> q" := (List.In p (preds q)) (at level 70, right associativity).

  Notation "p -->* q" := (p === q \/ p --> q) (at level 70, right associativity).

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

  
  Inductive Path : list Lab -> Prop :=
  | PathNil : Path nil
  | PathCons a b p' : Path (b :: p') -> a --> b -> Path (a :: b :: p').

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

  Parameter has_edge_acyclic : Lab -> Lab -> bool.
  
  Notation "p '-a>' q" := (has_edge_acyclic p q = true) (at level 70).

  Parameter has_edge_acyclic_spec : forall p q, p -a> q <-> (p --> q
                                                      /\ (loop_head q = 0
                                                         \/ loop_exit p = 0)).
      
  Lemma has_edge_acyclic_has_edge : forall p q, p -a> q -> p --> q.
  Proof.
    intros. apply has_edge_acyclic_spec in H. firstorder.
  Qed.

  Inductive AcyPath : Lab -> Lab -> Prop :=
  | AcyPathInit : forall p : Lab, AcyPath p p
  | AcyPathStep : forall p q r : Lab, AcyPath p q -> q -a> r -> AcyPath p r.

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