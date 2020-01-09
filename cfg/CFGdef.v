Set Nested Proofs Allowed.

Require Export Coq.Logic.Decidable.
Require Export Coq.Classes.EquivDec.
Require Export Coq.Bool.Bool.
Require Export Lists.List.
Require Export Coq.Program.Equality Coq.Program.Utils.

(*Require Import finiteTypes.External.
Require Import finiteTypes.BasicDefinitions.*)

Require Export FinTypes.

Require Export Graph SimplDec.

(*  Notation "p '-->*' q" := (exists π, Path p q π) (at level 55, right associativity).*)

(** Definition of the reducible CFG **)

Reserved Infix "-->b" (at level 55).
Reserved Infix "-a>" (at level 55).
Reserved Infix "-a>*" (at level 55).

Definition is_true2 (A B : Type) := fun (f : A -> B -> bool) (a : A) (b : B) => is_true (f a b).

Class redCFG
      (Lab : finType)
      (edge : Lab -> Lab -> bool)
      (root : Lab)
      (a_edge : Lab -> Lab -> bool)
  :=
    {
      edge__P := is_true2 edge;
      a_edge__P := is_true2 a_edge;
      back_edge := minus_edge edge__P a_edge__P
                   where "p --> q" := ((is_true2 edge) p q);
      (* reducibility *)
      loop_head_dom : forall ql qh, back_edge ql qh -> Dom edge__P root qh ql
      where "p -a> q" := (a_edge p q = true);
      a_edge_incl : sub_graph a_edge__P edge__P
      where "p '-a>*' q" := (exists π, Path a_edge__P p q π);
      a_edge_acyclic : acyclic a_edge__P;
      a_reachability : forall q, (exists π, Path a_edge__P root q π);
      (* useful definitions *)
      loop_head h := exists p, back_edge p h;
      loop_contains qh q := exists p π, back_edge p qh /\ Path edge__P q p π /\ qh ∉ tl (rev π);
      exit_edge h p q := loop_contains h p /\ ~ loop_contains h q /\ p --> q;
      (* the following restrictions can be easily be met by introducing new blocks *)
      single_exit : forall h p q, exit_edge h p q -> forall h', exit_edge h' p q -> h = h';
      no_exit_head : forall h p q, exit_edge h p q -> ~ loop_head q;
      exit_pred_loop : forall h q qe e, exit_edge h qe e -> q --> e -> loop_contains h q;
      no_self_loops : forall q p, edge q p = true -> q <> p;
      root_no_pred : forall p, edge p root <> true
    }.

Hint Resolve loop_head_dom a_edge_incl a_edge_acyclic a_reachability.
  
  Definition CPath `{redCFG} := Path edge__P.
  Definition APath `{redCFG} := Path a_edge__P.
  Infix "↪" := back_edge (at level 55).
  Notation "p '-->*' q" := (exists π, CPath p q π) (at level 55, right associativity).
  Notation "p '-a>*' q" := (exists π, APath p q π) (at level 55).

Section cfg.
  Context `{C : redCFG}.

  Notation "p '-a>b' q" := (a_edge p q) (at level 55).
  Notation "p '-a>' q" := (p -a>b q = true) (at level 55).
  Notation "p '-->b' q" := (edge p q) (at level 55).
  Notation "p '-->' q" := (p -->b q = true) (at level 55, right associativity).


  (** * decidable properties on redCFG **)
  
  Global Instance Lab_dec : EqDec Lab eq.
  Proof.
    intros x y. destruct (decide_eq x y).
    - left. rewrite e. reflexivity.
    - right. eauto.
  Qed.
  
  Instance loop_head_dec p : dec (loop_head p).
    eauto.
  Qed.

  (* I could also prove that, but it is not trivial non-classical. *)  
  Parameter loop_contains_dec : forall qh q, dec (loop_contains qh q).
  Global Existing Instance loop_contains_dec.
  
  Hint Resolve loop_contains_dec.

  Global Instance exit_edge_dec : forall h p q, dec (exit_edge h p q).
  Proof.
    eauto.
  Qed.

  Definition entry_edge (p h : Lab) := loop_head h /\ ~ loop_contains h p /\ edge p h = true.

  Definition exiting (h p : Lab) : Prop :=
    exists q, exit_edge h p q.

  Definition exited (h q : Lab) : Prop :=
    exists p, exit_edge h p q.

  Global Instance exited_dec (h q : Lab) : dec (exited h q).
  Proof.
    eauto.
  Qed.

  Lemma back_edge_dec p q : dec (p ↪ q).
  Proof.
    eauto.
  Qed.

  Hint Resolve back_edge_dec.
  
  (** * depth **)

  Definition depth (p : Lab) := length (filter (DecPred (fun h => loop_contains h p)) (elem Lab)). 

  (** * Some basic facts **)
  
  Lemma reachability (q : Lab) : exists π : list Lab, Path edge__P root q π.
  Proof.
    specialize (a_reachability q) as Hreach. destructH. exists π. eapply subgraph_path';eauto. 
  Qed.
  
  Lemma back_edge_incl (p q : Lab) (Hback : p ↪ q) : edge__P p q.
  Proof. 
    unfold back_edge in Hback. eapply minus_subgraph. eauto.
  Qed.

  Lemma acyclic_path_NoDup p q π
        (Hπ : Path a_edge__P p q π)
    : NoDup π.
  Proof.
    induction Hπ.
    - econstructor;eauto. econstructor.
    - cbn. econstructor;auto.
      intro N. specialize a_edge_acyclic as Hacy. unfold acyclic in Hacy.
      eapply path_from_elem in N;eauto. destructH. apply Hacy in N0;eauto.
  Qed.

  Lemma edge_destruct p q
        (Hedge : p --> q)
    : p -a> q \/ p ↪ q.
  Proof.
    decide (p -a> q);[left;auto|right].
    unfold back_edge. unfold minus_edge. conv_bool. split; auto.
  Qed.
  
End cfg.

(** * decPred_bool **)

Instance decide_decPred_bool (A : Type) (f : A -> bool) a : dec (if f a then True else False).
Proof.
  cbn. destruct (f a); eauto.
Qed.

Definition decPred_bool (A : Type) (f : A -> bool) := DecPred (fun a => if f a then True else False).

Definition finType_sub_decPred {X : finType} (p : decPred X) : finType.
Proof.
  eapply (@finType_sub X p). eapply decide_pred. 
Defined.

(** * generalizations **)

Open Scope prg.

Definition restrict_edge (A : finType) (f : A -> A -> Prop) (p : decPred A)
  : let L' := finType_sub p (decide_pred p) in L' -> L' -> Prop
  := fun x y => (f (`x) (`y)).

Definition restrict_edge' (A : Type) (f : A -> A -> Prop) (p : decPred A)
  := f ∩ ((fun a _ => p a)
            ∩ (fun _ b => p b)).

Definition loop_contains' (L : Type) (edge a_edge : L -> L -> Prop) (qh q : L)
  := exists (p : L)  π, (edge ∖ a_edge) p qh
                   /\ Path edge q p π
                   /\ qh ∉ tl (rev π).

Definition exit_edge' (L : finType) (edge a_edge : L -> L -> Prop) (h p q : L)
  := loop_contains' edge a_edge h p /\ ~ loop_contains' edge a_edge h q /\ edge p q.

Definition back_edge'  (L : Type) (edge a_edge : L -> L -> Prop) (p q : L)
  := (edge ∖ a_edge) p q.

Definition loop_head' (L : Type) (edge a_edge : L -> L -> Prop) (h : L)
  := exists p, ((edge) ∖ (a_edge)) p h.
