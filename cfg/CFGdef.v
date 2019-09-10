Set Nested Proofs Allowed.

Require Export Coq.Logic.Decidable.
Require Export Coq.Classes.EquivDec.
Require Export Coq.Bool.Bool.
Require Export Lists.List.
Require Export Coq.Program.Equality.
Require Export Coq.Program.Utils.

(*Require Import finiteTypes.External.
Require Import finiteTypes.BasicDefinitions.*)

Require Export FinTypes.

Require Export Graph SimplDec ListExtra.

(*  Notation "p '-->*' q" := (exists π, Path p q π) (at level 55, right associativity).*)

(** Definition of the reducible CFG **)

Reserved Infix "-->b" (at level 55).
Reserved Infix "-a>" (at level 55).
Reserved Infix "-a>*" (at level 55).

Class redCFG
      (Lab : finType)
      (edge : Lab -> Lab -> bool)
      (root : Lab) 
      (a_edge : Lab -> Lab -> bool)
  :=
    {
      back_edge_b := minus_edge edge a_edge
                     where "p -->b q" := (edge p q);
      back_edge := (fun p q => back_edge_b p q = true)
                   where "p --> q"  := (p -->b q = true);
      (* reducibility *)
      loop_head_dom : forall ql qh, back_edge ql qh -> Dom edge root qh ql
      where "p -a> q" := (a_edge p q = true);
      a_edge_incl : sub_graph a_edge edge
      where "p '-a>*' q" := (exists π, Path a_edge p q π);
      a_edge_acyclic : acyclic a_edge;
      a_reachability : forall q, (exists π, Path a_edge root q π);
      (* useful definitions *)
      loop_head h := exists p, back_edge p h;
      loop_contains qh q := exists p π, back_edge p qh /\ Path edge q p π /\ qh ∉ tl (rev π);
      exit_edge h p q := loop_contains h p /\ ~ loop_contains h q /\ p --> q;
      (* the following restrictions can be easily be met by introducing new blocks *)
      single_exit : forall h p q, exit_edge h p q -> forall h', exit_edge h' p q -> h = h';
      no_exit_head : forall h p q, exit_edge h p q -> ~ loop_head q;
      exit_pred_loop : forall h q qe e, exit_edge h qe e -> q --> e -> loop_contains h q;
      no_self_loops : forall q p, edge q p = true -> q <> p;
      root_no_pred : forall p, edge p root <> true
    }.

Hint Resolve loop_head_dom a_edge_incl a_edge_acyclic a_reachability.


  Lemma ne_list_nlrcons: forall (A : Type) (l : ne_list A), exists (a : A) (l' : list A), l = l' >: a.
  Proof.
    induction l.
    - exists a, nil. eauto.
    - destructH. rewrite IHl. exists a0, (a :: l'). cbn. reflexivity.
  Qed.
  
  Ltac destr_r x :=
    let Q := fresh "Q" in
    specialize (ne_list_nlrcons x) as Q;
    let a := fresh "a" in
    let l := fresh "l" in
    destruct Q as [a [l Q]];
    rewrite Q in *.
  
  Definition CPath `{redCFG} := Path edge.
  Definition APath `{redCFG} := Path a_edge.
  Infix "↪" := back_edge (at level 55).
  Notation "p '-->*' q" := (exists π, CPath p q π) (at level 55, right associativity).
  Notation "p '-a>*' q" := (exists π, APath p q π) (at level 55).

Section cfg.
  Context `{C : redCFG}.

  Notation "p '-a>b' q" := (a_edge p q) (at level 55).
  Notation "p '-a>' q" := (p -a>b q = true) (at level 55).
  Notation "p '-->b' q" := (edge p q) (at level 55).
  Notation "p '-->' q" := (p -->b q = true) (at level 55, right associativity).

  (** abbreviation for CPath **)
  Definition CPath' π := CPath (ne_back π) (ne_front π) π.

  Lemma cpath_cpath' (* unused *)r p t
        (Hpath : CPath r p t)
    : CPath' t.
  Proof.
    unfold CPath'. eapply path_back in Hpath as Hback.
    eapply path_front in Hpath as Hfront.
    rewrite Hfront,Hback. assumption.
  Qed.
  
  (*
Local Ltac prove_spec :=
  intros;
  let tac :=
      fun _ => lazymatch goal with
              [ |- to_bool ?e = true <-> ?p] => destruct e; cbn; split; eauto ; intros; congruence
            end
  in
  lazymatch goal with
  | [ |- ?f _ _ _ = true <-> ?p ]
    => unfold f; tac 0
  | [ |- ?f _ _ = true <-> ?p ]
    => unfold f; tac 0
  | [ |- ?f _ = true <-> ?p ]
    => unfold f; tac 0
  | [ |- ?f = true <-> ?p ]
    => unfold f; tac 0
  end.*)

  (** decidable properties on redCFG **)
  
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
    unfold back_edge, back_edge_b, minus_edge.
    destruct (edge p q), (a_edge p q);cbn;firstorder.
  Qed.

  Hint Resolve back_edge_dec.

  (** Some basic facts **)
  
  Lemma reachability (q : Lab) : exists π : ne_list Lab, Path edge root q π.
  Proof.
    specialize (a_reachability q) as Hreach. destructH. exists π. eapply subgraph_path';eauto. 
  Qed.
  
  Lemma back_edge_incl (p q : Lab) (Hback : p ↪ q) : edge p q = true.
  Proof. 
    unfold back_edge,back_edge_b in Hback. eapply minus_subgraph. eauto.
  Qed.

  Lemma acyclic_path_NoDup p q π
        (Hπ : Path a_edge p q π)
    : NoDup π.
  Proof.
    induction Hπ.
    - econstructor;eauto. econstructor.
    - cbn. econstructor;auto.
      intro N. specialize a_edge_acyclic as Hacy. unfold acyclic in Hacy.
      eapply path_from_elem in N;eauto. destructH. apply Hacy in N0;eauto.
  Qed.
  
  (** about loops **)
  
  Lemma loop_contains_loop_head (qh q : Lab)
    : loop_contains qh q -> loop_head qh.
  Proof.
    intro Q. unfold loop_head, loop_contains in *. destruct Q as [p [_ [Q _]]].
    eexists; eauto.
  Qed.

  Lemma loop_contains_self h : loop_head h -> loop_contains h h.
  Proof.
    intros Hl. unfold loop_contains.
    - unfold loop_head in Hl. destruct Hl. 
      eapply loop_head_dom in H as Hdom.
      eapply back_edge_incl in H as Hreach. specialize (a_reachability x) as Hreach'.
      destructH.
      eapply subgraph_path' in Hreach' as Hreach'';eauto using a_edge_incl.
      eapply Hdom in Hreach''. eapply path_from_elem in Hreach''; eauto.
      destructH; eauto.
      eapply path_NoDup' in Hreach''0;eauto. 
      destructH. exists x, π0. firstorder;eauto.
      + eapply subgraph_path';eauto using a_edge_incl.
      + eapply NoDup_rev in Hreach''3. eapply path_back in Hreach''2.
        remember (rev π0) as l.
        destruct l;cbn in *;eauto.
        specialize (ne_list_nlrcons π0) as Heql'. destructH. subst π0. cbn in *. simpl_nl' Heql.
        rewrite rev_rcons in Heql. inversion Heql;subst e l.
        simpl_nl' Hreach''2. subst. inversion Hreach''3;subst. auto.
  Qed.
  
End cfg.