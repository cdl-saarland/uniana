
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Decidable.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Bool.Bool.
Require Import Lists.ListSet.
Require Import Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Utils.

Require Import Util.
Require NeList.

Module Graph.

  Export NeList.NeList.

  (** Graph **)

  Class Graph (L : Type) (edge : L -> L -> Prop) : Type :=
    {
      L_dec : EqDec L eq where "p --> q" := (edge p q);
      edge_dec : forall p q, {p --> q} + {~ p --> q}(*;
      root_no_pred : forall p:L, ~ edge p root*)
    }.

  Generalizable Variables L root edge.

  Notation "p --> q" := ((fun (L : Type) (edge : L -> L -> Prop) (_ : Graph L edge) => edge) _ _ _ p q)
                          (at level 55, right associativity).

(*  Infix "-->" := edge (at level 55, right associativity).*)

  Definition in_graph `{Graph} (p : L) := exists q, p --> q \/ q --> p.
  
  Inductive Path `{Graph} : L -> L -> ne_list L -> Prop :=
  | PathSingle a : Path a a (ne_single a)
  | PathCons {a b c π} : Path a b π -> b --> c -> Path a c (c :<: π).

  Definition Dom `{Graph} r p q := forall π, Path r q π -> In p π.

  Program Instance sub_Graph `{G : Graph} (l : list L)
    : Graph L (fun p q => (p ∈ l /\ q ∈ l /\ edge p q)).
  Next Obligation. apply L_dec. Qed.
  Next Obligation.
    destruct (edge_dec p q).
    destruct (in_dec L_dec p l).
    destruct (in_dec L_dec q l).
    1: left; firstorder. all: right; firstorder.
  Qed.
  
  Program Instance union_Graph
          {L : Type} {edge1 edge2 : L -> L -> Prop}
          (G1 : Graph L edge1) (G2 : Graph L edge2)
    : Graph L (fun p q => edge1 p q \/ edge2 p q).
  Next Obligation. apply L_dec. Qed.
  Next Obligation.
    destruct (@edge_dec _ edge1 _ p q), (@edge_dec _ edge2 _ p q); tauto.
  Qed.
  (*Next Obligation.
    intro H. destruct H; apply root_no_pred in H; contradiction.
  Qed.*)

  Program Instance minus_Graph
          {L : Type} {edge1 edge2 : L -> L -> Prop}
          (G1 : Graph L edge1) (G2 : Graph L edge2)
    : Graph L (fun p q => edge1 p q /\ ~ edge2 p q).
  Next Obligation. apply L_dec. Qed.
  Next Obligation.
    destruct (@edge_dec _ edge1 _ p q), (@edge_dec _ edge2 _ p q); tauto.
  Qed. (*
  Next Obligation.
    intro H. destruct H; apply root_no_pred in H; contradiction.
  Qed.*)

  Lemma path_front `{Graph} p q π :
    Path p q π -> ne_front π = q.
  Admitted.
  
  Lemma path_back `{Graph} p q π :
    Path p q π -> ne_front π = p.
  Admitted.

  Lemma postfix_path `{Graph} l p q q' l' :
    Path q' q l'
    -> Postfix (l :r: p) l'
    -> Path p q (nl_rcons l p).
  Admitted.

  Definition Path' `{Graph} π := Path (ne_back π) (ne_front π) π.


  Lemma ne_to_list_not_nil {A:Type} (l : ne_list A) :
    nil <> l.
  Proof.
    intro N. induction l; cbn in *; congruence.
  Qed.
  
  Lemma postfix_front {A : Type} (l l' : ne_list A) :
    Postfix l l'
    -> ne_front l = ne_front l'.
  Proof.
    intros H. dependent induction H.
    - apply ne_to_list_inj in x; rewrite x; eauto.
    - rewrite rcons_nl_rcons in x. apply ne_to_list_inj in x. 
      rewrite <-x. destruct l'0.
      + exfalso. inversion H; [eapply ne_to_list_not_nil|eapply rcons_not_nil]; eauto.
      + cbn. erewrite IHPostfix; eauto; [|rewrite nlcons_to_list; reflexivity]. simpl_nl; reflexivity.
  Qed.
  
  Lemma path_postfix_path `{Graph} p q q' (l l' : ne_list L) :
    Path p q l
    -> Postfix l' l
    -> Path p q' l'.
  Proof.
  Admitted. (*
    intros Hpath Hpost. dependent induction Hpost.
    - apply ne_to_list_inj in x. setoid_rewrite x; eauto.
    - unfold Path'. specialize (IHHpost H). erewrite postfix_front; eauto.
  Qed.*)

End Graph.
(*+ CFG +*)

Module CFG.

  Export Graph.
  
  (** basic parameters **)
  Parameter Lab : Type.  
  Parameter all_lab : list Lab.
  Parameter all_lab_spec : forall l, l ∈ all_lab.
  Parameter Lab_dec : EqDec Lab eq.
     
  Program Instance Lab_Graph
          (rel : Lab -> Lab -> Prop)
          (rel_dec : forall a b, {rel a b} + {~ rel a b})
    : Graph Lab rel.

  Notation "p '-->*' q" := (exists π, Path p q π) (at level 55, right associativity).

  Reserved Notation "p -a> q" (at level 55).
  Reserved Notation "p -a>* q" (at level 55).

  Definition decidableT (a : Prop) := {a} + {~ a}.

  Definition minus_edge (rel_sub rel_min : Lab -> Lab -> Prop) : Lab -> Lab -> Prop :=
    (fun p q : Lab => rel_sub p q /\ ~ rel_min p q).

  Lemma minus_dec (rel_sub rel_min : Lab -> Lab -> Prop) :
    (forall p q, decidableT (rel_sub p q))
    -> (forall p q, decidableT (rel_min p q))
    -> (forall p q, decidableT (minus_edge rel_sub rel_min p q)).
  Proof.
    unfold decidableT, minus_edge. intros sdec mdec.
    intros. specialize (sdec p q). specialize (mdec p q). destruct sdec, mdec; firstorder.
  Qed.
  
  Class redCFG (edge : Lab -> Lab -> Prop) (G : Graph Lab edge) (root : Lab)
        {acyclic_edge : Lab -> Lab -> Prop}
        (acyclic_fragment : Graph Lab acyclic_edge) :=
    {
      loop_head_dom : forall ql qh, minus_edge edge acyclic_edge ql qh -> @Dom _ _ G root qh ql
                   where "p -a> q" := (acyclic_edge p q);
      acyclic_edge_incl : forall p q, p -a> q -> p --> q 
                   where "p '-a>*' q" := (exists π, @Path _ acyclic_edge acyclic_fragment p q π);
      (*reach_acy : forall (p : Lab), root -a>* p; this is too much, we want to allow incomplete graphs*)
      acyclic : forall (p q : Lab), p -a> q -> ~ q -a>* p;
    }.

  Notation "p '-a>' q" := ((fun (acyclic_edge : Lab -> Lab -> Prop)
                              (acyclic_fragment : Graph Lab acyclic_edge)
                              (_ : redCFG _ _ acyclic_fragment) => acyclic_edge) _ _ _ p q)
                            (at level 55).
  
  Definition AcyPath `{redCFG} : Lab -> Lab -> ne_list Lab -> Prop :=
    @Path _ _ acyclic_fragment.

  Notation "p '-a>*' q" := (exists π, AcyPath p q π) (at level 55).

  Generalizable Variables G root acyclic_edge acyclic_fragment edge.

  Definition back_edge {edge acyclic_edge : Lab -> Lab -> Prop}
             {acyclic_fragment : Graph Lab acyclic_edge}
             {G : Graph Lab edge} {root : Lab}
             {_ : @redCFG edge _ root _ acyclic_fragment} := minus_edge edge acyclic_edge.

  Infix "↪" := back_edge (at level 55).
  
  Definition loop_head `{H : redCFG} p : Prop :=
    exists q, q ↪ p.

  Lemma loop_head_dec `{H : redCFG} p : decidableT (loop_head p).
  Admitted.
  
  Definition loop_contains `{redCFG} qh q : Prop :=
    exists p, Dom root qh q /\ q -a>* p /\ p --> qh /\ back_edge p qh.

  Lemma loop_contains_dec `{redCFG} qh q : {loop_contains qh q} + {~ loop_contains qh q}.
  Admitted.

  Definition loop_contains_b `{redCFG} qh q :=
    if loop_contains_dec qh q then true else false.

  Definition exit_edge `{redCFG} (h p q : Lab) : Prop :=
    loop_contains h p /\ ~ loop_contains h q /\ p --> q.

  Definition exiting `{redCFG} (h p : Lab) : Prop :=
    exists q, exit_edge h p q.

  Definition exited `{redCFG} (h q : Lab) : Prop :=
    exists p, exit_edge h p q.

  Fixpoint preds' `{redCFG} (l : list Lab) (p : Lab) : list Lab :=
    match l with
    | nil => nil
    | q :: l => if (edge_dec p q) then q :: (preds' l p) else preds' l p
    end.

  Definition preds `{redCFG} : Lab -> list Lab := preds' all_lab.

  Program Instance loop_CFG `(G : redCFG) (h : Lab) (H : loop_head h) 
    : @redCFG _ (sub_Graph (filter (loop_contains_b h) all_lab)) h.
  Next Obligation.
   Unset Printing Notations. 

  Fixpoint implode' (G : redCFG) (l : list Lab) {struct l} : redCFG * (Lab -> option redCFG)
    := .
    
   loop_depth, loop_head

  Parameter root_no_pred0 : forall p, p ∉ preds0 root.
                 
  Parameter root : Lab.
  
  Notation "p --> q" := (p ∈ preds0 q) (at level 55, right associativity).
  
  
  (** more parameters **)
  Parameter all_lab : set Lab.
  Parameter all_lab_spec : forall l, set_In l all_lab.
  Notation "p -->? q" := (p === q \/ p --> q) (at level 70, right associativity).
  Parameter loop_exit : forall `{Graph Lab}, Lab -> list Lab.
  Parameter back_edge : Lab -> Lab -> Prop.
  Parameter back_edge_dec : forall p q, {back_edge p q} + {~ back_edge p q}.
  Parameter back_edge_incl : forall p q, back_edge p q -> p --> q.
  
  Lemma Lab_dec' : forall (l l' : Lab), { l = l' } + { l <> l'}.
  Proof.
    apply Lab_dec.
  Qed.

  Definition is_back_edge (p q : Lab) :=
    match (back_edge_dec p q) with | left _ => true | right _ => false end.
  
  Notation "p '-->*' q" := (exists π, Path p q π) (at level 70, right associativity).

  Notation "p '-a>' q" := (In p (preds q) /\ ~ back_edge p q) (at level 70).
  

  Program Instance back_edge_CFG : Graph Lab root back_edge.
  Next Obligation. apply back_edge_dec. Qed.
  Next Obligation. intro H. eapply root_no_pred'. eapply back_edge_incl; eauto. Qed.

  Definition acyclic_CFG := minus_Graph CFG back_edge_CFG.
  
  
  Parameter loop_head_dec : forall p, {loop_head p} + {~ loop_head p}.

  (** Paths **)
      
  Lemma acyclic_edge_has_edge : forall p q, p -a> q -> p --> q.
  Proof.
    intros. firstorder. 
  Qed.

  Definition acyclic_edge := (fun p q : Lab => cfg_edge p q /\ ~ back_edge p q).

  Definition AcyPath : Lab -> Lab -> ne_list Lab -> Prop := @Path _ _ acyclic_edge _. 

  Notation "p '-a>*' q" := (exists π, AcyPath p q π) (at level 70).
  
  (** Reducibility **)
  Parameter reach_acy : forall (p : Lab), root -a>* p.
  
  Parameter loop_head_dom : forall ql qh, is_back_edge ql qh = true -> Dom qh ql.

  
  Parameter loop_exit_spec : forall qh qe,
      In qh (loop_exit qe) <-> exists q, q --> qe /\ in_loop q qh /\ ~ in_loop qe qh.

  Parameter no_self_loops :
    forall q p, q --> p -> q =/= p.

  Definition CPath := @Path _ _ _ CFG.

  Definition CPath' `{Graph} π := CPath (ne_front π) (ne_back π) π.

  (** collapsed CFG **)

  Parameter depth : Lab -> nat.
  Parameter depth_spec : True. (* TODO *)

(*  Definition collapse_head (qh : Lab) := forall qe, qh ∈ exit qe -> 

  Program Instance collapsed_CFG (col_dep : nat) : Graph Lab root (fun p q : Lab => if )*)
  
End CFG.

Import CFG.


Module TCFG.

  Import CFG.

  Generalizable Variable edge.

  Definition Tag := list nat.

  Lemma Tag_dec : EqDec Tag eq.
  Proof.
    apply list_eqdec, nat_eq_eqdec.
  Qed.
  
  Parameter start_tag : Tag.
  Definition Coord : Type := (Lab * Tag).
  Definition start_coord := (root, start_tag) : Coord.
  
  Hint Unfold Coord.

  Ltac destr_let :=
    match goal with
    | [ |- context[let (_,_) := fst ?a in _]] => destruct a;unfold fst 
    | [ |- context[let (_,_) := snd ?a in _]] => destruct a;unfold snd
    | [ |- context[let (_,_) := ?a in _]] => destruct a
    end.

  Program Instance TCFG (tag : Lab -> Lab -> Tag -> Tag) :
    Graph Coord start_coord (fun c c'
                             => let (p,i) := c  in
                               let (q,j) := c' in
                               cfg_edge p q /\ tag p q i = j
                            ).
  Next Obligation.
    repeat destr_let. edestruct (@edge_dec _ _ _ CFG l l0); decide' (Tag_dec (tag l l0 t) t0);
                        firstorder.
  Qed.
  Next Obligation.
    repeat destr_let. intros [H H']. apply root_no_pred' in H. eauto.
  Qed.

  Fixpoint eff_tag p q i : Tag
    := if is_back_edge p q
       then match i with
            | nil => nil
            | n :: l => (S n) :: l
            end
       else 
         let l' := @iter Tag (@tl nat) i (length (loop_exit p)) in
         if loop_head_dec q then O :: l' else l'.

  Definition TPath := @Path _ _ _ (TCFG eff_tag).

  Lemma TPath_CPath c c' π :
    TPath c c' π -> CPath (fst c) (fst c') (ne_map fst π).
  Proof.
    intros H. dependent induction H; [|destruct b,c]; econstructor; cbn in *.
    - apply IHPath.
    - apply H0.
  Qed.            
  
  Definition TPath' `{Graph} π := TPath (ne_front π) (ne_back π) π.
  
  Parameter eff_tag_fresh : forall p q q0 i j j0 l,
      TPath (q0,j0) (q,j) l -> eff_tag q p j = i -> forall i', In (p, i') l -> i' <> i.

  Parameter eff_tag_det : forall q j p i i',
      eff_tag q p j = i ->
      eff_tag q p j = i' ->
      i = i'.
  
End TCFG.

  
    
    
          