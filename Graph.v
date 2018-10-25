
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
  Class Graph (L : Type) (root : L) (edge : L -> L -> Prop) : Type :=
    {
      L_dec : EqDec L eq;
      edge_dec : forall p q, {edge p q} + {~ edge p q};
      root_no_pred : forall p:L, ~ edge p root
    }.

  Inductive Path `{Graph} : L -> L -> ne_list L -> Prop :=
  | PathSingle a : Path a a (ne_single a)
  | PathCons {a b c π} : Path a b π -> edge b c -> Path a c (c :<: π).

  Generalizable Variable L root edge.

  Definition Dom `{Graph} p q := forall π, Path root q π -> In p π.

  Program Instance union_Graph
          {L : Type} {root : L} {edge1 edge2 : L -> L -> Prop}
          (G1 : Graph L root edge1) (G2 : Graph L root edge2)
    : Graph L root (fun p q => edge1 p q \/ edge2 p q).
  Next Obligation. apply L_dec. Qed.
  Next Obligation.
    destruct (@edge_dec _ _ edge1 _ p q), (@edge_dec _ _ edge2 _ p q); tauto.
  Qed.
  Next Obligation.
    intro H. destruct H; apply root_no_pred in H; contradiction.
  Qed.

  Program Instance minus_Graph
          {L : Type} {root : L} {edge1 edge2 : L -> L -> Prop}
          (G1 : Graph L root edge1) (G2 : Graph L root edge2)
    : Graph L root (fun p q => edge1 p q /\ ~ edge2 p q).
  Next Obligation. apply L_dec. Qed.
  Next Obligation.
    destruct (@edge_dec _ _ edge1 _ p q), (@edge_dec _ _ edge2 _ p q); tauto.
  Qed.
  Next Obligation.
    intro H. destruct H; apply root_no_pred in H; contradiction.
  Qed.

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
  
  Lemma postfix_nl_rcons {A : Type} l (a:A) :
    l :r: a = nl_rcons l a.
  Proof.
    induction l; eauto. rewrite cons_rcons_assoc. rewrite IHl. cbn. reflexivity.
  Qed.
  
  Lemma postfix_front {A : Type} (l l' : ne_list A) :
    Postfix l l'
    -> ne_front l = ne_front l'.
  Proof.
    intros H. dependent induction H.
    - apply ne_to_list_inj in x; rewrite x; eauto.
    - rewrite postfix_nl_rcons in x. apply ne_to_list_inj in x. 
      rewrite <-x. destruct l'0.
      + exfalso. inversion H; [eapply ne_to_list_not_nil|eapply rcons_not_nil]; eauto.
      + cbn. erewrite IHPostfix; eauto; [|rewrite nlcons_to_list; reflexivity]. simpl_nl; reflexivity.
  Qed.
  
  Lemma path_postfix_path `{Graph} (l l' : ne_list L) :
    Path' l
    -> Postfix l' l
    -> Path' l'.
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
  Parameter Lab_dec : EqDec Lab eq.
  Parameter preds : Lab -> list Lab.
  Notation "p --> q" := (List.In p (preds q)) (at level 55, right associativity).
  Parameter root : Lab.
  Parameter root_no_pred' : forall p, ~ p --> root.
  Definition cfg_edge p q := In p (preds q).
  (*  Parameter Lab_fin : exists l:list Lab, forall p:Lab, In p l. *)
  
  Program Instance CFG : Graph Lab root cfg_edge.
  Next Obligation.
    unfold cfg_edge. remember (preds q) as l.
    apply eq_incl in Heql.
    revert p q Heql. induction l; intros p q Heql; cbn;[tauto|].
    decide' (Lab_dec a p).
    - left;left. reflexivity.
    - apply incl_cons in Heql.
      destruct (IHl p q Heql).
      + tauto.
      + right. firstorder.
  Qed.
  Next Obligation.
    apply root_no_pred'.
  Qed.

  (** more parameters **)
  Parameter all_lab : set Lab.
  Parameter all_lab_spec : forall l, set_In l all_lab.
  Notation "p -->? q" := (p === q \/ p --> q) (at level 70, right associativity).
  Parameter Var : Type.
  Parameter Var_dec : EqDec Var eq.
  Parameter loop_exit : Lab -> list Lab.
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
  
  Definition loop_head p : Prop :=
    exists q, q --> p /\ back_edge q p.
  
  Parameter loop_head_dec : forall p, {loop_head p} + {~ loop_head p}.

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

  Definition in_loop q qh : Prop :=
    exists p, q -a>* p /\ p --> qh /\ is_back_edge p qh = true.
  
  Parameter loop_exit_spec : forall qh qe,
      In qh (loop_exit qe) <-> exists q, q --> qe /\ in_loop q qh /\ ~ in_loop qe qh.

  Parameter no_self_loops :
    forall q p, q --> p -> q =/= p.

  Definition CPath := @Path _ _ _ CFG.

  Definition CPath' `{Graph} π := CPath (ne_front π) (ne_back π) π.
  
End CFG.

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
  
End TCFG.

  
    
    
          