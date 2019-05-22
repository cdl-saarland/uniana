
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Decidable.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Bool.Bool.
Require Import Lists.ListSet.
Require Import Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Utils.

(*Require Import finiteTypes.External.
Require Import finiteTypes.BasicDefinitions.*)

Require Export FinTypes.

Require Export Graph.

(*  Notation "p '-->*' q" := (exists π, Path p q π) (at level 55, right associativity).*)

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
      loop_head_dom : forall ql qh, back_edge ql qh -> Dom edge root qh ql
      where "p -a> q" := (a_edge p q = true);
      a_edge_incl : sub_graph a_edge edge
      where "p '-a>*' q" := (exists π, Path a_edge p q π);
      a_edge_acyclic : acyclic a_edge;
      a_reachability : forall q, (exists π, Path a_edge root q π);
      loop_contains qh q := exists p π, back_edge p qh /\ Path edge q p π /\ qh ∉ tl (rev π);
      exit_edge h p q := loop_contains h p /\ ~ loop_contains h q /\ p --> q;
      single_exit : forall h p q, exit_edge h p q -> forall h', exit_edge h' p q -> h = h';
      loop_head h := exists p, back_edge p h;
      no_exit_head : forall h p q, exit_edge h p q -> ~ loop_head q;
      no_exit_branch : forall h p p' qe e, exit_edge h qe e -> e --> p -> e --> p' -> p = p' (* we need separate exits *)
    }.
    
Definition loop_containsT `{redCFG} qh q
  := {(p,π) : Lab * (ne_list Lab) | back_edge p qh /\ Path edge q p π /\ qh ∉ tl (rev π)}.

Lemma loop_containsT_inh `{C : redCFG} q qh
  : loop_contains qh q <-> inhabited (loop_containsT qh q).
Proof.
  split;intros.
  - unfold loop_contains in H. destructH. econstructor. econstructor. instantiate (1:=(p,π)). cbn. eauto. 
  - unfold loop_contains in H. destruct H. unfold loop_containsT in X.
    destruct X. destruct x. eexists;eexists; eauto.
Qed.

Notation "p '-a>b' q" := ((fun (Lab : finType)
                             (a_edge : Lab -> Lab -> bool)
                             (_ : redCFG Lab _ _ a_edge) => a_edge) _ _ _ p q)
                           (at level 55).

Notation "p '-a>' q" := (p -a>b q = true) (at level 55).

Notation "p '-->b' q" := ((fun (Lab : finType)
                           (edge : Lab -> Lab -> bool)
                           (root : Lab)
                           (a_edge : Lab -> Lab -> bool)
                           (_ : @redCFG Lab edge _ _) => edge) _ _ _ _ _ p q) (at level 55).

Notation "p '-->' q" := (p -->b q = true) (at level 55, right associativity).

Notation "p '-->*' q" := ((fun (Lab : finType)
                             (edge : Lab -> Lab -> bool)
                             (root : Lab)
                             (a_edge : Lab -> Lab -> bool)
                             (_ : @redCFG Lab edge root a_edge)
                             (p q : Lab)
                           => exists π, Path edge p q π) _ _ _ _ _ p q)
                           (at level 55, right associativity).

Notation "p '-a>*' q" := ((fun (Lab : finType)
                             (edge : Lab -> Lab -> bool)
                             (root : Lab)
                             (a_edge : Lab -> Lab -> bool)
                             (_ : @redCFG Lab edge root a_edge)
                             (p q : Lab)
                           => exists π, Path a_edge p q π) _ _ _ _ _ p q) (at level 55).

Infix "↪" := back_edge (at level 55).


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
  end.

Section red_cfg.

  Definition CPath `{redCFG} := Path edge.

  Context `{C : redCFG}.
  
  Global Instance Lab_dec : EqDec Lab eq.
  Proof.
    intros x y. destruct (decide_eq x y).
    - left. rewrite e. reflexivity.
    - right. eauto.
  Qed.

  Lemma reachability (q : Lab) : exists π : ne_list Lab, Path edge root q π.
  Proof.
    specialize (a_reachability q) as Hreach. destructH. exists π. eapply subgraph_path';eauto. eapply a_edge_incl.
  Qed.

  Definition CPath' π := CPath (ne_back π) (ne_front π) π.

  Lemma cpath_cpath' r p t
        (Hpath : CPath r p t)
    : CPath' t.
  Proof.
    unfold CPath'. eapply path_back in Hpath as Hback.
    eapply path_front in Hpath as Hfront.
    rewrite Hfront,Hback. assumption.
  Qed.

  (** decidable properties on redCFG **)
  
  Lemma loop_head_dec p : dec (loop_head p).
    eauto.
  Qed.

(*  Definition loop_head_b p : bool := to_bool (loop_head_dec p).
  Lemma loop_head_spec : forall p : Lab, loop_head_b p = true <-> loop_head p.
    prove_spec.
  Qed.*)

  Instance ne_list_eq_dec (A : Type) : eq_dec A -> eq_dec (ne_list A).
  Proof.
    intros H l.
    induction l; intro l'; induction l'.
    - decide (a = a0); subst;[left|right];eauto. contradict n. inversion n;eauto.
    - right. intro N; inversion N.
    - right. intro N; inversion N.
    - decide (a = a0).
      + subst. destruct (IHl l').
        * subst. left. reflexivity.
        * right. intro N; inversion N. congruence.
      + right. intro N; inversion N. congruence.
  Qed.

  Definition EqNeList (X : eqType) := EqType (ne_list X).

  Global Instance loop_contains_dec qh q : dec (loop_contains qh q).
    unfold loop_contains. eauto.
    eapply finType_exists_dec. intros.
    (* proof idea : consider only dupfree paths, there are only finitely many of them. *)
  Admitted.
  Hint Resolve loop_contains_dec.
  
(*  Definition loop_contains_b qh q := to_bool (loop_contains_dec qh q).

  Lemma loop_contains_spec : forall qh q, loop_contains_b qh q = true <-> loop_contains qh q.
  Proof.
    intros. unfold loop_contains_b. destruct (loop_contains_dec qh q); cbn; split;eauto.
    intro. congruence.
  Qed.*)

  Lemma back_edge_incl (p q : Lab) (Hback : p ↪ q) : edge p q = true.
  Proof. 
    unfold back_edge,back_edge_b in Hback. eapply minus_subgraph. eauto.
  Qed.
  
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
      eapply back_edge_incl in H as Hreach. specialize (reachability x) as Hreach'.
      destructH.
      eapply Hdom in Hreach' as Hreach''. eapply path_from_elem in Hreach'; eauto.
      destructH; eauto.
      eapply path_NoDup' in Hreach'0;eauto. 
      destructH. exists x, π0. firstorder;eauto.
  Admitted.

  Definition deq_loop q p : Prop :=
    forall h, loop_contains h p -> loop_contains h q.

  Global Instance deq_loop_dec h p : dec( deq_loop h p).
    unfold deq_loop. eapply finType_forall_dec. intros.
    eapply impl_dec; eapply loop_contains_dec.
  Qed.

  Definition deq_loop_b h p
    := to_bool (deq_loop_dec h p).
  
  Lemma deq_loop_spec : forall h p, deq_loop_b h p = true <-> deq_loop h p.  
  Proof.
    prove_spec.
  Qed.
  
  Lemma deq_loop_refl l :
    deq_loop l l.
  Proof.
    unfold deq_loop;firstorder.
  Qed.

  Global Instance exit_edge_dec : forall h p q, dec (exit_edge h p q).
  Proof.
    eauto.
  Qed.
  
  (*Definition exit_edge_b h p q : bool := to_bool (exit_edge_dec h p q).
  Lemma exit_edge_b_spec : forall h p q, exit_edge_b h p q = true <-> exit_edge h p q.
  Proof.
    prove_spec.
  Qed.    *)

  
  Instance decide_decPred_bool (A : Type) (f : A -> bool) a : dec (if f a then True else False).
  Proof.
    cbn. destruct (f a); eauto.
  Qed.
  
  
  Definition decPred_bool (A : Type) (f : A -> bool) := DecPred (fun a => if f a then True else False).
   
  Definition finType_sub_decPred (X : finType) (p : decPred X) : finType.
  Proof.
    eapply (@finType_sub X p). eapply decide_pred. 
  Defined.
(*
  Definition finType_sub_bool (X : finType) (p : X -> bool) : finType.
  Proof.
    eapply (@finType_sub X (decPred_bool p)). eauto. Show Proof.
  Defined.
  *)
  Definition depth (p : Lab) := length (filter (DecPred (fun h => loop_contains h p)) (elem Lab)). 
  
  Definition innermost_loop h p : Prop := loop_contains h p /\ deq_loop h p.

  Definition innermost_loopT h p : Type := loop_containsT h p * deq_loop h p.

  Definition containing_loops (p : Lab) := filter (DecPred (fun h => loop_contains h p)) (elem Lab).

  
  Definition finType_sig_or_never (X : finType) (P : decPred X) : {x : X | P x} + {forall x : X, ~ P x}.
  Proof.
    remember (filter P (elem X)).
    destruct l.
    - right. intros ? ?. specialize (in_filter_iff P x (elem X)) as Hiff. rewrite <-Heql in Hiff.
      cbn in Hiff. eapply Hiff. split;eauto.
    - left. econstructor. specialize (in_filter_iff P e (elem X)) as Hiff.
      rewrite <-Heql in Hiff. cbn in Hiff. eapply Hiff. eauto.
  Qed.
  
  Definition ex_innermost_loop p
    := finType_sig_or_never (DecPred (fun h => innermost_loop h p)).

  Definition innermost_loop_strict (h p : Lab)
    := loop_contains h p /\ h <> p /\ forall h', loop_contains h' p -> (loop_contains h' h \/ h' = p).
  
  Definition innermost_loop_strictT (h p : Lab) 
    := (loop_containsT h p * (h <> p) * forall h', loop_containsT h' p -> (loop_containsT h' h + (h' = p)))%type.
    
  Definition ex_innermost_loop_strict (p : Lab)
    : {h : Lab | innermost_loop_strict h p} + {forall h, ~ innermost_loop_strict h p}
    := finType_sig_or_never (DecPred (fun h => innermost_loop_strict h p)).
  
(*  Definition get_innermost_loop_strict (p : Lab) : option Lab :=
    match inner_most_loop_ex p with
    | inleft (exist _ h H) => Some h
    | inright _ => None
    end.*)
  (* TODO: maybe switch to the non-dependent version above *)
  Definition get_innermost_loop_strict (p : Lab) : option {h : Lab | loop_contains h p} :=
    match ex_innermost_loop_strict p with
    | inleft (exist _ h H) => Some (exist _ h (match H with
                                              | conj Q _ => Q
                                              end))
    | inright _ => None
    end.
  
  Lemma dec_DM_and_iff (X Y : Prop) : dec X -> ~ (X /\ Y) <-> ~ X \/ ~ Y.
    split;[now eapply dec_DM_and|firstorder].
  Qed.
  Lemma dec_DM_and_iff' (X Y : Prop) : dec Y -> ~ (X /\ Y) <-> ~ X \/ ~ Y.
    split;[now eapply dec_DM_and'|firstorder].
  Qed.
  Lemma dec_DN_iff (X : Prop) : dec X -> ~ ~ X <-> X.
    split;[now eapply dec_DN|firstorder].
  Qed.
  Lemma dec_DM_impl_iff (X Y : Prop) : dec X -> dec Y -> ~ (X -> Y) <-> X /\ ~ Y.
    split;[now eapply dec_DM_impl|firstorder].
  Qed.

  Ltac simpl_dec' H :=
     (first [(setoid_rewrite (DM_notAll _) in H;eauto)|
             (setoid_rewrite (dec_DM_and_iff _ _) in H;eauto)|
              (setoid_rewrite (dec_DM_and_iff' _ _) in H;eauto)|
              setoid_rewrite DM_not_exists in H|
              setoid_rewrite DM_or in H|
              (setoid_rewrite (dec_DN_iff _) in H;eauto)|
              (setoid_rewrite (dec_DM_impl_iff _ _) in H;eauto)]).
  Ltac simpl_dec :=
    (try (setoid_rewrite DM_notAll;[|eauto]);
     try (setoid_rewrite (dec_DM_and_iff _ _);[|eauto]);
     try (setoid_rewrite (dec_DM_and_iff' _ _);[|eauto]);
     try setoid_rewrite DM_not_exists;
     try setoid_rewrite DM_or;
     try (setoid_rewrite (dec_DN_iff _);[|eauto]);
     try (setoid_rewrite (dec_DM_impl_iff _ _);eauto)).

  Ltac collapse H :=
    lazymatch type of H with
    | ?a /\ ?b => let H1 := fresh "H" in
                let H2 := fresh "H" in
                destruct H as [H1 H2];
                collapse H1;
                collapse H2
    | ?a \/ ?b => destruct H as [H|H]; collapse H
    | ~ ?x => simpl_dec' H; collapse H
    | _ => idtac
    end.

(*  Require Import Coq.Classes.Morphisms_Prop.*)

  Goal forall (X : finType) (P Q : X -> Prop), (forall x, dec (P x)) -> (forall x, dec (Q x)) -> ~ (forall x, P x \/ Q x) -> False.
    intros. (*setoid_rewrite (DM_notAll _) in H.*) (*evar (forall x, P x \/ Q x).*)
    simpl_dec' H.
  Abort.

  
  Definition get_innermost_loop (p : Lab) : option {h : Lab | loop_contains h p} :=
    match ex_innermost_loop p with
    | inleft (exist _ h H) => Some (exist _ h (match H with
                                              | conj Q _ => Q
                                              end))
    | inright _ => None
    end.

(*  Inductive loop_chain : ne_list Lab -> Prop :=
  | LoopChainSingle (p : Lab) : loop_chain (ne_single p)
  | LoopChainCons (h1 h2 : Lab) l :
      innermost_loop_strict h1 h2 -> loop_chain (h2 :<: l) -> loop_chain (h1 :<: h2 :<: l).

  Definition loop_chain_of (p : Lab) l := loop_chain l /\ p = ne_back l.*)

  Definition LPath := Path (fun h p => decision (innermost_loop_strict h p)).

  Lemma loop_contains_trans h h' p
        (Hloop : loop_contains h h')
        (Hloop' : loop_contains h' p)
    : loop_contains h p.
  Proof.
    unfold loop_contains in *. destructH. destructH.
  Admitted.

  Lemma nin_tl_iff (A : Type) `{EqDec A eq} (a : A) (l : ne_list A)
    : a ∉ tl (rev l) -> a ∉ l \/ a = ne_back l.
  Proof.
    intros.
    decide' (a == ne_back l);eauto.
    left. contradict H0. induction l;cbn in *;eauto.
    - destruct H0;eauto. congruence.
    - fold (rcons (rev l) a0).
      rewrite tl_rcons;[eapply In_rcons;eauto|destruct l;cbn;eauto;erewrite app_length;cbn;omega].
      destruct H0.
      + subst. eauto.
      + right. eapply IHl;eauto.
  Qed.

  Lemma loop_reachs_member (h q : Lab)
    : loop_contains h q -> h -->* q.
  Proof.
    intros Hloop. unfold loop_contains in Hloop.
    destructH. eapply nin_tl_iff in Hloop3;[|eauto].
    erewrite path_back in Hloop3;eauto.
    destruct Hloop3;[|subst q; eexists; econstructor].
    specialize (reachability q) as H'. destructH. eapply loop_head_dom in Hloop0.
    eapply path_app in Hloop2;eauto. eapply Hloop0 in Hloop2. eapply in_nl_conc in Hloop2.
    destruct Hloop2;[contradiction|].
    assert (h ∈ π0).
    { destruct π0; cbn in *;[contradiction|right;eauto]. }
    eapply path_from_elem in H1;eauto. firstorder. 
  Qed.

  Lemma edge_head_same_loop p h h'
        (Hedge : edge p h = true)
        (Hhead : loop_head h)
        (Hloop : loop_contains h' p)
    : loop_contains h' h.
  Proof.
    eapply no_exit_head in Hhead;[contradiction|].
  Admitted.

  Lemma edge_innermost:
    forall a b : Lab,
      edge b a = true -> loop_head a -> forall h' : Lab, loop_contains h' a -> loop_contains h' b \/ h' = a.
  Proof.
    intros a b Hedge Hhead. intros.  
  Admitted.

  Lemma prefix_induction {A : Type} {P : list A -> Prop}
    : P nil
      -> (forall (a : A) (l : list A) (l' : list A), P l' -> Prefix (a :: l') l -> P l)
      -> forall l : list A, P l.
  Proof.
    intros Hbase Hstep l. induction l;eauto.
    eapply Hstep;eauto. econstructor.
  Qed.


(*  Lemma prefix_ne_induction {A : Type} (P : ne_list A -> Prop)
    : forall (l : ne_list A), ((forall (a : A) (l' : ne_list A), Prefix (a :<: l') l -> P l') -> P l)
      -> P l.
  Proof.
    intros l Hstep.
    induction l.
    - eapply Hstep. intros. exfalso. inversion H;subst. destruct l';subst;cbn in *; congruence. inversion H2.
    - eapply Hstep. intros. 
    eapply Hstep. intros. 
    induction l;eauto.
    eapply Hstep;eauto. econstructor.
  Qed.*)

  Lemma find_some' (A : Type) (f : A -> bool) (l : list A) (x : A)
        (Hl : x ∈ l)
        (Hf : f x = true)
    : exists y, Some y = find f l.
  Proof.
    induction l;cbn;[contradiction|].
    destruct Hl;subst.
    - rewrite Hf. eauto.
    - destruct (f a);eauto.
  Qed.

  Lemma path_contains_front {L : Type} (x y : L) e l
        (Hpath : Path e x y l)
    : y ∈ l.
  Proof.
    induction Hpath; cbn; eauto.
  Qed.
  
  Lemma path_contains_back {L : Type} (x y : L) e l
        (Hpath : Path e x y l)
    : x ∈ l.
  Proof.
    induction Hpath; cbn; eauto.
  Qed.

  Instance loop_contains_Antisymmetric : Antisymmetric Lab eq loop_contains.
  Proof.
    unfold Antisymmetric.
    intros.
    specialize (a_reachability x) as Hx.
    specialize (a_reachability y) as Hy.
    (* acyclic reachability in on x & y, then dom_loop_acyclic on both thus x -a>* y /\ y -a>* x, contradiction *)
  Admitted.

  Lemma innermost_loop_strict_unique (h h' p : Lab)
        (H : innermost_loop_strict h p)
        (Q : innermost_loop_strict h' p)
    : h = h'.
  Proof.
    unfold innermost_loop_strict in *. do 2 destructH.
    eapply H3 in Q0. destruct Q0;[|contradiction].
    eapply Q3 in H0. destruct H0;[|contradiction].
    eapply loop_contains_Antisymmetric;auto.
  Qed.

  Definition StrictPrefix' := 
    fun (A : Type) (l l' : ne_list A) => exists a : A, Prefix (a :<: l) l'.

  Lemma prefix_strictPrefix:
    forall (e : Lab) (x ϕ : ne_list Lab), Prefix ϕ x -> StrictPrefix' ϕ (e :<: x).
  Proof.
    intros e x ϕ Hϕ1.
    unfold StrictPrefix'. cbn.
    revert dependent e.
    induction Hϕ1; intros.
    - exists e; econstructor.
    - specialize(IHHϕ1 a). destructH. exists a0. econstructor. auto.
  Qed.

  Lemma StrictPrefix_well_founded (A : Type) : well_founded (@StrictPrefix' A).
  Proof.
    unfold well_founded.
    intros. 
    induction a.
    - econstructor. intros. unfold StrictPrefix' in *. destructH. inversion H;[congruence'|]. inversion H2.
    - constructor. intros.
      unfold StrictPrefix' in H.
      destructH. cbn in *. inversion H;subst.
      + eapply ne_to_list_inj in H3. subst. auto.
      + eapply IHa. unfold StrictPrefix'. exists a1. cbn. auto.
  Qed.
  
  Lemma root_loop_root h
    : loop_contains h root -> h = root.
  Admitted.

  Lemma dom_dom_acyclic r p q
    : Dom edge r p q -> Dom a_edge r p q.
  Proof.
    intros. unfold Dom in *. intros. apply H. eapply subgraph_path'; eauto using a_edge_incl.
  Qed.

  Lemma dom_loop h
    : forall q: Lab, loop_contains h q -> Dom edge root h q.
  Proof.
    intros q Hq. unfold loop_contains,CPath in *. intros π Hπ.
    destructH. 
    eapply nin_tl_iff in Hq3;eauto.
    erewrite path_back in Hq3;eauto.
    eapply path_app in Hq2; eauto.
    eapply loop_head_dom in Hq2;eauto. eapply in_nl_conc in Hq2.
    destruct Hq3;[|subst h;eapply path_front in Hπ; subst q; destruct π;cbn;eauto].
    destruct Hq2;[contradiction|]. clear - H0. destruct π; cbn in *; eauto.
  Qed.

  Lemma find_some_strong (A : Type) `{Q:EqDec A eq} (f : A -> bool) (l : list A) (x : A) (Hnd : NoDup l)
    : find f l = Some x -> x ∈ l /\ f x = true /\ forall y, y ≻* x | l -> f y = true -> x = y.
  Proof.
    repeat split. 1,2: eapply find_some in H; firstorder.
    revert dependent x.
    induction l;intros.
    - inversion H0.
    - cbn in H.
      destruct (f a) eqn:E.
      + inversion H; subst. inversion H0;subst;auto.
        inversion Hnd; subst. exfalso; contradict H5. eapply splinter_incl;[eapply H4|]. firstorder 0.
      + destruct (a == y);[rewrite e in E;congruence|].
        inversion Hnd; subst. eapply IHl;eauto. inversion H0;subst;auto. congruence.
  Qed.

  Lemma loop_contains_either h1 h2 h3
        (Hloop1 : loop_contains h1 h3)
        (Hloop2 : loop_contains h2 h3)
    : loop_contains h1 h2 \/ loop_contains h2 h1.
  Admitted.


  
  Definition exiting (h p : Lab) : Prop :=
    exists q, exit_edge h p q.

  Definition exited (h q : Lab) : Prop :=
    exists p, exit_edge h p q.

  Global Instance exited_dec (h q : Lab) : dec (exited h q).
  Proof.
    eauto.
  Qed.

  Definition preds `{redCFG Lab edge} p : list Lab := filter (decPred_bool (fun q => edge q p)) (elem Lab). 

  Definition In_b {A : Type} `{H : EqDec A eq} (a : A) (l : list A)
    := if in_dec H a l then true else false.


  Lemma back_edge_dec p q : dec (p ↪ q).
  Proof.
    unfold back_edge, back_edge_b, minus_edge.
    destruct (edge p q), (a_edge p q);cbn;firstorder.
  Qed.

  Hint Resolve back_edge_dec.

  (** simple propositions **)

(*  Lemma path_in_alllab1 p q :
    p <> q -> p -->* q -> p ∈ all_lab.
  Proof.
    intros Hneq Hpath.
    destruct Hpath. revert dependent q.
    induction x; intros q Hneq Hpath; inversion Hpath;[contradiction|subst].
    decide (p = b);subst.
    - eapply edge_incl1;eauto.
    - eapply IHx;eauto.
  Qed.*)
  
(*  Lemma path_in_alllab2 p q :
    p <> q -> p -->* q -> q ∈ all_lab.
  Proof.
    intros Hneq Hpath.
    destruct Hpath. inversion H; [contradiction|eapply edge_incl2;eauto].
  Qed.*)


  Lemma minus_back_edge edge' p q
    : ((edge ∩ edge') ∖ (a_edge ∩ edge')) p q = true -> p ↪ q.
  Proof.
    intros Q.
    unfold minus_edge,intersection_edge in Q. rewrite negb_andb in Q. conv_bool.
    unfold back_edge,back_edge_b.
    destruct Q as [[Q1 Q2] Q34]. unfold minus_edge. rewrite Q1; cbn. destruct Q34; eauto.
    rewrite Q2 in H; cbn in H; congruence.
  Qed.

  Lemma dom_path p q
    : Dom edge root p q -> p -->* q.
  Proof.
    intros Hdom.
    specialize reachability as [π Hπ]. specialize (Hdom π Hπ).
    eapply path_from_elem in Hπ; eauto using Lab_dec. firstorder.
  Qed.

  Lemma loop_contains_not_dom h q 
    : loop_contains h q -> h <> q -> exists p, p ↪ h /\ ~ Dom edge q h p.
  Proof.
    intros Hloop Hneq. unfold loop_contains in Hloop. destructH.
    unfold Dom; eexists; firstorder; eauto.
    intros H0.
    eapply nin_tl_iff in Hloop3;eauto. erewrite path_back in Hloop3;eauto.
    destruct Hloop3;[|subst q;contradiction]. apply H,H0. eauto.
  Qed.

  Lemma DM_not_exists X (p : X -> Prop) :
    ~ (exists x, p x) <-> forall x, ~ p x.
  Proof.
    firstorder.
  Qed.

  Lemma not_and_iff (A B : Prop) : decidable A -> (~ (A /\ B) <-> ~ A \/ ~ B).
  Proof.
    firstorder.
  Qed.

  Lemma in_tl_in {A : Type} (a : A) (l : list A) : a ∈ tl l -> a ∈ l.
  Proof.
    destruct l; cbn in *; eauto.
  Qed.

  Lemma dom_loop_contains h p q
    : loop_contains h q -> ~ loop_contains h p -> Dom edge p h q.
  Proof.
    intros Hloop Hnloop.
    decide (p = q); [subst;contradiction|].
    unfold loop_contains in Hloop. destructH.
    eapply nin_tl_iff in Hloop3;eauto; erewrite path_back in Hloop3;eauto.
    destruct Hloop3 as [Hloop3|Hloop3];[|subst q;eapply dominant_self]. rename π into π1.
    intros π Hπ.
(*    assert (p ∈ all_lab) as H0 by (eapply path_in_alllab1;eauto).*)
    specialize reachability as Hϕ.
    unfold loop_contains in Hnloop.
    rewrite DM_not_exists in Hnloop. setoid_rewrite DM_not_exists in Hnloop.
    eapply path_app in Hloop2;eauto.
    specialize (Hnloop p0 (π1 :+ tl π)).
    setoid_rewrite not_and_iff in Hnloop; [setoid_rewrite not_and_iff in Hnloop|].
    - destruct Hnloop as [Hnloop|Hnloop]; [contradiction|destruct Hnloop].
      + contradiction.
      + clear - Hloop3 H.
        eapply not_not in H.
        * eapply in_tl_in in H. eapply in_rev in H. eapply in_nl_conc in H. destruct H;[contradiction|].
          eapply in_tl_in;eauto.
        * eapply In_dec.
    - edestruct path_dec;eauto; firstorder.
    - edestruct (back_edge_dec p0 h); firstorder.
      Unshelve. all:eauto. (*TODO: remove *)
  Qed.
  
  Lemma NoDup_rcons (A : Type) (x : A) (l : list A)
    : x ∉ l -> NoDup l -> NoDup (l :r: x).
  Proof.
    intros Hnin Hnd. revert x Hnin.
    induction Hnd; intros y Hnin; cbn.
    - econstructor; eauto. econstructor.
    - econstructor.
      + rewrite in_app_iff. contradict Hnin. destruct Hnin; [contradiction|firstorder].
      + eapply IHHnd. contradict Hnin. right; assumption.
  Qed.

  Lemma NoDup_nin_rcons (A : Type) (x : A) (l : list A)
    : NoDup (l :r: x) -> x ∉ l.
  Proof.
    intros Hnd Hin.
    dependent induction l.
    - destruct Hin.
    - destruct Hin; rewrite cons_rcons_assoc in Hnd; inversion Hnd.
      + subst a. eapply H2. apply In_rcons;firstorder.
      + eapply IHl; eauto.
  Qed.
  
  Lemma loop_contains_path h q π
    : CPath h q π -> loop_contains h q -> NoDup π -> forall p, p ∈ π -> loop_contains h p.
  Proof.
    intros Hπ Hin Hnd p Hp. 
    decide (p = h) as [Hph|Hph].
    - rewrite Hph. eapply loop_contains_self. eapply loop_contains_loop_head; eauto.
    - destruct (loop_contains_dec h p) as [N|N]; [eauto|exfalso].
      eapply path_from_elem in Hp; eauto. destructH.
      eapply dom_loop_contains in N; eauto; cycle 1.
      eapply postfix_incl in Hp1 as Hp1'; eauto.
      dependent induction Hp1.
      + simpl_nl' x. subst ϕ. 
        eapply Hph. eapply path_back in Hp0; eapply path_back in Hπ. rewrite <-Hp0. eauto.
      + clear IHHp1. unfold Dom in N.
        eapply postfix_incl in Hp1. eapply Hp1 in N; eauto.
        rewrite rcons_nl_rcons in x. eapply ne_to_list_inj in x. rewrite <-x in Hnd.
        eapply f_equal with (f:=ne_back) in x. simpl_nl' x. eapply path_back in Hπ. rewrite Hπ in x.
        subst a.
        eapply NoDup_nin_rcons; eauto. rewrite rcons_nl_rcons. assumption.
  Qed.

  Lemma loop_contains_splinter h1 h2 p π
        (Hloop1 : loop_contains h1 h2)
        (Hloop2 : loop_contains h2 p)
        (Hpath : Path edge root p π)
    : h2 ≻* h1 | π.
  Proof.
    eapply dom_loop in Hloop2. eapply Hloop2 in Hpath as Hin.
    eapply path_to_elem in Hin;eauto. destructH.
    eapply splinter_prefix;eauto.
    inversion Hin0;subst h2 a.
    - eapply dom_loop in Hloop1. eapply Hloop1 in Hin0. rewrite <-H1 in Hin0. inversion Hin0;subst;[|contradiction].
      econstructor. econstructor. econstructor. econstructor.
    - cbn in *. econstructor. eapply dom_loop in Hloop1. eapply Hloop1 in Hin0. rewrite <-H3 in Hin0.
      eapply splinter_single. cbn in *; eauto.
  Qed.
  
  Lemma loop_LPath_helper p h π
        (Hpath : Path a_edge root p (p :<: π))
        (Hloop : loop_contains h p)
        (Hin : h ∈ π)
        (Hnolo : forall q : Lab, q ≻* h | π -> toBool _ (D:=decision (loop_contains q p)) = true -> h = q)
    : (forall h' : Lab, loop_contains h' p -> loop_contains h' h \/ h' = p).
  Proof.
    intros. eapply loop_contains_either in H as H';[|apply Hloop].
    destruct H';[|left;auto].
    decide (h' = p);[right;auto|]. 
    specialize (Hnolo h'). exploit Hnolo.
    - eapply subgraph_path' in Hpath;eauto using a_edge_incl.
      eapply loop_contains_splinter in Hpath;eauto.
      cbn in Hpath. inversion Hpath;subst;auto. inversion H2;subst;contradiction.
    - decide (loop_contains h' p); cbn in *;[congruence|contradiction].
    - subst. left. eapply loop_contains_self. eapply loop_contains_loop_head;eauto.
  Qed.
      
  Lemma acyclic_path_NoDup p q π
        (Hπ : Path a_edge p q π)
    : NoDup π.
  Proof.
    induction Hπ.
    - econstructor;eauto. econstructor.
    - cbn. econstructor;auto.
      intro N. specialize a_edge_acyclic as Hacy. unfold acyclic in Hacy.
      simpl_dec' Hacy.
      specialize (Hacy _ _ H).
      eapply path_from_elem in N;eauto. destructH. apply Hacy in N0. contradiction.
  Qed.
  
  Lemma loop_LPath h p
        (Hloop : loop_contains h p)
    : exists π, LPath h p π.
  Proof.
    specialize (a_reachability p) as Hreach.
    destructH. revert dependent p. revert dependent π. 
    specialize (well_founded_ind (R:=(@StrictPrefix' Lab)) (@StrictPrefix_well_founded Lab)
                                 (fun π : ne_list Lab => forall p, loop_contains h p
                                                           -> Path a_edge root p π
                                                           -> exists (π0 : ne_list Lab), LPath h p π0))
      as WFind.
    eapply WFind.
    intros;clear WFind.
    destruct x.
    - inversion H1; subst p a e.
      eapply root_loop_root in H0. subst. repeat econstructor.
    - remember (find (fun h' => decision (loop_contains h' p)) x) as S.
      destruct S; symmetry in HeqS.
      + eapply find_some_strong in HeqS. destructH. decide (loop_contains e0 p);cbn in *;[|congruence].
        inversion H1;subst.
        decide (h = e).
        { subst;eexists;econstructor. }
        specialize (path_to_elem _ a_edge _ _ e0 x H6 HeqS0) as [ϕ [Hϕ0 Hϕ1]].
        specialize (H ϕ). exploit' H.
        { cbn. clear - Hϕ1.
          eapply prefix_strictPrefix;auto.
        } 
        specialize (H e0). exploit H.
        { clear - l H0 n HeqS0 HeqS3 H1.
          decide (e0 = h);[subst;eapply loop_contains_self;unfold loop_contains in H0;firstorder|].
          eapply loop_contains_either in H0 as H0'; eauto.
          destruct H0';[exfalso|auto].
          eapply (loop_LPath_helper) in HeqS3;auto. 2:exact H0. destruct HeqS3;[|contradiction].
          eapply loop_contains_Antisymmetric in H. exploit H. contradiction.
        } 
        destructH.        
        exists (e :<: π0).
        econstructor;cycle 1.
        * instantiate (1:=e0). decide (innermost_loop_strict e0 e);cbn;[auto|exfalso;contradict n0].
          unfold innermost_loop_strict. split;auto. split.
          -- eapply acyclic_path_NoDup in H1. clear - HeqS0 H1. inversion H1; subst.
             contradict H2. subst. auto.
          -- eapply loop_LPath_helper;eauto.
        * auto.
        * auto.
        * inversion H1;subst. eapply acyclic_path_NoDup; eauto.
      + decide (h = e); subst.
        { inversion H1. subst. repeat econstructor. }
        eapply find_none in HeqS;cycle 1.
        * instantiate (1:=h).
          enough (h ∈ (e :<: x)) as Hex.
          { destruct Hex;[symmetry in H2;contradiction|auto]. }
          eapply dom_dom_acyclic;eauto. eapply dom_loop;auto.
        * exfalso. decide (loop_contains h p); cbn in *; [congruence|contradiction].
  Qed.    
  
  Lemma loop_contains_innermost (h p : Lab)
        (Hloop : loop_contains h p)
    : exists h', innermost_loop h' p.
  Proof.
    unfold innermost_loop.
    eapply loop_LPath in Hloop as Hloop'. destructH.
    decide (loop_head p).
    + exists p. split;eauto using loop_contains_self. unfold deq_loop; firstorder.
    + inversion Hloop'. subst.
      * exists p. split;eauto using loop_contains_self. unfold deq_loop; firstorder.
      * subst. exists b.
        decide (innermost_loop_strict b p);cbn in *;[|congruence]. unfold innermost_loop_strict in i.
        clear - i n. destructH. unfold deq_loop.
        split;auto. intros. exploit i3. destruct i3;auto.
        subst. eapply loop_contains_loop_head in H. contradiction.
  Qed.

  Lemma loop_contains_innermost_strict (h p : Lab)
        (Hloop : loop_contains h p)
        (Hneq : h <> p)
    : exists h', innermost_loop_strict h' p.
  Proof.
    eapply loop_LPath in Hloop as Hloop'. destructH.
    inversion Hloop';subst;eauto;[contradiction|].
    exists b. decide (innermost_loop_strict b p);cbn in *;[auto|congruence].
  Qed.
  
  Lemma get_innermost_loop_spec
    : forall p : Lab,
      match get_innermost_loop p with
      | Some (exist _ h _) => innermost_loop h p
      | None => forall h' : Lab, loop_contains h' p -> False
      end.
  Proof.
    unfold get_innermost_loop.
    intro. destruct (ex_innermost_loop p).
    - destruct s;eauto.
    - cbn in n. unfold innermost_loop in n. intros.
      eapply loop_contains_innermost in H. clear h'. destructH.
      specialize (n h'). eapply dec_DM_and in n;eauto.
      destruct n;unfold innermost_loop in H;firstorder.
  Qed.

  Lemma get_innermost_loop_strict_spec (p : Lab)
    : match get_innermost_loop_strict p with
      | Some (exist _ h H) => innermost_loop_strict h p
      | None => forall h', loop_contains h' p -> h' = p
      end.
  Proof.
    unfold get_innermost_loop_strict.
    destruct (ex_innermost_loop_strict p); cbn.
    - destruct s. eauto.
    - intros. 
      decide (h' = p);[eauto|].
      eapply loop_contains_innermost_strict in H;eauto.
      destructH. specialize (n h'0); contradiction.
  Qed. 
  
  Lemma deq_loop_trans p q r
        (H1 : deq_loop p q)
        (H2 : deq_loop q r)
    : deq_loop p r.
  Proof.
    unfold deq_loop in *. intros. eapply H1,H2;eauto.
  Qed.

  Program Instance deq_loop_PreOrder : PreOrder deq_loop.
  Next Obligation.
    unfold Reflexive. eapply deq_loop_refl.
  Qed.
  Next Obligation.
    unfold Transitive; eapply deq_loop_trans.
  Qed.

  Lemma innermost_loop_deq_loop h p q
        (Hinner : innermost_loop h p)
        (Hloop : loop_contains h q)
    : deq_loop q p.
  Proof.
  Admitted.

  Lemma deq_loop_exited h qe e
        (Hexit : exit_edge h qe e)
    : deq_loop qe e.
  Proof.
    unfold exit_edge in *. unfold deq_loop. intros.
  Admitted.
  
  Lemma deq_loop_exiting h qe e
        (Hexit : exit_edge h qe e)
    : deq_loop h qe.
  Proof.
    unfold exit_edge, deq_loop. intros. eapply single_exit in Hexit.
  Admitted.
  
  Lemma loop_contains_deq_loop h p
        (Hloop : loop_contains h p)
    : deq_loop p h.
  Proof.
    unfold deq_loop. intros. eapply loop_contains_trans;eauto.
  Qed.
  (** ancestors **)

  Definition ancestor a p q :=
    loop_contains a p /\ loop_contains a q \/ a = root .

  Definition near_ancestor  a p q :=
    ancestor a p q /\ forall a', ancestor a p q -> deq_loop a a'.

  Lemma ex_near_ancestor p q
    : exists a, near_ancestor a p q.
    (* choose either a common head or root if there is no such head *)
  Admitted.
  
  Lemma ancestor_dom1 a p q
    : ancestor a p q -> Dom edge root a p.
  Admitted.

  Lemma ancestor_sym a p q
    : ancestor a p q -> ancestor a q p.
  Proof.
    unfold ancestor;firstorder 0.
  Qed.
  
  Lemma ancestor_dom2 a p q
    : ancestor a p q -> Dom edge root a q.
  Proof.
    eauto using ancestor_dom1, ancestor_sym.
  Qed.

  (** loop_CFG: remove everything outside the loop **)


  Lemma loop_contains_ledge_head h h' p
    : loop_contains h p -> p ↪ h' -> loop_contains h h'.
  Proof.
  Admitted.
  
  Definition finType_sub_elem (h : Lab) (p : decPred Lab) : p h -> finType_sub_decPred p.
    intros H.
    econstructor. unfold pure. instantiate (1 := h). decide (p h);eauto.
  Defined.

  Open Scope prg.

  Definition restrict_edge (f : Lab -> Lab -> bool) (p : decPred Lab)
    : let L' := finType_sub_decPred p in L' -> L' -> bool
    := fun x y => (f (`x) (`y)).

  Definition loop_nodes (h : Lab) := DecPred (fun p => loop_contains h p \/ exited h p).

(*  Lemma loop_edge_h_invariant (h : Lab) (H : loop_head h) : loop_nodes h h.
  Proof.
    unfold loop_nodes. cbn. now eapply loop_contains_self. 
  Qed.*)

End red_cfg.

Arguments finType_sub_elem {_}.
Arguments restrict_edge {_}.

(** * sub_CFG **)

Program Instance sub_CFG
        `{C : redCFG}
        (P : decPred Lab)
        (r : Lab)
        (HP : P r)
        (Hreach : forall p, exists π, Path (restrict_edge a_edge P)
                                 (finType_sub_elem r P HP) 
                                 p π)
  : @redCFG (finType_sub_decPred P)
            (restrict_edge edge P)
            (finType_sub_elem r P HP)
            (restrict_edge a_edge P).

Next Obligation. (* loop_head_dom *)
  (* eapply dom_intersection,loop_head_dom,minus_back_edge;eauto. *)
Admitted.
Next Obligation. (* a_edge_incl *)
  (* eapply intersection2_subgraph; apply a_edge_incl.*)
Admitted.
Next Obligation. (* a_edge_acyclic *)
  eapply acyclic_subgraph_acyclic.
  - admit. (*eapply intersection_subgraph1.*)
  - eapply a_edge_acyclic.
    Unshelve. all:eauto.
Admitted.
Next Obligation. (* single_exit *)
  destruct h; destruct h'. destruct H12, H8. admit.
Admitted.
Next Obligation. (* no_head_exit *)
Admitted.
Next Obligation. (* no_exit_branch *)
Admitted.

(** * loop_CFG **)

Instance loop_CFG
           `(C : redCFG)
           (h : Lab)
           (H : loop_head h)
  : @redCFG (finType_sub_decPred (loop_nodes h))
            (restrict_edge edge (loop_nodes h))
            (finType_sub_elem h (loop_nodes h) (or_introl (loop_contains_self H)))
            (restrict_edge a_edge (loop_nodes h)).
Proof.
  eapply sub_CFG; intros.
  admit.
Admitted.

Lemma loop_CFG_elem `{C : redCFG} (h p : Lab)
           (Hloop : loop_contains h p)
  : finType_sub_decPred (loop_nodes h).
Proof.
  intros.
  econstructor. instantiate (1:=p).
  unfold pure. decide ((loop_nodes h) p);eauto.
  contradict n. unfold loop_nodes,predicate. left;auto.
Defined.

Arguments loop_CFG_elem {_ _ _ _} _.


Definition implode_nodes `{C : redCFG}
  := DecPred (fun p => (deq_loop root p
                     \/ (depth p = S (depth root)) /\ loop_head p)).

Definition get_root `(C : redCFG) := root.

Arguments loop_CFG {_ _ _ _} _.

Lemma loop_CFG_head_root `{C : redCFG} (h : Lab)
      (Hhead : loop_head h)
      (D := loop_CFG C h Hhead)
  : get_root D = loop_CFG_elem C h h (loop_contains_self Hhead).
Proof.
  unfold get_root. unfold loop_CFG_elem.
Admitted.

Lemma loop_CFG_top_level `{C : redCFG} (h p : Lab)
      (Hloop : loop_contains h p)
      (Hinner : innermost_loop_strict h p)
      (D := loop_CFG C h (loop_contains_loop_head Hloop))
      (p' := loop_CFG_elem C h p Hloop)
  : implode_nodes (C:=D) p'.
Proof.
  set (root' := (finType_sub_elem h
                                  (loop_nodes h)
                                  (or_introl (loop_contains_self (loop_contains_loop_head Hloop))))) in *.
  assert (innermost_loop (C:=D) root' p'). admit. (* this is not true. i need strict innermost loops *)
  unfold implode_nodes. econstructor.
  unfold deq_loop.
Admitted.
(*

Program Instance loop_CFG
        `{C : redCFG}
        (h : Lab)
        (H : loop_head h)
  : @redCFG (finType_sub_decPred (loop_nodes h))
            (restrict_edge (edge ∩ loop_edge h) (loop_nodes h))
            (finType_sub_elem h (loop_nodes h) (loop_edge_h_invariant H))
            (restrict_edge (a_edge ∩ loop_edge h) (loop_nodes h)).
(*  Next Obligation.
    eapply in_filter_iff.
    split; [eapply intersection_subgraph1 in H|eapply intersection_subgraph2 in H].
    - eapply edge_incl1;eauto.
    - unfold loop_edge in H. eapply intersection_subgraph1 in H. unfold decPred_bool. cbn. rewrite H. exact I.
  Qed.
  Next Obligation.
    eapply in_filter_iff.
    split; [eapply intersection_subgraph1 in H|eapply intersection_subgraph2 in H].
    - eapply edge_incl2;eauto.
    - unfold loop_edge in H. eapply intersection_subgraph2 in H. cbn. rewrite H. exact I.
  Qed.*)
Next Obligation. (* loop_head_dom *)
Admitted. (*
    destruct (loop_head_dec h) as [H0|H0];[|admit].
    eapply dom_intersection.
    eapply dom_trans ; eauto.
    - eapply reachability. eapply loop_head_in_graph;eauto. 
    - eapply dom_loop;eauto. 
      eapply loop_contains_ledge_head.
      + eapply minus_subgraph in H. eapply intersection_subgraph2 in H.
        unfold loop_edge in H.
        eapply intersection_subgraph1 in H; eapply loop_contains_spec;eauto.
      + eapply minus_back_edge;eauto. 
    - eapply loop_head_dom. eapply minus_back_edge; eauto.
  Admitted.*)
Next Obligation. (* subgraph *)
  eapply intersection2_subgraph. eapply a_edge_incl.

Admitted.
Next Obligation. (* acyclic *)
  eapply acyclic_subgraph_acyclic.
  - eapply intersection_subgraph1.
  - eapply a_edge_acyclic.
Admitted.

(*
  Lemma loop_contains_in_alllab h p :
    loop_contains h p -> p ∈ all_lab.
  Proof.
    intros Hloop. destruct Hloop. destructH.
    decide (x = p);subst.
    - eapply edge_incl1; eapply back_edge_incl; eauto.
    - eapply path_in_alllab1;eauto.
  Qed.*)

(*  Lemma loop_edge_reach_help `{C : redCFG} h p (*q*)
        (Hhead : loop_head h)
        (*        (Hedge : (edge ∩ loop_edge h) p q = true)*)
        (Hloop : loop_contains h p)
    : exists π, Path (edge ∩ loop_edge h) h p π.
  Proof.
    (*assert (p ∈ all_lab) as Hin by (eapply loop_contains_in_alllab;eauto).*) (* TODO *)
    specialize (dom_path h) as [π Hπ];[|eapply dom_loop;eauto].
    assert (EqDec Lab eq) as HHeq by eauto.
    specialize (path_NoDup _ _ _ _ _ (ex_intro _ π Hπ)) as [φ [Hφ Hnd]].
    exists φ. eapply path_loop_edge;eauto. eapply loop_contains_path; eauto.
  Qed. *)

Next Obligation. (* reachability *)
(*
    eapply in_filter_iff in H. destructH.
    destruct (loop_head_dec h) as [H|H];[|admit].
    eapply loop_edge_reach_help;eauto;eapply loop_contains_spec;eauto.*)
Admitted.
Next Obligation. (* single_exit *)
  (* since the original has single exits intersecting doesn't change anything *)
Admitted.
Next Obligation. (* no_head_exit *)
  (* there are neither new heads nor new edges -> property follows *)
Admitted.  
*)

Definition top_level `{redCFG} q := forall h, loop_contains h q -> (h = root \/ h = q).

Arguments loop_CFG {_ _ _ _} (_).

(** * head_exits **)

Definition head_exits_edge `{redCFG} h q : bool
  := if decision (exited h q) then true else false. 

Lemma head_exits_edge_spec :
  forall `{redCFG} h q, head_exits_edge h q = true <-> exists p, exit_edge h p q.
Proof.
  intros. unfold head_exits_edge. decide (exited h q); split;cbn;eauto.
  intros;congruence.
Qed.

Program Instance head_exits_CFG `(redCFG)
  : redCFG (edge ∪ head_exits_edge) root (a_edge ∪ head_exits_edge).


Lemma head_exits_in_path_head_incl `{redCFG} ql π
      (Hpath : Path (edge ∪ head_exits_edge) root ql π)
  : exists ϕ, Path edge root ql ϕ /\ forall h, loop_head h -> h ∈ ϕ -> h ∈ π.
Admitted.

Lemma head_exits_back_edge `{redCFG} ql qh :
  ((edge ∪ head_exits_edge) ∖ (a_edge ∪ head_exits_edge)) ql qh = true <-> ql ↪ qh.
Admitted.

Next Obligation. (* loop_head_dom *)
  unfold Dom. intros π Hpath.
  rewrite head_exits_back_edge in H0.
  eapply head_exits_in_path_head_incl in Hpath. destructH. unfold loop_head in Hpath1.
  eapply loop_head_dom in Hpath0;eauto.
Qed.
Next Obligation. (* a_edge_incl *)
  eapply union_subgraph.
  - exact a_edge_incl.
  - firstorder.
Qed.

Lemma head_exits_no_self_loop `{redCFG} p q : head_exits_edge p q = true -> p <> q.
Admitted.


Lemma head_exits_path `{redCFG} p q :
  head_exits_edge p q = true -> p -a>* q.
Admitted.

Lemma head_exits_same_connected `{redCFG} p q π
      (Hpath : Path (a_edge ∪ head_exits_edge) p q π)
  : exists ϕ, Path a_edge p q ϕ.
Admitted.
Next Obligation. (* a_edge_acyclic *)
  unfold acyclic. intros p q Hedge [π Hπ]. eapply head_exits_same_connected in Hπ. destructH.
  unfold union_edge in Hedge; conv_bool. destruct Hedge as [Hedge|Hedge].
  - eapply a_edge_acyclic; eauto.
  - eapply head_exits_no_self_loop in Hedge as Hnself.
    eapply head_exits_path in Hedge. destructH. eapply path_path_acyclic;eauto.
    exact a_edge_acyclic.
Qed.

Next Obligation. (* reachability *)
  specialize a_reachability as H0. eapply subgraph_path in H0;eauto.
  unfold sub_graph,union_edge. firstorder. 
Qed.
Next Obligation. (* single_exit *)
  (* new exits don't have new targets, and the source has the same depth *)
Admitted.
Next Obligation. (* no_head_exit *)
  (* new exits don't have new targets *)
Admitted.
Next Obligation. (* no_exit_branch *)
Admitted.

Definition head_exits_property `(C : redCFG) := forall h p q, exit_edge h p q -> edge h q = true.

Arguments exit_edge {_ _ _ _} (_).

Lemma head_exits_property_satisfied `(C : redCFG) : head_exits_property (head_exits_CFG C).
Proof.
  unfold head_exits_property. 
  intros h p q Hexit. unfold union_edge. conv_bool.
  unfold exit_edge in Hexit. destructH. unfold union_edge in Hexit3. conv_bool.
  destruct Hexit3.
  - right. eapply head_exits_edge_spec. exists p. admit. (* loop_contains <-> loop_contains *)
  - eapply head_exits_edge_spec in H. destructH. admit.
Admitted.

Arguments exit_edge {_ _ _ _ _}.

(** implode CFG **)
(* assuming no exit-to-heads *)


Lemma implode_nodes_root_inv `{C : redCFG}
  : implode_nodes root.
Proof.
  unfold implode_nodes. cbn.
  left.
  unfold deq_loop. firstorder.
Qed.

Instance implode_CFG `(H : redCFG) (Hhe : head_exits_property H)
  : @redCFG (finType_sub_decPred implode_nodes)
            (restrict_edge edge implode_nodes)
            (finType_sub_elem root implode_nodes (implode_nodes_root_inv))
            (restrict_edge a_edge implode_nodes).
Proof.
  eapply sub_CFG;intros.
Admitted.

Lemma implode_CFG_elem `{C : redCFG} (p : Lab) (Himpl : implode_nodes p)
  : finType_sub_decPred implode_nodes.
Proof.
  econstructor. unfold pure. instantiate (1:=p).
  decide (implode_nodes p);eauto.
Defined.


(*
Next Obligation.
  eapply filter_In in H0. destructH. eapply reachability in H1. destruct H1 as [π Hπ].
  conv_bool. rewrite deq_loop_spec in H2.
  revert q Hπ H2.
  eapply (prefix_ne_induction π).
  clear π. intros π IH q Hπ Hdeq.
  destruct π as [|b π].
  - inversion Hπ;subst. eexists;econstructor.
  - replace b with q in *; [|inversion Hπ;reflexivity]. clear b.
    destruct π as [|b π].
    * clear - Hdeq Hπ. inversion Hπ;subst. inversion H1;subst. exists (q :<: ne_single l).
      econstructor;[econstructor|]. unfold intersection_edge;conv_bool. split;eauto.
      unfold implode_edge;conv_bool.
      admit.
    (*split;eapply deq_loop_spec;eauto. eapply deq_loop_refl.*)
    * destruct (deq_loop_b root b) eqn:E.
      -- eapply deq_loop_spec in E. specialize (IH q (b :<: π)).
         destruct Hdeq.
         {
           edestruct IH;eauto.
           ++ econstructor.
           ++ inversion Hπ;subst;inversion H2;subst. assumption.
           ++ exists (q :<: x). econstructor;eauto.
              unfold intersection_edge;conv_bool;split.
              ** inversion Hπ;subst;inversion H3;subst;eauto.
              ** unfold implode_edge;conv_bool. admit. (* split;eapply deq_loop_spec;eauto.*)
         }
         admit. 
      -- eapply not_true_iff_false in E. rewrite deq_loop_spec in E.
         eapply ex_innermost_loop in E; cycle 1.
         {
           inversion Hπ;subst;inversion H1;subst. eapply path_in_alllab2;eauto.
           contradict E. subst;eapply deq_loop_refl.
         } 
         unfold innermost_loop in E. destructH.
         admit.
Admitted.*)

(*Instance opt_loop_CFG `(C : redCFG) (h : Lab)
  : @redCFG (finType_sum (@finType_sub_decPred Lab (@loop_nodes Lab edge root a_edge C h)) Lab)
            (match decision (@loop_head _ _ _ _ C h) with
             | left H => (@restrict_edge Lab edge (@loop_nodes Lab edge root a_edge C h))
             | right _ => edge
             end)
            (match decision (loop_head h) with
             | left H => (@finType_sub_elem Lab h (@loop_nodes Lab edge root a_edge C h)
                                           (@loop_edge_h_invariant Lab edge root a_edge C h H))
             | right _ => root
             end)
            (match decision (loop_head h) with
             | left H => (@restrict_edge Lab a_edge (@loop_nodes Lab edge root a_edge C h))
             | right _ => a_edge
             end).*)
               
Goal forall `(C : redCFG) (h:Lab), (match decision (@loop_head _ _ _ _ C h) with
             | left H => (@finType_sub_decPred Lab (@loop_nodes Lab edge root a_edge C h))
             | right _ => Lab
                               end).
intros. decide (loop_head h);eauto. Show Proof.
Abort.

Definition if_transfm : forall (X Y : Type) (A B : Prop) (b : {A} + {B}), (if b then X -> X -> bool else Y -> Y -> bool)
                             -> (if b then X else Y)
                             -> (if b then X else Y)
                             -> bool.
  intros. destruct b. all: exact (X0 X1 X2).
Defined.


Instance opt_loop_CFG' `(C : redCFG) (h : Lab)
  : let d := (@decision (@loop_head _ _ _ _ C h) (loop_head_dec _)) in
    let Lab' := @finType_sub_decPred Lab (@loop_nodes Lab edge root a_edge C h) in
    @redCFG (if d then Lab' else Lab)
            ((if d
                 return ((if d then Lab' else Lab)
                         -> (if d then Lab' else Lab) -> bool) then
                (@restrict_edge Lab edge (@loop_nodes Lab edge root a_edge C h))
              else
                edge))
            (match d
                   return (eqtype (type (if d then Lab' else Lab))) with
             | left H => (@finType_sub_elem Lab h (@loop_nodes Lab edge root a_edge C h)
                                           (or_introl (@loop_contains_self Lab edge root a_edge C h H)))
             | right _ => root
             end)
            ((if d as d
                 return ((if d then Lab' else Lab)
                         -> (if d then Lab' else Lab) -> bool) then
                (@restrict_edge Lab a_edge (@loop_nodes Lab edge root a_edge C h))
              else
                a_edge)).
Proof.
  intros.
  destruct (loop_head_dec h); eauto. 
Defined.

Definition loop_CFG_type `(C : redCFG) (h : Lab) (H : loop_head h)
  := @finType_sub_decPred Lab (@loop_nodes Lab edge root a_edge C h).

Definition opt_loop_CFG_type `(C : redCFG) (d : option {h : Lab | loop_head h})
  := (match d with
      | Some (exist _ h H) => loop_CFG_type H
      | None => Lab
      end). 

Instance opt_loop_CFG `(C : redCFG) (d : option {h : Lab | loop_head h})
  : @redCFG (opt_loop_CFG_type d)
            (match d
                   return ((opt_loop_CFG_type d) -> (opt_loop_CFG_type d) -> bool) with
             | Some (exist _ h H) => (@restrict_edge Lab edge (@loop_nodes Lab edge root a_edge C h))
             | None => edge
             end)
            (match d
                   return (eqtype (type (opt_loop_CFG_type d))) with
             | Some (exist _ h H) => (@finType_sub_elem Lab h (@loop_nodes Lab edge root a_edge C h)
                                                       (or_introl (@loop_contains_self Lab edge root a_edge C h H)))
             | None => root
             end)
            (match d
                   return ((opt_loop_CFG_type d) -> (opt_loop_CFG_type d) -> bool) with
             | Some (exist _ h H) => (@restrict_edge Lab a_edge (@loop_nodes Lab edge root a_edge C h))
             | None => a_edge
             end).
Proof.
  intros.
  destruct d; [destruct s|]; eauto.
Defined.

Lemma opt_loop_CFG_elem `{C : redCFG} (p : Lab)
      (d : option {h : Lab | loop_head h})
      (Hd : match d with
            | Some (exist _ h _) => loop_contains h p
            | None => True
            end)
  : opt_loop_CFG_type d.
Proof.
  destruct d;[|exact p].
  destruct s. eapply loop_CFG_elem; eauto.
Defined.

Arguments opt_loop_CFG {_ _ _ _} _.
Arguments head_exits_CFG {_ _ _ _} _.
Arguments implode_CFG {_ _ _ _} _.

Definition local_impl_CFG `(C : redCFG) (d : option {h : Lab | loop_head h})
  := let D := opt_loop_CFG C d in
     implode_CFG (head_exits_CFG D) (head_exits_property_satisfied (C:=D)).

Arguments redCFG : clear implicits.
Arguments implode_nodes {_ _ _ _} _.
Definition local_impl_CFG_type `(C : redCFG) (d : option {h : Lab | loop_head h})
  := (finType_sub_decPred (implode_nodes (head_exits_CFG (opt_loop_CFG C d)))).
Arguments redCFG : default implicits.
Arguments implode_nodes : default implicits.

Definition original_of_impl `(C : redCFG) (d : option {h : Lab | loop_head h})
  : local_impl_CFG_type d -> Lab.
Proof.
  intros. eapply proj1_sig in X.
  unfold opt_loop_CFG_type in X. destruct d.
  - destruct s. eapply proj1_sig in X. exact X.
  - exact X.
Defined.

Definition loop_CFG_of_original `(C : redCFG) (h : Lab) (H : loop_head h) (p : Lab)
  : option (loop_CFG_type H).
Proof.
  decide (loop_nodes h p).
  - apply Some. econstructor. eapply purify;eauto.
  - apply None.
Defined.

Definition impl_of_original `(C : redCFG) (d : option {h : Lab | loop_head h})
  : Lab -> option (local_impl_CFG_type d).
Proof.
  intro p.
  destruct d; unfold local_impl_CFG_type, opt_loop_CFG.
  - destruct s as [h H]. destruct (loop_CFG_of_original H p).
    + decide (implode_nodes (head_exits_CFG (loop_CFG C h H)) e).
      * apply Some. econstructor. eapply purify;eauto.
      * exact None.
    + exact None.
  - decide (implode_nodes (head_exits_CFG C) p).
    + apply Some.
      econstructor. eapply purify;eauto.
    + exact None.
Defined.

(*Program Lemma local_impl_CFG_elem `(C : redCFG) (d : option {h : Lab | loop_head h})
         : match d with
  | Some (exist _ h _) => _
  | None => _
    end.
Proof.
  destruct d. destruct s.
Admitted.*)

Arguments local_impl_CFG {_ _ _ _} _.
(** more parameters **)

Lemma Lab_dec' `{redCFG} : forall (l l' : Lab), { l = l' } + { l <> l'}.
Proof.
  apply Lab_dec.
Qed.

(* TODO : remove or include in redCFG def *)
Parameter no_self_loops : forall `(C : redCFG), forall q p, edge q p = true -> q =/= p.
