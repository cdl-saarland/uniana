
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

  Section Graph.
    
    Variable L : Type.
    Variables edge edge1 edge2 : L -> L -> bool.
    
    Hypothesis L_dec : EqDec L eq.

    Local Notation "p -->b q" := (edge p q) (at level 55, right associativity).
    Local Notation "p --> q" := (p -->b q = true) (at level 55, right associativity).
    
    Inductive Path : L -> L -> ne_list L -> Prop :=
    | PathSingle a : Path a a (ne_single a)
    | PathCons {a b c π} : Path a b π -> b --> c -> Path a c (c :<: π).

    Local Notation "p -->* q" := (exists π, Path p q π) (at level 55).

    Definition Dom r p q := forall π, Path r q π -> p ∈ π.

    Lemma dominant_root r p : Dom r r p.
    Proof.
      intros π Hpath. induction Hpath;cbn;eauto.
    Qed.

    Lemma dominant_self p q : Dom p q q.
    Proof.
      intros π Hπ. induction Hπ;cbn;eauto.
    Qed.
    
    Lemma path_front p q π :
      Path p q π -> ne_front π = q.
    Proof.
      intro H. induction H; cbn; eauto.
    Qed.
    
    Lemma path_back p q π :
      Path p q π -> ne_back π = p.
    Proof.
      intro H. induction H; cbn; eauto.
    Qed.

    Lemma path_dec p q π :
      {Path p q π} + {~ Path p q π}.
    Proof.
      revert q; induction π; intros q.
      - decide' (p == a); decide' (q == p). 1: left; econstructor.
        all: right; intro N; inversion N; firstorder.
      - decide' (q == a);
          [destruct (edge (ne_front π) q) eqn:E;
           [destruct (IHπ (ne_front π))|]|].
        1: left; econstructor; eauto.
        all: right; intro N; inversion N;subst. 3: eapply c; reflexivity.
        all: eapply path_front in H0 as H0'; subst b. 1:contradiction.
        rewrite <-not_true_iff_false in E. contradiction.
    Qed.

    Lemma path_app π ϕ p q r : Path p q π -> Path q r ϕ -> Path p r (ϕ :+ tl π).
    Admitted.

    Lemma path_app_conc π ϕ p q q' r : Path p q π -> q --> q' -> Path q' r ϕ -> Path p r (ϕ :+: π).
    Admitted.

    (* this is not used : { *)
    Inductive uniqueIn {A : Type} (a : A) : list A -> Prop := 
    | UniqueIn (l : list A) : a ∉ l -> uniqueIn a (a :: l)
    | UniqueCons (b : A) (l : list A) : uniqueIn a l -> a <> b -> uniqueIn a (b :: l).

    Lemma uniqueIn_app {A : Type} `{EqDec A eq} (a : A) l1 l2
      : uniqueIn a l1 -> a ∉ l2 -> uniqueIn a (l1 ++ l2).
    Proof.
      intros Huq Hin.
      induction l1; cbn; eauto.
      - inversion Huq.
      - decide' (a == a0).
        + econstructor; eauto. inversion Huq; eauto. intro N. eapply in_app_or in N. firstorder.
        + econstructor 2; eauto. eapply IHl1. inversion Huq; [contradiction|eauto].
    Qed.
    
    Lemma path_glue_loop p r (π0 π1 : ne_list L) :
      Path p r π0
      -> uniqueIn r π0 -> uniqueIn r π1
      -> uniqueIn r (π1 ++ tl π0).
    Proof.
      intros Hpr Huq0 Huq1.
      eapply uniqueIn_app; eauto.
      induction π0; cbn; eauto.
      clear - Huq0 Hpr. eapply path_front in Hpr. cbn in *. subst a. intro N.
      inversion Huq0; eauto.
    Qed.

    Lemma uniqueIn_NoDup {A : Type} `{EqDec A eq} (l : list A)
      : NoDup l <-> forall a, a ∈ l -> uniqueIn a l.
    Proof.
      rename H into Hed.
      split; [intros Hnd a Hin|intros H].
      - induction l; inversion Hin; inversion Hnd; cbn; subst.
        + econstructor; eauto.
        + exploit IHl. econstructor;eauto. intro N. subst. contradiction.
      - induction l; econstructor.
        + specialize (H a (or_introl (eq_refl))). inversion H; eauto.
        + eapply IHl. intros b Hb.
          specialize (H b (or_intror Hb)).
          decide' (a == b); inversion H; eauto; subst; contradiction.
    Qed.
    (* } *)

    Lemma prefix_single {A : Type} (a : A) (l : ne_list A)
      : Prefix (ne_single a) l -> ne_back l = a.
    Proof.
      intro H. induction l; inversion H; cbn; eauto; subst. inversion H2.
      destruct l; cbn in *; congruence.
    Qed.

    Lemma path_prefix_path p q (π ϕ : ne_list L) : Path p q π -> Prefix ϕ π -> Path p (ne_front ϕ) ϕ.
    Proof.
      intros Hpq Hpre. revert dependent q. dependent induction Hpre; intros q Hpq.
      - eapply ne_to_list_inj in x. subst. erewrite path_front; eauto.
      - destruct π.
        + inversion x. subst l'. inversion Hpre; subst. destruct ϕ; cbn in H2; congruence.
        + rewrite nlcons_to_list in x. eapply ne_to_list_inj in x.
          eapply IHHpre; cycle 1.
          * instantiate (1:=π). destruct l';[cbn in x;congruence|].
            cbn in x. inversion x. simpl_nl. reflexivity.
          * instantiate (1:= ne_front π). inversion Hpq; subst. erewrite path_front; eauto.
          * reflexivity.
    Qed.
    
    Lemma path_postfix_path p q (π ϕ : ne_list L) : Path p q π -> Postfix ϕ π -> Path (ne_back ϕ) q ϕ.
    Proof.
    Admitted.

    Definition prefix_incl : forall (A : Type) (l l' : list A), Prefix l l' -> l ⊆ l'
      := fun (A : Type) (l l' : list A) (post : Prefix l l') =>
           Prefix_ind A (fun l0 l'0 : list A => l0 ⊆ l'0) (fun l0 : list A => incl_refl l0)
                      (fun (a : A) (l0 l'0 : list A) (_ : Prefix l0 l'0) (IHpost : l0 ⊆ l'0) =>
                         incl_appr (a :: nil) IHpost) l l' post.      

    Lemma prefix_NoDup {A : Type} (l l' : list A) : Prefix l l' -> NoDup l' -> NoDup l.
    Proof.
      intros Hpre Hnd. induction Hpre; eauto.
      inversion Hnd; subst; eauto.
    Qed.
    
    Lemma path_NoDup p q : p -->* q -> exists π, Path p q π /\ NoDup π.
    Proof.
      intros [ϕ Hto].
      induction Hto.
      - exists (ne_single a). split;econstructor;eauto. econstructor.
      - destruct IHHto as [ψ [IHHto IHnodup]].
        destruct (In_dec c ψ).
        + eapply prefix_nincl_prefix in H0.
          exists (c :< prefix_nincl c ψ). split.
          * rewrite nlcons_to_list in H0.
            eapply path_prefix_path in H0; eauto; cbn in *; simpl_nl' H0; eauto.
          * eapply prefix_NoDup; eauto. simpl_nl; eauto.
        + exists (c :<: ψ). split;econstructor;eauto.
    Qed.

    Lemma in_nlcons {A : Type} `{EqDec A eq} (l : list A) (a b : A)
      : a ∈ (b :< l) <-> a = b \/ a ∈ l.
    Proof.
      split; intro Q.
      - revert dependent b. induction l; cbn in *;intros b Q;[firstorder|].
        destruct Q;[firstorder|].
        right. specialize (IHl a0 H0). firstorder.
      - revert dependent b. induction l; cbn in *;intros b Q;[firstorder|].
        destruct Q;[firstorder|].
        right. eapply IHl. firstorder.
    Qed.

    Lemma in_ne_conc {A : Type} `{EqDec A eq} (l l' : ne_list A)
      : forall a, a ∈ (l :+: l') <-> a ∈ l \/ a ∈ l'.
    Proof.
      split; revert a; induction l;intros b Q; cbn in *; firstorder 0.
    Qed.

    Lemma in_nl_conc {A : Type} `{EqDec A eq} (l : ne_list A) l' (a : A)
      : a ∈ (l :+ l') <-> a ∈ l \/ a ∈ l'.
    Proof.
      split;revert a;induction l'; intros b Q; cbn in *; [firstorder| |firstorder|].
      - eapply in_ne_conc in Q. repeat destruct Q; eauto. eapply in_nlcons in H0. destruct H0;eauto.
      - eapply in_ne_conc. repeat destruct Q; eauto. right. eapply in_nlcons. firstorder.
    Qed.


    Lemma path_to_elem p q r π : Path p q π -> r ∈ π -> exists ϕ, Path p r ϕ /\ Prefix ϕ π.
    Proof.
      revert dependent q.
      induction π; intros q Hpath Hin; cbn in *; eauto.
      - destruct Hin;[subst|contradiction].
        eapply path_front in Hpath as Hfront. eapply path_back in Hpath as Hback. subst p q; cbn in *.
        eexists; split; eauto. econstructor.
      - destruct Hin.
        + subst a. eapply path_back in Hpath as Hback. eapply path_front in Hpath as Hfront.
          subst p q; cbn in *. exists (r :<: π); split; eauto.
          econstructor.
        + inversion Hpath; subst. specialize (IHπ b H4 H) as [ϕ [Hϕ Hpre]].
          eexists;split;eauto. econstructor;eauto.
    Qed.

    Lemma path_from_elem p q r π : Path p q π -> r ∈ π -> exists ϕ, Path r q ϕ /\ Postfix ϕ π.
    Proof.
      intros Hpath Hin. exists (postfix_nincl r π >: r).
      assert (Postfix (postfix_nincl r π >: r) π) as H;[|split];eauto.
      - simpl_nl. eapply postfix_nincl_spec; eauto.
      - eapply path_postfix_path in Hpath;eauto. simpl_nl' Hpath;eauto.
    Qed.        
    
    Lemma dom_nin r p q π : Dom r p q -> Path r p π -> NoDup π -> q ∈ π -> p = q.
    Proof.
      intros Hdom Hpath Hnd Hin. eapply path_to_elem in Hpath as Hpath';eauto.
      destruct Hpath' as [ϕ [Hϕ Hpre]].
      inversion Hpre; subst.
      - eapply ne_to_list_inj in H1. subst. eapply path_front in Hpath. eapply path_front in Hϕ.
        subst p q; eauto.
      - exfalso.
        rewrite nlcons_to_list in H. eapply ne_to_list_inj in H; subst π.
        eapply path_front in Hpath. cbn in Hpath. simpl_nl' Hpath. subst a.
        eapply Hdom in Hϕ as Hϕ'. eapply prefix_incl in H1. eapply H1 in Hϕ'.
        simpl_nl' Hnd. inversion Hnd; subst; contradiction.
    Qed.
    
    Lemma in_ne_back {A : Type} `{EqDec A eq} (l : ne_list A) : ne_back l ∈ l.
    Proof.
      induction l; cbn; eauto.
    Qed.
    
    Lemma dom_trans r h p q : r -->* h -> Dom r h p -> Dom r p q -> Dom h p q.
    Proof.
      intros Hϕ Hdom_h Hdom_p π Hπ.
      eapply path_NoDup in Hϕ as [ϕ [Hϕ Hndup]].
      eapply path_app in Hπ as Hπ';eauto. eapply Hdom_p in Hπ'.
      eapply in_nl_conc in Hπ'.
      destruct Hπ'; eauto.
      enough (h = p).
      - subst h. eapply path_back in Hπ. subst p; eapply in_ne_back.
      - eapply dom_nin. 3: eassumption. 1: apply Hdom_h. 1: eauto.
        destruct ϕ; cbn in H; [contradiction|]. right; eauto.
    Qed.
    
    Definition intersection_edge := fun p q => edge1 p q && edge2 p q.

    Definition union_edge := fun p q => edge1 p q || edge2 p q.

    Definition minus_edge := fun p q => edge1 p q && negb(edge2 p q).

    Definition sub_graph := forall p q, edge1 p q = true -> edge2 p q = true.

    Definition acyclic := forall p q, p --> q -> ~ q -->* p.

    Lemma path_path_acyclic p q π ϕ : Path p q π -> Path q p ϕ -> p <> q -> ~ acyclic.
    Proof.
      intros Hpath1 Hpath2 Hneq Hacy.
      inversion Hpath1;[contradiction|].
      inversion Hpath2;subst;[contradiction|].
      specialize (Hacy b q H0). eapply Hacy. exists (π0 :+: π1).
      eapply path_app_conc;eauto.
    Qed.

    Lemma postfix_path l p q q' l' :
      Path q' q l'
      -> Postfix (l :r: p) l'
      -> Path p q (nl_rcons l p).
    Admitted.

    Definition Path' π := Path (ne_back π) (ne_front π) π.

    
    Lemma postfix_front {A : Type} (l l' : ne_list A) :
      Postfix l l'
      -> ne_front l = ne_front l'.
    Proof.
      intros H. dependent induction H.
      - apply ne_to_list_inj in x; rewrite x; eauto.
      - rewrite rcons_nl_rcons in x. apply ne_to_list_inj in x. 
        rewrite <-x. destruct l'0.
        + exfalso. inversion H; [eapply ne_to_list_not_nil|eapply rcons_not_nil]; eauto.
        + cbn. erewrite IHPostfix; eauto; [|rewrite nlcons_to_list; reflexivity].
          simpl_nl; reflexivity.
    Qed.

    
    Ltac path_simpl' H :=
      lazymatch type of H with
      | Path ?edge ?x ?y (?z :<: ?π) => let Q := fresh "Q" in
                                       eapply path_front in H as Q;
                                       cbn in Q; subst z
      | Path ?edge ?x ?y (?π :>: ?z) => let Q := fresh "Q" in
                                       eapply path_back in H as Q;
                                       cbn in Q; subst z
      end.

  (*
    Lemma path_postfix_path p q q' (l l' : ne_list L) :
      Path p q l
      -> Postfix l' l
      -> Path p q' l'.
    Proof.
    Admitted. 
    intros Hpath Hpost. dependent induction Hpost.
    - apply ne_to_list_inj in x. setoid_rewrite x; eauto.
    - unfold Path'. specialize (IHHpost H). erewrite postfix_front; eauto.
  Qed.*)

  End Graph.

  Arguments Path {L}.
  Arguments Dom {L}.
  Arguments intersection_edge {L}.
  Infix "∩" := intersection_edge (at level 50).
  Arguments union_edge {L}.
  Infix "∪" := union_edge (at level 51).
  Arguments minus_edge {L}.
  Infix "∖" := minus_edge (at level 49).
  Arguments sub_graph {L}.
  Arguments acyclic {L}.
  
  Lemma subgraph_path {L : Type} (edge1 edge2 : L -> L -> bool) p q :
    sub_graph edge1 edge2 -> (exists π, Path edge1 p q π) -> (exists ϕ, Path edge2 p q ϕ).
  Proof.
    intros Hsub [π Hpath]. unfold sub_graph in Hsub. induction Hpath.
    - exists (ne_single a). econstructor.
    - destruct IHHpath as [ϕ IHHpath]. exists (c :<: ϕ). econstructor; eauto.
  Qed.

  Lemma subgraph_path' {L : Type} (edge1 edge2 : L -> L -> bool) p q π :
    sub_graph edge1 edge2 -> Path edge1 p q π -> Path edge2 p q π.
  Proof.
    intros Hsub Hpath. unfold sub_graph in Hsub. induction Hpath.
    - econstructor.
    - econstructor; eauto. 
  Qed.
  
  Lemma acyclic_subgraph_acyclic {L : Type} (edge1 edge2 : L -> L -> bool) :
    sub_graph edge1 edge2 -> acyclic edge2 -> acyclic edge1.
  Proof.
    intros Hsub Hacy p q Hedge N. unfold acyclic, sub_graph in *. 
    eapply Hacy; eauto. destruct N as [π Hpath].
    eapply subgraph_path; eauto.
  Qed.

  Lemma minus_subgraph {L : Type} (edge1 edge2 : L -> L -> bool) :
    sub_graph (edge1 ∖ edge2) edge1.
  Proof.
    intros p q Hsub. unfold minus_edge in Hsub. conv_bool. firstorder.
  Qed.

  Lemma intersection_subgraph1 {L : Type} (edge1 edge2 : L -> L -> bool) :
    sub_graph (edge1 ∩ edge2) edge1.
  Proof.
    intros p q Hinter. unfold intersection_edge in Hinter. conv_bool. firstorder.
  Qed.
  
  Lemma intersection_subgraph2 {L : Type} (edge1 edge2 : L -> L -> bool) :
    sub_graph (edge1 ∩ edge2) edge2.
  Proof.
    intros p q Hinter. unfold intersection_edge in Hinter. conv_bool. firstorder.
  Qed.

  Lemma intersection2_subgraph {L : Type} (edge edge1 edge2 : L -> L -> bool) :
    sub_graph edge1 edge2
    -> sub_graph (edge1 ∩ edge) (edge2 ∩ edge).
  Proof.
    intros Hsub p q Hinter. unfold intersection_edge in *. unfold sub_graph in Hsub.
    conv_bool. destruct Hinter as [Hinter1 Hinter2]. eapply Hsub in Hinter1.
    rewrite Hinter1,Hinter2; cbn;eauto.
  Qed.

  Lemma union_subgraph {L : Type} (edge1 edge1' edge2 edge2' : L -> L -> bool) :
    sub_graph edge1 edge1' -> sub_graph edge2 edge2' -> sub_graph (edge1 ∪ edge2) (edge1' ∪ edge2').
  Proof.
    intros Hsub1 Hsub2 p q Hu. unfold union_edge, sub_graph in *.
    conv_bool. destruct Hu as [Hu|Hu];firstorder 1.
  Qed.    
  
  Lemma dom_intersection {L : Type} (edge1 edge2 : L -> L -> bool) r p q :
    Dom edge1 r p q -> Dom (edge1 ∩ edge2) r p q.
  Proof.
    intros Hdom.
    unfold Dom in *. intros. apply Hdom.
    eapply subgraph_path';eauto.
    eapply intersection_subgraph1.
  Qed.
    
End Graph.
(*+ CFG +*)

Module CFG.

  Export Graph.
  
  (** basic parameters **)
  Parameter Lab : Type.
  Parameter Lab_dec : EqDec Lab eq.

  Hint Resolve Lab_dec.
  
  (*  Notation "p '-->*' q" := (exists π, Path p q π) (at level 55, right associativity).*)

  Reserved Infix "-->b" (at level 55).
  Reserved Infix "-a>" (at level 55).
  Reserved Infix "-a>*" (at level 55).

  Definition decidableT (a : Prop) := {a} + {~ a}.
  
  Class redCFG
        (all_lab : list Lab)
        (edge : Lab -> Lab -> bool)
        (root : Lab) 
        (a_edge : Lab -> Lab -> bool)
    :=
      {
        back_edge_b := minus_edge edge a_edge
                       where "p -->b q" := (edge p q);
        back_edge := (fun p q => back_edge_b p q = true)
                     where "p --> q"  := (p -->b q = true);
        edge_incl1 : forall p q, p --> q -> p ∈ all_lab;
        edge_incl2 : forall p q, p --> q -> q ∈ all_lab;
        loop_head_dom : forall ql qh, back_edge ql qh -> Dom edge root qh ql
        where "p -a> q" := (a_edge p q = true);
        a_edge_incl : sub_graph a_edge edge
        where "p '-a>*' q" := (exists π, Path a_edge p q π);
        a_edge_acyclic : acyclic a_edge;
        reachability : forall q, q ∈ all_lab -> (exists π, Path edge root q π);
        loop_contains qh q := exists p π, back_edge p qh /\ Path edge q p π /\ (qh ∉ π \/ q = qh);
        exit_edge h p q := loop_contains h p /\ ~ loop_contains h q /\ p --> q;
        single_exit : forall h p q, exit_edge h p q -> forall h', exit_edge h' p q -> h = h';
        loop_head h := exists p, back_edge p h;
        no_exit_head : forall h p q, exit_edge h p q -> ~ loop_head q
      }. 
  
  Notation "p '-a>b' q" := ((fun (a_edge : Lab -> Lab -> bool)
                               (_ : redCFG _ _ _ a_edge) => a_edge) _ _ p q)
                             (at level 55).
  
  Notation "p '-a>' q" := (p -a>b q = true) (at level 55).

  Infix "-->b" := ((fun (edge : Lab -> Lab -> bool)
                      (_ : redCFG _ edge _ _) => edge)_ _) (at level 55).

  Notation "p --> q" := (p -->b q = true) (at level 55, right associativity).

  Notation "p '-->*' q" := ((fun (edge : Lab -> Lab -> bool)
                               (_ : redCFG _ edge _ _) => exists π, Path edge p q π) _ _)
                             (at level 55, right associativity).

  Notation "p '-a>*' q" := ((fun (a_edge : Lab -> Lab -> bool)
                               (_ : redCFG _ _ _ a_edge)
                             => exists π, Path a_edge p q π) _ _) (at level 55).
  
  Infix "↪" := back_edge (at level 55).

  Section red_cfg.

    (*Variables (edge a_edge : Lab -> Lab -> bool) (root : Lab) (all_lab : list Lab).*)

    Definition CPath `{redCFG} := Path edge.

    Context `{C : redCFG}.

    Definition CPath' π := CPath (ne_back π) (ne_front π) π.
    
    Lemma loop_head_dec p : decidableT (loop_head p).
    Admitted.

    Parameter loop_head_b : Lab -> bool.
    Parameter loop_head_spec : forall p : Lab, loop_head_b p = true <-> loop_head p.

    Lemma loop_contains_dec qh q : {loop_contains qh q} + {~ loop_contains qh q}.
    Admitted.

    Infix "∘" := Basics.compose (at level 40).
    
    Definition loop_contains_b qh q := to_bool (loop_contains_dec qh q).

    Parameter loop_contains_spec : forall qh q, loop_contains_b qh q = true <-> loop_contains qh q.

    (*  Definition loop_contains_spec `*)

    Definition deq_loop q p : Prop :=
      forall h, loop_contains h p -> loop_contains h q.

    Definition deq_loop_dec h p : {deq_loop h p} + {~ deq_loop h p}.
    Admitted.

    Definition deq_loop_b h p
      := to_bool (deq_loop_dec h p).

    Parameter deq_loop_spec : forall h p, deq_loop_b h p = true <-> deq_loop h p.
    
    Lemma deq_loop_refl l :
      deq_loop l l.
    Proof.
      unfold deq_loop;firstorder.
    Qed.

    Definition innermost_loop h p : Prop := loop_head h /\ deq_loop h p /\ loop_contains h p.

    Lemma ex_innermost_loop p
      : p ∈ all_lab -> ~ deq_loop root p -> exists h, innermost_loop h p.
    Proof.
      intros Hin N. unfold innermost_loop,deq_loop in *.
      eapply reachability in Hin as [π Hπ].
      (* pick last header, but not if it has an exit, in Hπ, exists because of N *)
    Admitted.

    Parameter get_innermost_loop : Lab -> Lab.

    Parameter exit_edge_b : forall `{redCFG}, Lab -> Lab -> Lab -> bool.
    Parameter exit_edge_b_spec : forall h p q, exit_edge_b h p q = true <-> exit_edge h p q.

    Parameter exit_edge_num : forall `{redCFG}, Lab -> Lab -> nat.

    Definition depth p := length (filter (fun q => loop_contains_b q p) all_lab).

    Definition exiting (h p : Lab) : Prop :=
      exists q, exit_edge h p q.

    Definition exited (h q : Lab) : Prop :=
      exists p, exit_edge h p q.

    Fixpoint preds' `{redCFG} (l : list Lab) (p : Lab) : list Lab :=
      match l with
      | nil => nil
      | q :: l => if (edge q p) then q :: (preds' l p) else preds' l p
      end.

    Definition preds : Lab -> list Lab := preds' all_lab.

    Definition filter_loop h := filter (loop_contains_b h) all_lab.

    Definition In_b {A : Type} `{H : EqDec A eq} (a : A) (l : list A)
      := if in_dec H a l then true else false.

    Lemma loop_contains_loop_head (qh q : Lab)
      : loop_contains qh q -> loop_head qh.
    Proof.
      intro Q. unfold loop_head, loop_contains in *. destruct Q as [p [_ [Q _]]].
      eexists; eauto.
    Qed.
    
    Lemma back_edge_incl p q : back_edge p q -> p --> q.
    Proof.
      unfold back_edge,back_edge_b. eapply minus_subgraph.
    Qed.

    Lemma back_edge_dec p q : {p ↪ q} + {~ p ↪ q}.
    Proof.
      unfold back_edge, back_edge_b, minus_edge.
      destruct (edge p q), (a_edge p q);cbn;firstorder.
    Qed.

    Hint Resolve back_edge_dec.

    Lemma path_in_alllab1 p q :
      p <> q -> p -->* q -> p ∈ all_lab.
    Proof.
      intros Hneq Hpath.
      destruct Hpath. revert dependent q.
      induction x; intros q Hneq Hpath; inversion Hpath;[contradiction|subst].
      decide' (p == b).
      - eapply edge_incl1;eauto.
      - eapply IHx;eauto.
    Qed.
    
    Lemma path_in_alllab2 p q :
      p <> q -> p -->* q -> q ∈ all_lab.
    Proof.
      intros Hneq Hpath.
      destruct Hpath. inversion H; [contradiction|eapply edge_incl2;eauto].
    Qed.
    
    Lemma loop_reachs_member (h q : Lab)
      : loop_contains h q ->h -->* q.
    Proof.
      intros Hloop. unfold loop_contains in Hloop.
      destructH.
      assert (q ∈ all_lab).
      {
        decide' (q == p).
        - eapply edge_incl1. apply back_edge_incl;eauto.
        - eapply path_in_alllab1;eauto.
      }
      destruct Hloop3;[|subst q; eexists; econstructor].
      eapply reachability in H. destructH. eapply loop_head_dom in Hloop0.
      eapply path_app in Hloop2;eauto. eapply Hloop0 in Hloop2. eapply in_nl_conc in Hloop2.
      destruct Hloop2;[contradiction|].
      assert (h ∈ π0).
      { destruct π0; cbn in *;[contradiction|right;eauto]. }
      eapply path_from_elem in H2;eauto. firstorder.
    Qed.
    
    Lemma dom_loop h
      : forall q: Lab, loop_contains h q -> Dom edge root h q.
    Proof.
      intros q Hq. unfold loop_contains,CPath in *. intros π Hπ.
      destructH. eapply path_app in Hq2; eauto.
      eapply loop_head_dom in Hq2;eauto. eapply in_nl_conc in Hq2.
      destruct Hq3;[|subst h;eapply path_front in Hπ; subst q; destruct π;cbn;eauto].
      destruct Hq2;[contradiction|]. clear - H0. destruct π; cbn in *; eauto.
    Qed.

    Lemma minus_back_edge edge' p q
      : ((edge ∩ edge') ∖ (a_edge ∩ edge')) p q = true -> p ↪ q.
    Proof.
      intros Q.
      unfold minus_edge,intersection_edge in Q. rewrite negb_andb in Q. conv_bool.
      unfold back_edge,back_edge_b.
      destruct Q as [[Q1 Q2] Q34]. unfold minus_edge. rewrite Q1; cbn. destruct Q34; eauto.
      rewrite Q2 in H; cbn in H; congruence.
    Qed.

    Lemma loop_head_in_graph h : loop_head h -> h ∈ all_lab.
      intro Q.
      unfold loop_head in *.  destructH.
      eapply edge_incl2;eapply back_edge_incl;eauto.
    Qed.

    Lemma dom_path p q
      : q ∈ all_lab -> Dom edge root p q -> p -->* q.
    Proof.
      intros Hin Hdom.
      eapply reachability in Hin as [π Hπ]. specialize (Hdom π Hπ).
      eapply path_from_elem in Hπ; eauto using Lab_dec. firstorder.
    Qed.

    Lemma loop_contains_not_dom h q 
      : loop_contains h q -> h <> q -> exists p, p ↪ h /\ ~ Dom edge q h p.
    Proof.
      intros Hloop Hneq. unfold loop_contains in Hloop. destructH.
      unfold Dom; eexists; firstorder; eauto.
      intros H0. destruct Hloop3;[|subst q;contradiction]. apply H,H0. eauto.
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
      decide' (p == q); [contradiction|].
      unfold loop_contains in Hloop. destructH.
      destruct Hloop3 as [Hloop3|Hloop3];[|subst q;eapply dominant_self]. rename π into π1.
      intros π Hπ.
      assert (p ∈ all_lab) as H0 by (eapply path_in_alllab1;eauto).
      eapply reachability in H0. destructH.
      unfold loop_contains in Hnloop.
      rewrite DM_not_exists in Hnloop. setoid_rewrite DM_not_exists in Hnloop.
      eapply path_app in Hloop2;eauto.
      specialize (Hnloop p0 (π1 :+ tl π)).
      setoid_rewrite not_and_iff in Hnloop; [setoid_rewrite not_and_iff in Hnloop|].
      - destruct Hnloop as [Hnloop|Hnloop]; [contradiction|destruct Hnloop].
        + contradiction.
        + clear - Hloop3 H. eapply not_or in H. destructH. eapply not_not in H0.
          * eapply in_nl_conc in H0. destruct H0;[contradiction|]. eapply in_tl_in;eauto.
          * eapply In_dec.
      - edestruct path_dec;eauto; firstorder.
      - edestruct (back_edge_dec p0 h); firstorder.
        Unshelve. all:eauto. (*TODO: remove *)
    Qed.

    Lemma loop_contains_self h : loop_head h -> loop_contains h h.
    Proof.
      intros Hl. unfold loop_contains.
      - unfold loop_head in Hl. destruct Hl. 
        eapply loop_head_dom in H as Hdom.
        eapply back_edge_incl in H as Hreach. specialize (reachability x) as Hreach'.
        exploit' Hreach'.
        + eapply edge_incl1;eauto.
        + destructH.
          eapply Hdom in Hreach' as Hreach''. eapply path_from_elem in Hreach'; eauto.
          destructH; eauto. eexists; eexists. firstorder; eauto.
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
      destruct (p == h) as [Hph|Hph].
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

    Definition loop_edge h := (fun q _ : Lab => loop_contains_b h q)
                                ∩ (fun _ q : Lab => loop_contains_b h q).

    Lemma path_loop_edge h q π
      : CPath h q π -> (forall p, p ∈ π (* /\ p=q *) -> loop_contains h p)
        -> Path (edge ∩ loop_edge h) h q π.
    Proof.
    Admitted.

    Lemma loop_contains_ledge_head h h' p
      : loop_contains h p -> p ↪ h' -> loop_contains h h'.
    Proof.
    Admitted.

    Program Instance loop_CFG
            (h : Lab)
      : redCFG (filter (fun p => loop_contains_b h p) all_lab)
               (edge ∩ loop_edge h)
               h
               (a_edge ∩ loop_edge h).
    Next Obligation.
      eapply filter_In.
      split; [eapply intersection_subgraph1 in H|eapply intersection_subgraph2 in H].
      - eapply edge_incl1;eauto.
      - unfold loop_edge in H. eapply intersection_subgraph1 in H. eapply H.
    Qed.
    Next Obligation.
      eapply filter_In.
      split; [eapply intersection_subgraph1 in H|eapply intersection_subgraph2 in H].
      - eapply edge_incl2;eauto.
      - unfold loop_edge in H. eapply intersection_subgraph2 in H. eapply H.
    Qed.
    Next Obligation.
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
    Admitted.
    Next Obligation.
      eapply intersection2_subgraph; apply a_edge_incl.
    Qed.
    Next Obligation.
      eapply acyclic_subgraph_acyclic.
      - eapply intersection_subgraph1.
      - eapply a_edge_acyclic.
    Qed.

    Lemma loop_contains_in_alllab h p :
      loop_contains h p -> p ∈ all_lab.
    Proof.
      intros Hloop. destruct Hloop. destructH.
      decide' (x == p).
      - eapply edge_incl1; eapply back_edge_incl; eauto.
      - eapply path_in_alllab1;eauto.
    Qed.

    Lemma loop_edge_reach_help h p (*q*)
          (Hhead : loop_head h)
          (*        (Hedge : (edge ∩ loop_edge h) p q = true)*)
          (Hloop : loop_contains h p)
      : exists π, Path (edge ∩ loop_edge h) h p π.
    Proof.
      assert (p ∈ all_lab) as Hin by (eapply loop_contains_in_alllab;eauto).
      eapply dom_path with (p:=h) in Hin as [π Hπ];[|eapply dom_loop;eauto].
      specialize (path_NoDup _ _ _ _ _ (ex_intro _ π Hπ)) as [φ [Hφ Hnd]].
      exists φ. eapply path_loop_edge;eauto. eapply loop_contains_path; eauto.
    Qed.
    
    Next Obligation.
      eapply filter_In in H. destructH.
      destruct (loop_head_dec h) as [H|H];[|admit].
      eapply loop_edge_reach_help;eauto;eapply loop_contains_spec;eauto.
    Admitted.
    Next Obligation.
      (* since the original has single exits intersecting doesn't change anything *)
    Admitted.
    Next Obligation.
    (* there are neither new heads nor new edges -> property follows *)
    Admitted.
    

    Definition top_level `{redCFG} q := forall h, loop_contains h q -> (h = root \/ h = q).
    

    Parameter exit_edge_dec : forall `{redCFG} h q p, 
        {exit_edge h p q} + {~ exit_edge h p q}.

  End red_cfg.

  Arguments loop_CFG {_ _ _ _} (_).
  
  Definition head_exits_edge `{redCFG} :=
    (fun h q
     => to_bool (Exists_dec (fun p => exit_edge h p q)
                           all_lab
                           (exit_edge_dec h q))).

  Parameter head_exits_edge_spec :
    forall `{redCFG} h q, head_exits_edge h q = true <-> exists p, exit_edge h p q.

  Program Instance head_exits_CFG `(redCFG)
    : redCFG all_lab (edge ∪ head_exits_edge) root (a_edge ∪ head_exits_edge).
  Next Obligation.
    unfold union_edge in H0. conv_bool. destruct H0;[eapply edge_incl1|];eauto.
    eapply head_exits_edge_spec in H0. destructH. unfold exit_edge in H0. destructH.
    unfold loop_contains in H1. destructH. eapply edge_incl2;eapply back_edge_incl;eauto.
  Qed.
  Next Obligation.
    unfold union_edge in H0. conv_bool. destruct H0;[eapply edge_incl2|];eauto.
    eapply head_exits_edge_spec in H0. destructH. unfold exit_edge in H0.
    eapply edge_incl2;destructH;eauto.
  Qed.

  Lemma head_exits_in_path_head_incl `{redCFG} ql π
        (Hpath : Path (edge ∪ head_exits_edge) root ql π)
    : exists ϕ, Path edge root ql ϕ /\ forall h, loop_head h -> h ∈ ϕ -> h ∈ π.
  Admitted.

  Lemma head_exits_back_edge `{redCFG} ql qh :
    ((edge ∪ head_exits_edge) ∖ (a_edge ∪ head_exits_edge)) ql qh = true <-> ql ↪ qh.
  Admitted.
  Next Obligation.
    unfold Dom. intros π Hpath.
    rewrite head_exits_back_edge in H0.
    eapply head_exits_in_path_head_incl in Hpath. destructH. unfold loop_head in Hpath1.
    eapply loop_head_dom in Hpath0;eauto.
  Qed.
  
  Next Obligation.
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
  Next Obligation.
    unfold acyclic. intros p q Hedge [π Hπ]. eapply head_exits_same_connected in Hπ. destructH.
    unfold union_edge in Hedge; conv_bool. destruct Hedge as [Hedge|Hedge].
    - eapply a_edge_acyclic; eauto.
    - eapply head_exits_no_self_loop in Hedge as Hnself.
      eapply head_exits_path in Hedge. destructH. eapply path_path_acyclic;eauto.
      exact a_edge_acyclic.
  Qed.
  Next Obligation.
    eapply reachability in H0. eapply subgraph_path in H0;eauto.
    unfold sub_graph,union_edge. firstorder.
  Qed.
  Next Obligation.
  (* new exits don't have new targets, and the source has the same depth *)
  Admitted.
  Next Obligation.
  (* new exits don't have new targets *)
  Admitted.


  Definition head_exits_property `(C : redCFG) := forall h p q, exit_edge h p q -> h --> q.
  
  Arguments exit_edge {_ _ _ _} (_).
  
  Lemma head_exits_property_satisfied `(C : redCFG) : head_exits_property (head_exits_CFG C).
  Proof.
    unfold head_exits_property. 
    intros h p q Hexit. unfold union_edge. conv_bool.
    unfold exit_edge in Hexit. destructH. unfold union_edge in Hexit3. conv_bool.
    destruct Hexit3.
    - right. eapply head_exits_edge_spec. exists p. admit. (* loop_contains <-> loop_contains *)
    - eapply head_exits_edge_spec in H. destructH.
  Admitted.
    
  Arguments exit_edge {_ _ _ _ _}.

  (* assuming no exit-to-heads *)
  Definition implode_edge `{redCFG} := (fun p q => deq_loop_b root p && deq_loop_b root q
                                                || deq_loop_b root p && loop_head_b q
                                                || loop_head_b p && deq_loop_b root q).
  
  Parameter implode_edge_spec :
    forall `{redCFG} p q, implode_edge p q = true <-> deq_loop root p /\ deq_loop root q.
  
  Program Instance implode_CFG `(H : redCFG) (Hhe : head_exits_property H)
    : redCFG (filter (fun p => deq_loop_b root p
                            || (depth p ==b S (depth root)) && loop_head_b p) all_lab)
             (edge ∩ implode_edge)
             root
             (a_edge ∩ implode_edge).
  Next Obligation.
      eapply filter_In.
      split; [eapply intersection_subgraph1 in H0|eapply intersection_subgraph2 in H0].
      - eapply edge_incl1;eauto.
      - unfold implode_edge in H0. conv_bool. repeat destruct H0; eauto 2. admit.
  Admitted.
  Next Obligation.
    eapply filter_In.
    split; [eapply intersection_subgraph1 in H0|eapply intersection_subgraph2 in H0].
    - eapply edge_incl2;eauto.
    - unfold implode_edge in H0. conv_bool. repeat destruct H0; eauto 2.  admit.
  Admitted.
  Next Obligation.
    eapply dom_intersection,loop_head_dom,minus_back_edge;eauto.
  Qed.
  Next Obligation.
    eapply intersection2_subgraph; apply a_edge_incl.
  Qed.
  Next Obligation.
    eapply acyclic_subgraph_acyclic.
    - eapply intersection_subgraph1.
    - eapply a_edge_acyclic.
  Qed.

  Lemma prefix_induction {A : Type} {P : list A -> Prop}
    : P nil
      -> (forall (a : A) (l : list A) (l' : list A), P l' -> Prefix (a :: l') l -> P l)
      -> forall l : list A, P l.
  Proof.
    intros Hbase Hstep l. induction l;eauto.
    eapply Hstep;eauto. econstructor.
  Qed.

  Lemma prefix_ne_induction {A : Type} l (P : ne_list A -> Prop) 
    : (forall (l : ne_list A), (forall (a : A) (l' : ne_list A), Prefix (a :<: l') l -> P l') -> P l)
      -> P l.
  Proof.
    intros Hstep. induction l.
    - eapply Hstep. intros b ? Hpre. inversion Hpre;subst;[simpl_nl' H2;contradiction|inversion H1].
    - admit.
  Admitted.
  
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
  Admitted.
  Next Obligation.
  (* as in loop_edge_CFG *)
  Admitted.
  Next Obligation.
  (* as in loop_edge_CFG *)
  Admitted.

  Definition local_impl_CFG `(C : redCFG) (h : Lab) :=
    let D := (loop_CFG C h) in 
    implode_CFG (head_exits_CFG D) (head_exits_property_satisfied D).


  (*  Parameter root_no_pred0 : forall p, p ∉ preds0 root.*)
  
  Parameter root : Lab.
  
  (*  Notation "p --> q" := (p ∈ preds0 q) (at level 55, right associativity).*)
  
  
  (** more parameters **)
  
  Lemma Lab_dec' : forall (l l' : Lab), { l = l' } + { l <> l'}.
  Proof.
    apply Lab_dec.
  Qed.

  Parameter no_self_loops : forall `(C : redCFG), forall q p, q --> p -> q =/= p.

  
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

  Hint Resolve Tag_dec.
  
  Lemma Coord_dec : EqDec Coord eq.
  Proof.
    eapply prod_eqdec;eauto.
  Qed.

  Hint Resolve Coord_dec.
  
  Hint Unfold Coord.

  Ltac destr_let :=
    match goal with
    | [ |- context[let (_,_) := fst ?a in _]] => destruct a;unfold fst 
    | [ |- context[let (_,_) := snd ?a in _]] => destruct a;unfold snd
    | [ |- context[let (_,_) := ?a in _]] => destruct a
    end.

  Definition tcfg_edge (edge : Lab -> Lab -> bool) (tag : Lab -> Lab -> Tag -> Tag) :=
    (fun c c' : Coord => let (p,i) := c  in
              let (q,j) := c' in
              edge p q && (to_bool (Tag_dec (tag p q i) j))).

  Fixpoint eff_tag `{redCFG} p q i : Tag
    := if back_edge_b p q
       then match i with
            | nil => nil
            | n :: l => (S n) :: l
            end
       else 
         let l' := @iter Tag (@tl nat) i (exit_edge_num p q) in
         if loop_head_dec q then O :: l' else l'.

  Definition TPath `{redCFG} := Path (tcfg_edge edge eff_tag).

  Lemma TPath_CPath `{redCFG} c c' π :
    TPath c c' π -> CPath (fst c) (fst c') (ne_map fst π).
  Proof.
    intros Q. dependent induction Q; [|destruct b,c]; econstructor; cbn in *.
    - apply IHQ. 
    - conv_bool. firstorder. 
  Qed.            
  
  Definition TPath' `{redCFG} π := TPath (ne_back π) (ne_front π) π.
  
  Parameter eff_tag_fresh : forall `{redCFG} p q q0 i j j0 l,
      TPath (q0,j0) (q,j) l -> eff_tag q p j = i -> forall i', In (p, i') l -> i' <> i.

  Parameter eff_tag_det : forall `{redCFG} q j p i i',
      eff_tag q p j = i ->
      eff_tag q p j = i' ->
      i = i'.
  
End TCFG.

  
    
    
          