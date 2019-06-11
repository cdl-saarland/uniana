
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Decidable.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Bool.Bool.
Require Import Lists.ListSet.
Require Import Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Utils.

Require Export Util NeList ListOrder.

(** Graph **)  

Section graph.
  
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

  
  Ltac path_simpl' H :=
    lazymatch type of H with
    | Path ?edge ?x ?y (?z :<: ?π) => let Q := fresh "Q" in
                                     eapply path_front in H as Q;
                                     cbn in Q; subst z
    | Path ?edge ?x ?y (?π :>: ?z) => let Q := fresh "Q" in
                                     eapply path_back in H as Q;
                                     cbn in Q; subst z
    end.

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
  
  Lemma path_app_conc π ϕ p q q' r : Path p q π -> q --> q' -> Path q' r ϕ -> Path p r (ϕ :+: π).
  Proof.
    intros Hπ Hedge Hϕ.
    induction Hϕ;cbn;econstructor;eauto.
  Qed.
  
  Lemma path_app π ϕ p q r : Path p q π -> Path q r ϕ -> Path p r (ϕ :+ tl π).
  Proof.
    intros Hpath1 Hpath2.
    destruct π;cbn;inversion Hpath1;subst;eauto. 
    rewrite <-nlconc_neconc.
    eapply path_app_conc;eauto.
  Qed.

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

  Lemma path_rcons p q r π
        (Hπ : Path p q π)
        (Hedge : r --> p)
    : Path r q (π :>: r).
  Proof.
    eapply path_app_conc;eauto. econstructor.
  Qed.

  Lemma path_rcons_inv q r π
        (Hπ : Path r q (π :>: r))
    : exists p, Path p q π.
  Proof.
    revert dependent q. induction π; intros q Hπ.
    - exists a. inversion Hπ;subst;econstructor.
    - cbn in Hπ. eapply path_front in Hπ as Hfront. cbn in Hfront. subst a.
      inversion Hπ;subst. unfold ne_rcons in IHπ.
      specialize (IHπ b H0). destructH.
      eexists. econstructor;eauto.
  Qed.

  
  Lemma path_postfix_path p q (π ϕ : ne_list L) : Path p q π -> Postfix ϕ π -> Path (ne_back ϕ) q ϕ.
  Proof.
    intros Hπ Hϕ.
    revert dependent p. dependent induction Hϕ; intros p Hπ.
    - simpl_nl' x. subst ϕ. eapply path_back in Hπ as Hπ'. subst;eauto.
    - inversion Hπ; subst;destruct l'. 2: repeat (destruct l';cbn in x;try congruence). 
      1,2: exfalso;eapply ne_to_list_not_nil;eauto; symmetry; eapply postfix_nil_nil;eauto.
      rewrite rcons_nl_rcons in x. simpl_nl' x. rewrite <-x in Hπ.
      rewrite nlcons_to_list in Hπ.
      rewrite <-nercons_nlrcons in Hπ. eapply path_back in Hπ as Hback;simpl_nl' Hback; subst.
      eapply path_rcons_inv in Hπ. destructH.
      specialize (IHHϕ (l :< l') ϕ). eapply IHHϕ;eauto.
      simpl_nl;reflexivity.
  Qed.

  Lemma path_NoDup' p q ϕ : Path p q ϕ -> exists π, Path p q π /\ NoDup π.
  Proof.
    intros Hto.
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
  
  Lemma path_NoDup p q : p -->* q -> exists π, Path p q π /\ NoDup π.
  Proof.
    intros [ϕ Hto]. eapply path_NoDup';eauto.
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
  

  Lemma path_from_elem' p q r π : Path p q π -> r ∈ π ->
                                  let ϕ := postfix_nincl r π >: r in
                                  Path r q ϕ /\ Postfix ϕ π.
  Proof. 
    intros Hpath Hin.
    assert (Postfix (postfix_nincl r π >: r) π) as H;[|split];eauto.
    - simpl_nl. eapply postfix_nincl_spec; eauto.
    - eapply path_postfix_path in Hpath;eauto. simpl_nl' Hpath;eauto.
  Qed.
  
  Lemma path_from_elem p q r π : Path p q π -> r ∈ π -> exists ϕ, Path r q ϕ /\ Postfix ϕ π.
  Proof.
    intros. eexists;eapply path_from_elem';eauto.
  Qed.
  
  Lemma path_from_elem_to_elem (p q r1 r2 : L) (π : ne_list L)
        (Hπ : Path p q π)
        (Hprec : r2 ≻* r1 | π)
    : exists ϕ : ne_list L, Path r1 r2 ϕ. 
  Proof.
    eapply succ_rt_prefix in Hprec.
    destructH' Hprec.
    rewrite nlcons_to_list in Hprec0.
    eapply path_prefix_path in Hprec0 as Hprec2;eauto. simpl_nl' Hprec2.
    eapply path_from_elem in Hprec2;simpl_nl;eauto.
    destructH. eauto.
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

  Definition acyclic := forall p q π, p --> q -> Path q p π -> False.
  
  Lemma path_path_acyclic p q π ϕ : Path p q π -> Path q p ϕ -> p <> q -> ~ acyclic.
  Proof.
    intros Hpath1 Hpath2 Hneq Hacy.
    inversion Hpath1;[contradiction|].
    inversion Hpath2;subst;[contradiction|].
    specialize (Hacy b q (π0 :+: π1) H0). eapply Hacy.
    eapply path_app_conc;eauto. 
  Qed.
  
  Lemma path_path_acyclic' p q π ϕ : Path p q π -> Path q p ϕ -> acyclic -> p = q.
  Proof.
    intros Hpath1 Hpath2 Hacy.
    destruct (L_dec p q);[auto|]. eapply path_path_acyclic in c;eauto. contradiction.
  Qed.

  Lemma acyclic_path_path : (forall p q π ϕ, p <> q -> Path p q π -> ~ Path q p ϕ) -> (forall p, p -> p -> False) -> acyclic.
  Proof.
    intros. unfold acyclic. intros p q Hedge Hpath.
    destruct (L_dec p q);[rewrite e in *|];eauto.
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
      + cbn. erewrite IHPostfix; eauto; [|rewrite nlcons_to_list; reflexivity].
        simpl_nl; reflexivity.
  Qed.      

  Lemma postfix_path l p q q' l' :
    Path q' q l'
    -> Postfix (l :r: p) l'
    -> Path p q (l >: p).
  Proof.
    revert q q' l'. induction l; intros q q' l' Hl Hpost;cbn in *.
    - enough (ne_front l' = p) by (eapply path_front in Hl;subst;econstructor).
      destruct l';cbn in *;symmetry;eapply postfix_hd_eq;eauto.
    - rewrite nlcons_to_list in Hpost.
      eapply path_postfix_path in Hl as Hl'';eauto.
      replace (a :< (l ++ p :: nil)) with (a :<: l >: p) in Hl''.
      + cbn in Hl''. destruct l; simpl_nl' Hl'';cbn in Hl'';eauto.
      + clear. revert a. induction l; intros b; simpl_nl; cbn; eauto. rewrite <-IHl. reflexivity.
  Qed.

  Lemma succ_in_path_edge π (x y w z : L)
        (Hpath : Path x y π)
        (Hsucc : succ_in π w z)
    : edge z w = true.
  Proof.
    induction Hpath; unfold succ_in in Hsucc;destructH.
    - repeat destruct l1,l2; cbn in Hsucc; try congruence.
      destruct l2;cbn in Hsucc; congruence.
    - destruct l2.
      + cbn in Hsucc. inversion Hsucc;subst. inversion Hpath;subst;inversion H2;subst;eauto.
      + eapply IHHpath. exists l1, l2. inversion Hsucc; subst; eauto.
  Qed.

  Definition Path' π := Path (ne_back π) (ne_front π) π.

End graph.

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
  intro Hp. eapply Hacy; eauto.
  eapply subgraph_path' in Hp; eauto.
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

Ltac path_simpl' H :=
  lazymatch type of H with
  | Path ?edge ?x ?y (?z :<: ?π) => let Q := fresh "Q" in
                                   eapply path_front in H as Q;
                                   cbn in Q; subst z
  | Path ?edge ?x ?y (?π :>: ?z) => let Q := fresh "Q" in
                                   eapply path_back in H as Q;
                                   cbn in Q; subst z
  end.