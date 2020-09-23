
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Decidable.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Bool.Bool.
Require Import Lists.ListSet.
Require Import Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Utils.

Require Export ConvBoolTac ListOrder DecTac.

(** Graph **)

Section graph.

  Variable L : Type.
  Variables edge edge1 edge2 : L -> L -> Prop.
  Variable edge_dec : forall x y, dec (edge x y).

  Hypothesis L_dec : EqDec L eq.

  Local Notation "p --> q" := (edge p q) (at level 55, right associativity).
  Local Notation "p -->b q" := (if decision (edge p q) then true else false) (at level 55, right associativity).

  Inductive Path : L -> L -> list L -> Prop :=
  | PathSingle a : Path a a [a]
  | PathCons {a b c π} : Path a b π -> b --> c -> Path a c (c :: π).

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

  Lemma path_front p q r π
        (Hπ : Path p q (r :: π))
    : q = r.
  Proof.
    inversion Hπ;reflexivity.
  Qed.

  Ltac isabsurd :=
    match goal with
    | H : Path _ _ [] |- _ => inversion H
    | _ => try congruence'
    end.

  Lemma path_back p q r π
        (Hπ : Path p q (π ++ [r]))
    : p = r.
  Proof.
    revert dependent q.
    induction π;intros q Hπ;inversion Hπ;subst;cbn in *;eauto;try isabsurd.
  Qed.

  Ltac path_simpl' H :=
    let Q := fresh "Q" in
    lazymatch type of H with
    | Path ?x ?y (?z :: ?π) => replace z with y in *;
                                [|eapply path_front;eauto];
                                match type of H with
                                | Path _ _ (?w :: [])
                                  => fold ([] ++ [w]) in H;
                                    path_simpl' H;
                                    unfold app in H
                                | Path ?x ?y (?w :: ?z :: [])
                                  => fold ([w] ++ [z]) in H;
                                    path_simpl' H;
                                    unfold app in H
                                | _ => idtac
                                end
    | Path ?x ?y (?π ++ [?z]) => replace z with x in *;
                                   [|eapply path_back;eauto]
    end.

  Lemma path_dec p q π :
    {Path p q π} + {~ Path p q π}.
  Proof.
    revert q; induction π; intros q.
    - right. intro N. inversion N.
    - destruct π.
      + decide' (p == a).
        * decide' (p == q);[left;econstructor|].
          right. intro N. eapply c. inversion N;reflexivity.
        * right. intro N. eapply c. inversion N;subst. reflexivity. isabsurd.
      + decide' (q == a).
        * specialize (IHπ l). destruct IHπ.
          -- decide (l --> q).
             ++ left. econstructor;eauto.
             ++ right. intro N. inversion N. subst. path_simpl' H0. congruence.
          -- right. contradict n. inversion n;subst;eauto. path_simpl' H0. eauto.
        * right. intro N. inversion N;subst. congruence.
  Qed.

  Inductive ne_l : list L -> Prop :=
  | neCons a l : ne_l (a :: l).

  Lemma path_non_empty p q π
        (Hπ : Path p q π)
    : ne_l π.
  Proof.
    inversion Hπ;subst;econstructor.
  Qed.

  Lemma path_app π ϕ p q q' r : Path p q π -> q --> q' -> Path q' r ϕ -> Path p r (ϕ ++ π).
  Proof.
    intros Hπ Hedge Hϕ.
    induction Hϕ;cbn;econstructor;eauto.
  Qed.

  Lemma path_app' π ϕ p q r : Path p q π -> Path q r ϕ -> Path p r (ϕ ++ tl π).
  Proof.
    intros Hpath1 Hpath2.
    destruct π;cbn;inversion Hpath1;subst;eauto.
    - rewrite app_nil_r. eauto.
    - eapply path_app;eauto.
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

  Lemma path_glue_loop p r (π0 π1 : list L) :
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

(*  Lemma prefix_single {A : Type} (a : A) (l : list A)
    : Prefix [a] l -> hd_error (rev l) = Some a.
  Proof.
    intro H. induction l; inversion H; cbn; eauto; subst. inversion H2.
    destruct l; cbn in *; congruence.
  Qed.*)

  Ltac turn_cons a l :=
    let Q := fresh "Q" in
    let a' := fresh a in
    let l' := fresh l in
    rename l into l';
    rename a into a';
    specialize (cons_rcons a' l') as Q;
    destruct Q as [a [l Q]];
    rewrite Q in *.


  Lemma prefix_rcons_eq: forall (A : Type) (a b : A) (l l' : list A), Prefix (l ++ [a]) (l' ++ [b]) -> a = b.
  Proof.
    intros. eapply postfix_hd_eq. eapply prefix_rev_postfix'. cbn.
    do 2 rewrite rev_involutive. eauto.
  Qed.

  Lemma path_prefix_path p q r (π ϕ : list L)
    : Path p q π -> Prefix (r :: ϕ) π -> Path p r (r :: ϕ).
  Proof.
    intros Hpq Hpre.
    turn_cons r ϕ.
    replace r with p in *;cycle 1.
    { destr_r' π;subst π. 1: inversion Hpq.
      path_simpl' Hpq. symmetry. eapply prefix_rcons_eq. eauto.
    }
    enough (exists r, Path p r (ϕ :r: p)).
    { destructH. rewrite <-Q in *. path_simpl' H. auto. }
    clear Q.
    revert dependent q.
    dependent induction Hpre;intros.
    - path_simpl' Hpq. eauto.
    - inversion Hpq;subst. 1: inversion Hpre; congruence'.
      destr_r' l';subst l'. 1: inversion H3. path_simpl' H3.
      eapply IHHpre;eauto.
  Qed.

  Lemma path_app_inv p q t1 t2
        (Hpath : Path p q (t2 ++ t1))
        (Hnemp1 : t1 <> [])
        (Hnemp2 : t2 <> [])
    : exists b1 b2, Path p b1 t1 /\ Path b2 q t2.
  Proof.
    revert dependent q.
    induction t2; intros.
    - contradiction.
    - clear Hnemp2.
      destruct t2 as [| b2 t2 ].
      + clear IHt2. destruct t1 as [| b1 t1 ]; [ contradiction |]. clear Hnemp1.
        exists b1, a. split.
        eapply path_prefix_path; try eassumption.
        * rewrite prefix_eq. exists [a]. reflexivity.
        * eapply path_front in Hpath. subst. econstructor.
      + inv Hpath.
        destruct (IHt2) with (q := b2) as [a1 [a2 [Hp1 Hp2]]]; try eassumption.
        * intro. inv H.
        * eapply path_front in H3 as Heq. subst b. eassumption.
        * exists a1, a2. split. eassumption. econstructor. eapply Hp2.
          eapply path_front in H3. subst b. eassumption.
  Qed.

  Lemma path_front'
    : forall p q r π,
      Path p q π -> q = hd r π.
  Proof.
    intros.
    destruct π.
    - inversion H.
    - cbn. eapply path_front;eauto.
  Qed.

  Lemma path_back'
    : forall p q r π,
      Path p q π -> p = hd r (rev π).
  Proof.
    intros.
    destr_r' π;subst.
    - cbn in *. inversion H.
    - rewrite rev_rcons. cbn. eapply path_back;eauto.
  Qed.

  Lemma path_rcons p q r π
        (Hπ : Path p q π)
        (Hedge : r --> p)
    : Path r q (π ++ [r]).
  Proof.
    eapply path_app;eauto. econstructor.
  Qed.

  Lemma path_rcons_inv q r π
        (Hπ : Path r q (q :: π :r: r))
    : exists p, Path p q (q :: π).
  Proof.
    revert dependent q. induction π; intros q Hπ.
    - eexists. econstructor.
    - cbn in *. inversion Hπ. subst. path_simpl' H0. eapply IHπ in H0. destructH.
      eexists. econstructor;eauto.
  Qed.

  Lemma path_rcons_inv' q r π
        (Hπ : Path r q (q :: π :r: r))
    : exists p : L, Path p q (q :: π) /\ edge r p.
  Proof.
    revert dependent q. induction π; intros q Hπ.
    - eexists. split;[econstructor|].
      cbn in Hπ. inversion Hπ;subst. path_simpl' H0. auto.
    - cbn in *. inversion Hπ. subst. path_simpl' H0. eapply IHπ in H0. destructH.
      eexists. split;[econstructor|];eauto.
  Qed.

  Ltac turn_rcons l a :=
    let Q := fresh "Q" in
    let a' := fresh a in
    let l' := fresh l in
    rename l into l';
    rename a into a';
    specialize (rcons_cons a' l') as Q;
    destruct Q as [a [l Q]];
    rewrite Q in *.

  Lemma path_postfix_path p q r (π ϕ : list L)
    : Path p q π -> Postfix (ϕ ++ [r]) π -> Path r q (ϕ ++ [r]).
  Proof.
    intros Hπ Hpost.
    turn_rcons ϕ r.
    replace r with q in *;cycle 1.
    { destruct π. 1: inversion Hπ.
      path_simpl' Hπ. symmetry. eapply postfix_hd_eq;eauto.
    }
    enough (exists r, Path r q (q :: ϕ)).
    { destructH. rewrite <-Q in *.  path_simpl' H. auto. }
    clear Q.
    dependent induction Hpost generalizing p Hπ;intros;subst.
    - eauto.
    - inversion Hπ;subst.
      + rewrite cons_rcons' in H2. eapply rcons_inj in H2. cbn in H2. destruct H2. subst l' q.
        inversion Hpost. congruence'.
      + destruct l';cbn in *.
        * inversion Hpost. congruence'.
        * path_simpl' Hπ. rewrite <-cons_rcons_assoc in Hπ. path_simpl' Hπ.
          rewrite cons_rcons_assoc in Hπ. eapply path_rcons_inv in Hπ. destructH.
          eapply IHHpost;eauto.
  Qed.

  Lemma path_NoDup' p q ϕ : Path p q ϕ -> exists π, Path p q π /\ NoDup π.
  Proof.
    intros Hto.
    induction Hto.
    - exists ([a]). split;econstructor;eauto. econstructor.
    - destruct IHHto as [ψ [IHHto IHnodup]].
      destruct (@In_dec _ _ _ c ψ).
      + eapply prefix_nincl_prefix in H0.
        exists (c :: prefix_nincl c ψ). split.
        * eapply path_prefix_path in H0; eauto; cbn in *; eauto.
        * eapply prefix_NoDup; eauto.
      + exists (c :: ψ). split;econstructor;eauto.
  Qed.

  Lemma path_NoDup p q : p -->* q -> exists π, Path p q π /\ NoDup π.
  Proof.
    intros [ϕ Hto]. eapply path_NoDup';eauto.
  Qed.

  Lemma path_to_elem p q r π : Path p q π -> r ∈ π -> exists ϕ, Path p r ϕ /\ Prefix ϕ π.
  Proof.
    revert dependent q.
    induction π; intros q Hpath Hin; cbn in *; eauto.
    - contradiction.
    - path_simpl' Hpath. destruct Hin.
      + subst q. inversion Hpath.
        * eapply path_front in Hpath as Hfront. subst.
          eexists. split;econstructor.
        * subst; cbn in *. exists (r :: π); split; eauto.
          econstructor.
      + inversion Hpath; subst. 1: contradiction.
        eapply IHπ in H1;eauto. destructH. eexists.
        split;eauto.
        econstructor. eauto.
  Qed.

  Lemma path_from_elem' p q r π : Path p q π -> r ∈ π ->
                                  let ϕ := postfix_nincl r π ++ [r] in
                                  Path r q ϕ /\ Postfix ϕ π.
  Proof.
    intros Hpath Hin.
    assert (Postfix (postfix_nincl r π ++ [r]) π) as H;[|split];eauto.
    - eapply postfix_nincl_spec; eauto.
    - eapply path_postfix_path in Hpath;eauto.
  Qed.

  Lemma path_from_elem p q r π : Path p q π -> r ∈ π -> exists ϕ, Path r q ϕ /\ Postfix ϕ π.
  Proof.
    intros. eexists;eapply path_from_elem';eauto.
  Qed.

  Lemma path_from_elem_to_elem (p q r1 r2 : L) (π : list L)
        (Hπ : Path p q π)
        (Hprec : r2 ≻* r1 | π)
    : exists ϕ : list L, Path r1 r2 ϕ.
  Proof.
    eapply succ_rt_prefix in Hprec.
    destructH' Hprec.
    eapply path_prefix_path in Hprec0 as Hprec2. 2:eauto.
    eapply path_from_elem in Hprec2;eauto.
    destructH. eauto.
  Qed.

  Lemma path_front_eq p p' q q' π
    : Path p q π -> Path p' q' π -> q = q'.
  Proof.
    intros Hpq Hpq'.
    destruct Hpq;inversion Hpq';subst;auto.
  Qed.

  Lemma path_back_eq p p' q q' π
    : Path p q π -> Path p' q' π -> p = p'.
  Proof.
    intros Hpq Hpq'. revert dependent q'.
    induction Hpq;intros;inversion Hpq';subst;auto.
    - inversion H3.
    - inversion Hpq.
    - eauto.
  Qed.

  Lemma dom_nin r p q π : Dom r p q -> Path r p π -> NoDup π -> q ∈ π -> p = q.
  Proof.
    intros Hdom Hpath Hnd Hin. eapply path_to_elem in Hpath as Hpath';eauto.
    destruct Hpath' as [ϕ [Hϕ Hpre]].
    inversion Hpre; subst.
    - subst. eapply path_front_eq in Hpath;eauto.
    - path_simpl' Hpath.
      destruct Hin;[auto|exfalso].
      eapply Hdom in Hϕ as Hϕ'. eapply prefix_incl in Hϕ';eauto.
      inversion Hnd;subst. contradiction.
  Qed.

(*  Lemma in_ne_back {A : Type} `{EqDec A eq} (l : list A) : hd  ∈ l.
  Proof.
    induction l; cbn; eauto.
  Qed.*)

  Lemma path_contains_front (x y : L) l
        (Hpath : Path x y l)
    : y ∈ l.
  Proof.
    induction Hpath; cbn; eauto.
  Qed.

  Lemma path_contains_back (x y : L) l
        (Hpath : Path x y l)
    : x ∈ l.
  Proof.
    induction Hpath; cbn; eauto.
  Qed.

  Lemma dom_trans r h p q : r -->* h -> Dom r h p -> Dom r p q -> Dom h p q.
  Proof.
    intros Hϕ Hdom_h Hdom_p π Hπ.
    eapply path_NoDup in Hϕ as [ϕ [Hϕ Hndup]].
    eapply path_app' in Hπ as Hπ';eauto. eapply Hdom_p in Hπ'.
    eapply in_app_or in Hπ'.
    destruct Hπ'; eauto.
    enough (h = p).
    - subst h. eapply path_contains_back. eauto.
    - eapply dom_nin. 3: eassumption. 1: apply Hdom_h. 1: eauto.
      destruct ϕ; cbn in H; [contradiction|]. right; eauto.
  Qed.

  Definition intersection_edge := fun p q => edge1 p q /\ edge2 p q.

  Definition union_edge := fun p q => edge1 p q \/ edge2 p q.

  Definition minus_edge := fun p q => edge1 p q /\ ~ (edge2 p q).

  Definition sub_graph := forall p q, edge1 p q -> edge2 p q.

  Definition acyclic := forall p q π, p --> q -> Path q p π -> False.

  Lemma path_path_acyclic p q π ϕ : Path p q π -> Path q p ϕ -> p <> q -> ~ acyclic.
  Proof.
    intros Hpath1 Hpath2 Hneq Hacy.
    inversion Hpath1;[contradiction|].
    inversion Hpath2;subst;[contradiction|].
    specialize (Hacy b q (π0 ++ π1) H0). eapply Hacy.
    eapply path_app;eauto.
  Qed.

  Lemma path_path_acyclic' p q π ϕ : Path p q π -> Path q p ϕ -> acyclic -> p = q.
  Proof.
    intros Hpath1 Hpath2 Hacy.
    destruct (L_dec p q);[auto|]. eapply path_path_acyclic in c;eauto. contradiction.
  Qed.

  Lemma acyclic_NoDup p q π
        (Hpath : Path p q π)
        (Hacy : acyclic)
    : NoDup π.
  Proof.
    induction Hpath.
    - econstructor;eauto. econstructor.
    - econstructor;eauto. intro N. eapply path_from_elem in N; eauto. destructH. eapply Hacy;eauto.
  Qed.

  Lemma postfix_path l p q q' l' : (* FIXME: duplicate *)
    Path q' q l'
    -> Postfix (l ++ [p]) l'
    -> Path p q (l ++ [p]).
  Proof.
    intros Hpath Hpost.
    eapply path_postfix_path in Hpost;eauto.
  Qed.

  Lemma succ_in_path_edge π (x y w z : L)
        (Hpath : Path x y π)
        (Hsucc : succ_in π w z)
    : edge z w.
  Proof.
    induction Hpath; unfold succ_in in Hsucc;destructH.
    - repeat destruct l1,l2; cbn in Hsucc; try congruence.
      destruct l2;cbn in Hsucc; congruence.
    - destruct l2.
      + cbn in Hsucc. inversion Hsucc;subst. inversion Hpath;subst;auto.
      + eapply IHHpath. exists l1, l2. inversion Hsucc; subst; eauto.
  Qed.

  Lemma edge_path_hd_edge x y z π
        (Hedge : z --> x)
        (Hpath : Path x y (y :: π))
    : (hd z π) --> y.
  Proof.
    clear edge1 edge2.
    revert y Hpath.
    induction π;intros.
    - cbn. path_simpl' Hpath. auto.
    - cbn. inv Hpath. path_simpl' H0. auto.
  Qed.

  Lemma path_single (a b c : L)
        (Hpath : Path a b [c])
    : a = b /\ b = c.
  Proof.
    inversion Hpath.
    - subst; eauto.
    - inversion H3.
  Qed.

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

Lemma subgraph_path {L : Type} (edge1 edge2 : L -> L -> Prop) p q :
  sub_graph edge1 edge2 -> (exists π, Path edge1 p q π) -> (exists ϕ, Path edge2 p q ϕ).
Proof.
  intros Hsub [π Hpath]. unfold sub_graph in Hsub. induction Hpath.
  - exists ([a]). econstructor.
  - destruct IHHpath as [ϕ IHHpath]. exists (c :: ϕ). econstructor; eauto.
Qed.

Lemma subgraph_path' {L : Type} (edge1 edge2 : L -> L -> Prop) p q π :
  sub_graph edge1 edge2 -> Path edge1 p q π -> Path edge2 p q π.
Proof.
  intros Hsub Hpath. unfold sub_graph in Hsub. induction Hpath.
  - econstructor.
  - econstructor; eauto.
Qed.

Lemma acyclic_subgraph_acyclic {L : Type} (edge1 edge2 : L -> L -> Prop) :
  sub_graph edge1 edge2 -> acyclic edge2 -> acyclic edge1.
Proof.
  intros Hsub Hacy p q Hedge N. unfold acyclic, sub_graph in *.
  intro Hp. eapply Hacy; eauto.
  eapply subgraph_path' in Hp; eauto.
Qed.

Lemma union_subgraph1 (L : Type) (f g : L -> L -> Prop)
  : sub_graph f (f ∪ g).
Proof.
  unfold sub_graph, union_edge. intros. auto.
Qed.

Lemma minus_subgraph {L : Type} (edge1 edge2 : L -> L -> Prop) :
  sub_graph (edge1 ∖ edge2) edge1.
Proof.
  intros p q Hsub. unfold minus_edge in Hsub. conv_bool. firstorder.
Qed.

Lemma intersection_subgraph1 {L : Type} (edge1 edge2 : L -> L -> Prop) :
  sub_graph (edge1 ∩ edge2) edge1.
Proof.
  intros p q Hinter. unfold intersection_edge in Hinter. conv_bool. firstorder.
Qed.

Lemma intersection_subgraph2 {L : Type} (edge1 edge2 : L -> L -> Prop) :
  sub_graph (edge1 ∩ edge2) edge2.
Proof.
  intros p q Hinter. unfold intersection_edge in Hinter. conv_bool. firstorder.
Qed.

Lemma intersection2_subgraph {L : Type} (edge edge1 edge2 : L -> L -> Prop) :
  sub_graph edge1 edge2
  -> sub_graph (edge1 ∩ edge) (edge2 ∩ edge).
Proof.
  intros Hsub p q Hinter. unfold intersection_edge in *. unfold sub_graph in Hsub.
  conv_bool. destruct Hinter as [Hinter1 Hinter2]. auto.
Qed.

Lemma union_subgraph {L : Type} (edge1 edge1' edge2 edge2' : L -> L -> Prop) :
  sub_graph edge1 edge1' -> sub_graph edge2 edge2' -> sub_graph (edge1 ∪ edge2) (edge1' ∪ edge2').
Proof.
  intros Hsub1 Hsub2 p q Hu. unfold union_edge, sub_graph in *.
  conv_bool. destruct Hu as [Hu|Hu];firstorder 1.
Qed.

Lemma dom_intersection {L : Type} (edge1 edge2 : L -> L -> Prop) r p q :
  Dom edge1 r p q -> Dom (edge1 ∩ edge2) r p q.
Proof.
  intros Hdom.
  unfold Dom in *. intros. apply Hdom.
  eapply subgraph_path';eauto.
  eapply intersection_subgraph1.
Qed.

Lemma path_nlrcons (L : Type) (x y z : L) (l : list L) e
      (Hpath : Path e x y (l ++ [z]))
  : z = x.
Proof.
  revert dependent y.
  induction l;intros;cbn in *;inversion Hpath;subst;auto.
  - inversion H3.
  - congruence'.
  - eapply IHl;eauto.
Qed.


Ltac path_simpl' H :=
  let Q := fresh "Q" in
  lazymatch type of H with
  | Path ?e ?x ?y (?z :: ?π) => replace z with y in *;
                              [|eapply path_front;eauto];
                              match type of H with
                              | Path _ _ _ (?w :: [])
                                => fold ([] ++ [w]) in H;
                                  path_simpl' H;
                                  unfold app in H
                              | Path ?e ?x ?y (?w :: ?z :: [])
                                => fold ([w] ++ [z]) in H;
                                  path_simpl' H;
                                  unfold app in H
                              | _ => idtac
                              end
  | Path ?e ?x ?y (?π ++ [?z]) => replace z with x in *;
                                 [|eapply path_back;eauto]
  end.

Lemma path_rcons_rinv
  : forall (L : Type) (edge : L -> L -> Prop) (p q r : L) (π : list L),
    Path edge r p ((π :r: q) :r: r) -> Path edge q p (π :r: q).
Proof.
  clear.
  intros. revert dependent p. induction π;cbn in *;intros.
  - path_simpl' H. econstructor.
  - path_simpl' H. inversion H;[congruence'|subst].
    econstructor;eauto.
Qed.

Ltac path_simpl2' H :=
  let Q:= fresh "Q" in
  lazymatch type of H with
  | Path ?e ?x ?y (?z :: ?π) =>
    replace y with z in *; [ | symmetry;eapply path_front;eauto ];
                              match type of H with
                              | Path _ _ _ (?w :: [])
                                => fold ([] ++ [w]) in H;
                                  path_simpl' H;
                                  unfold app in H
                              | Path _ _ _ (?w :: ?z :: [])
                                => fold ([w] ++ [z]) in H;
                                  path_simpl' H;
                                  unfold app in H
                              | _ => idtac
                              end
  | Path ?e ?x ?y (?π ++ [?z]) => replace x with z in *; [ | symmetry;eapply path_back; eauto ]
  end.

Ltac inv_path H :=
  try path_simpl' H;
  let x := fresh "x" in
  inversion H as [ | ? x ]; subst;
  match goal with
  | Q : Path _ _ x _ |- _ => path_simpl2' Q
  | Q : Path _ _ _ [] |- _ => inversion Q
  | |- _ => idtac
  end.

Lemma acyclic_path_path (L : Type) (e : L -> L -> Prop)
  : (forall p q π ϕ, p <> q -> Path e p q π -> ~ Path e q p ϕ) -> (forall p q, e p q -> q <> p) -> acyclic e.
Proof.
  intros. intros p q π Hedge Hpath. revert p q Hedge Hpath.
  induction π;intros;inv_path Hpath.
  - eapply H0;eauto.
  - eapply H.
    + eapply H0. eapply Hedge.
    + eapply Hpath.
    + instantiate (1:=[q;p]).
      econstructor;eauto.
      econstructor.
Qed.
