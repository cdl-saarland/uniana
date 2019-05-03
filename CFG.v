
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

Require Import fin.FinTypes.

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
      reachability : forall q, (exists π, Path edge root q π);
      loop_contains qh q := exists p π, back_edge p qh /\ Path edge q p π /\ (qh ∉ π \/ q = qh);
      exit_edge h p q := loop_contains h p /\ ~ loop_contains h q /\ p --> q;
      single_exit : forall h p q, exit_edge h p q -> forall h', exit_edge h' p q -> h = h';
      loop_head h := exists p, back_edge p h;
      no_exit_head : forall h p q, exit_edge h p q -> ~ loop_head q;
      (*no_head_split : forall h p q, loop_head h -> h --> p -> h --> q -> p = q*)
    }.


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
  
  Instance Lab_dec : EqDec Lab eq.
  Proof.
    intros x y. destruct (decide_eq x y).
    - left. rewrite e. reflexivity.
    - right. eauto.
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

  Definition loop_head_b p : bool := to_bool (loop_head_dec p).
  Lemma loop_head_spec : forall p : Lab, loop_head_b p = true <-> loop_head p.
    prove_spec.
  Qed.

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

  Lemma loop_contains_dec qh q : dec (loop_contains qh q).
    unfold loop_contains. eauto.
    eapply finType_exists_dec. intros.
    (* proof idea : consider only dupfree paths, there are only finitely many of them. *)
  Admitted.
  Hint Resolve loop_contains_dec.
  
  Definition loop_contains_b qh q := to_bool (loop_contains_dec qh q).

  Lemma loop_contains_spec : forall qh q, loop_contains_b qh q = true <-> loop_contains qh q.
  Proof.
    intros. unfold loop_contains_b. destruct (loop_contains_dec qh q); cbn; split;eauto.
    intro. congruence.
  Qed.

  Definition deq_loop q p : Prop :=
    forall h, loop_contains h p -> loop_contains h q.

  Instance deq_loop_dec h p : dec( deq_loop h p).
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

  Lemma deq_loop_exited h qe e
        (Hexit : exit_edge h qe e)
    : deq_loop qe e.
  Proof.
  Admitted.
  
  Lemma deq_loop_exiting h qe e
        (Hexit : exit_edge h qe e)
    : deq_loop h qe.
  Admitted.
  
  Lemma deq_loop_trans p q r
        (H1 : deq_loop p q)
        (H2 : deq_loop q r)
    : deq_loop p r.
  Proof.
    unfold deq_loop in *. intros. eapply H1,H2;eauto.
  Qed.
  
  Lemma loop_contains_deq_loop h p
        (Hloop : loop_contains h p)
    : deq_loop p h.
  Admitted.

  

  Instance exit_edge_dec : forall h p q, dec (exit_edge h p q).
  Proof.
    intros; unfold exit_edge. eapply and_dec;[eauto| eapply and_dec];eauto. eapply not_dec. eauto.
  Qed.
  
  Definition exit_edge_b h p q : bool := to_bool (exit_edge_dec h p q).
  Lemma exit_edge_b_spec : forall h p q, exit_edge_b h p q = true <-> exit_edge h p q.
  Proof.
    prove_spec.
  Qed.
  
  Instance decide_decPred_bool (A : Type) (f : A -> bool) a : dec (if f a then True else False).
  Proof.
    cbn. destruct (f a); eauto.
  Qed.
  
  Definition decPred_bool (A : Type) (f : A -> bool) := DecPred (fun a => if f a then True else False).

  Definition finType_sub_decPred (X : finType) (p : decPred X) : finType.
  Proof.
    eapply (@finType_sub X p). eapply decide_pred. 
  Defined.

  Definition finType_sub_bool (X : finType) (p : X -> bool) : finType.
  Proof.
    eapply (@finType_sub X (decPred_bool p)). eauto. Show Proof.
  Defined.
  
  Definition depth (p : Lab) := Cardinality (finType_sub_bool (fun h => loop_contains_b h p)). 
  
  Definition innermost_loop h p : Prop :=  loop_contains h p /\ deq_loop h p.

  Lemma strong_reachability q
    : { π : ne_list Lab | Path edge root q π }.
  Admitted.
  
  Lemma ex_innermost_loop p
    : 0 < depth p -> { h : Lab | innermost_loop h p}.
  Proof.
    intros Hlt. unfold innermost_loop,deq_loop in *.
    specialize (strong_reachability) as [π Hπ].
    (* pick last header, but not if it has an exit, in Hπ, exists because of N *)
  Admitted.
  
  Definition get_innermost_loop (p : Lab) : Lab.
  Proof.
    destruct (depth p) eqn:E.
    - exact root.
    - assert (0 < depth p) by omega. eapply ex_innermost_loop in H as [h H]. exact h.
  Defined.
  
  Lemma get_innermost_loop_spec : forall p h, get_innermost_loop p = h <-> (depth p = 0 /\ h = root)
                                                                    \/ (innermost_loop h p).
  Proof.
  Admitted.

  Definition exiting (h p : Lab) : Prop :=
    exists q, exit_edge h p q.

  Definition exited (h q : Lab) : Prop :=
    exists p, exit_edge h p q.

  Global Instance exited_dec (h q : Lab) : dec (exited h q).
  Proof.
    unfold exited. 
    eapply finType_exists_dec; intros; eauto.
  Qed.

  Definition preds `{redCFG Lab edge} p : list Lab := filter (decPred_bool (fun q => edge q p)) (elem Lab). 

  Definition filter_loop h := filter (decPred_bool (loop_contains_b h)) (elem Lab).

  Definition In_b {A : Type} `{H : EqDec A eq} (a : A) (l : list A)
    := if in_dec H a l then true else false.

  Lemma loop_contains_loop_head (qh q : Lab)
    : loop_contains qh q -> loop_head qh.
  Proof.
    intro Q. unfold loop_head, loop_contains in *. destruct Q as [p [_ [Q _]]].
    eexists; eauto.
  Qed.

  Lemma back_edge_incl (p q : Lab) (Hback : p ↪ q) : p --> q.
  Proof. 
    unfold back_edge,back_edge_b in Hback. eapply minus_subgraph. eauto.
  Qed.

  Lemma back_edge_dec p q : {p ↪ q} + {~ p ↪ q}.
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
  
  Lemma loop_reachs_member (h q : Lab)
    : loop_contains h q -> h -->* q.
  Proof.
    intros Hloop. unfold loop_contains in Hloop.
    destructH.
    destruct Hloop3;[|subst q; eexists; econstructor].
    specialize (reachability q) as H'. destructH. eapply loop_head_dom in Hloop0.
    eapply path_app in Hloop2;eauto. eapply Hloop0 in Hloop2. eapply in_nl_conc in Hloop2.
    destruct Hloop2;[contradiction|].
    assert (h ∈ π0).
    { destruct π0; cbn in *;[contradiction|right;eauto]. }
    eapply path_from_elem in H1;eauto. firstorder. 
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
    decide (p = q); [subst;contradiction|].
    unfold loop_contains in Hloop. destructH.
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
      eapply back_edge_incl in H as Hreach. specialize (@reachability _ _ _ _ _ x) as Hreach'.
      destructH.
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
  
  Definition finType_sub_elem (h : Lab) (p : decPred Lab) : p h -> finType_sub_decPred p.
    intros H.
    econstructor. unfold pure. instantiate (1 := h). decide (p h);eauto.
  Defined.

  Open Scope prg.

  Definition restrict_edge (f : Lab -> Lab -> bool) (p : decPred Lab)
    : let L' := finType_sub_decPred p in L' -> L' -> bool
    := fun x y => (f (`x) (`y)).

  Definition loop_edge_dp (h : Lab) := decPred_bool (fun p => loop_contains_b h p).

  Lemma loop_edge_h_invariant (h : Lab) (H : loop_head h) : loop_edge_dp h h.
  Proof.
    unfold loop_edge_dp. cbn. destruct (loop_contains_b h h) eqn:E;[exact I|].
    rewrite <-not_true_iff_false in E. eapply E.
    rewrite loop_contains_spec. now eapply loop_contains_self.
  Qed.

End red_cfg.

Arguments finType_sub_elem {_}.
Arguments restrict_edge {_}.

(** * sub_CFG **)

Program Instance sub_CFG
        `{C : redCFG}
        (P : decPred Lab)
        (r : Lab)
        (HP : P r)
        (Hloop : forall p, P p -> loop_contains r p \/ r = root)
        (Hreach : forall p, exists π, Path (restrict_edge edge P)
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
  destruct h; destruct h'. destruct H12, H8.
  - admit.
  - admit.
  - admit.
  - rewrite <-H12. rewrite <-H8. reflexivity.
Admitted.
Next Obligation. (* no_head_exit *)
Admitted.

(** * loop_CFG **)

Instance loop_CFG
           `{C : redCFG}
           (h : Lab)
           (H : loop_head h)
  : @redCFG (finType_sub_decPred (loop_edge_dp h))
            (restrict_edge edge (loop_edge_dp h))
            (finType_sub_elem h (loop_edge_dp h) (loop_edge_h_invariant H))
            (restrict_edge a_edge (loop_edge_dp h)).
Proof.
  eapply sub_CFG; intros.
  - left. unfold loop_edge_dp in H0. cbn in H0. destruct (loop_contains_b h p) eqn:E;[|contradiction].
    eapply loop_contains_spec;eauto.
  - admit.
Admitted.

(*

Program Instance loop_CFG
        `{C : redCFG}
        (h : Lab)
        (H : loop_head h)
  : @redCFG (finType_sub_decPred (loop_edge_dp h))
            (restrict_edge (edge ∩ loop_edge h) (loop_edge_dp h))
            (finType_sub_elem h (loop_edge_dp h) (loop_edge_h_invariant H))
            (restrict_edge (a_edge ∩ loop_edge h) (loop_edge_dp h)).
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
  specialize reachability as H0. eapply subgraph_path in H0;eauto.
  unfold sub_graph,union_edge. firstorder.
Qed.
Next Obligation. (* single_exit *)
  (* new exits don't have new targets, and the source has the same depth *)
Admitted.
Next Obligation. (* no_head_exit *)
  (* new exits don't have new targets *)
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

(*Definition implode_edge `{redCFG} := (fun p q => deq_loop_b root p && deq_loop_b root q
                                              || deq_loop_b root p && loop_head_b q
                                              || loop_head_b p && deq_loop_b root q).*)
Definition implode_nodes `{C : redCFG}
  := decPred_bool (fun p => deq_loop_b root p
                         || (depth p ==b S (depth root)) && loop_head_b p).

Lemma implode_nodes_root_inv `{C : redCFG}
  : implode_nodes root.
Proof.
  unfold implode_nodes. cbn.
  assert (deq_loop_b root root = true) as H.
  {
    rewrite deq_loop_spec. unfold deq_loop. firstorder.
  }
  rewrite H. cbn. exact I.
Qed.      

Instance implode_CFG `(H : redCFG) (Hhe : head_exits_property H)
  : @redCFG (finType_sub_decPred implode_nodes)
            (restrict_edge edge implode_nodes)
            (finType_sub_elem root implode_nodes (implode_nodes_root_inv))
            (restrict_edge a_edge implode_nodes).
Proof.
  eapply sub_CFG;intros;[eauto|].
Admitted.
  

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

Definition local_impl_CFG `(C : redCFG) (h : Lab) : exists Lab' edge' root' a_edge',
    @redCFG Lab' edge' root' a_edge'.
Proof.
  decide (loop_head h).
  - specialize (loop_CFG C h l) as C1.
    specialize (head_exits_CFG C1) as C2.
    specialize (implode_CFG C2 (@head_exits_property_satisfied _ _ _ _ C1)) as C3.
    do 4 eexists. eapply C3.
  - specialize (head_exits_CFG C) as C2.
    specialize (implode_CFG C2 (@head_exits_property_satisfied _ _ _ _ C)) as C3.
    do 4 eexists. eapply C3.
Defined.


(** more parameters **)

Lemma Lab_dec' `{redCFG} : forall (l l' : Lab), { l = l' } + { l <> l'}.
Proof.
  apply Lab_dec.
Qed.

Parameter no_self_loops : forall `(C : redCFG), forall q p, edge q p = true -> q =/= p.
