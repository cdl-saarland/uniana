Require Export CFGancestor.

Section cfg.
  Context `{C : redCFG}.
  
  Notation "p '-a>b' q" := (a_edge p q) (at level 55).
  Notation "p '-a>' q" := (p -a>b q = true) (at level 55).
  Notation "p '-->b' q" := (edge p q) (at level 55).
  Notation "p '-->' q" := (p -->b q = true) (at level 55, right associativity).
  
  (** loop_CFG: remove everything outside the loop **)

  Lemma loop_contains_ledge_head (* unused *)h h' p
    : loop_contains h p -> p ↪ h' -> loop_contains h h'.
  Proof.
  Admitted.
  
  Definition finType_sub_elem (* unused *)(h : Lab) (p : decPred Lab) (H : p h)
    := (exist (fun x : Lab => pure p x) h (purify H)).

  Open Scope prg.

  Definition restrict_edge (A : finType) (f : A -> A -> bool) (p : decPred A)
    : let L' := finType_sub p (decide_pred p) in L' -> L' -> bool
    := fun x y => (f (`x) (`y)).

  Definition restrict_edge' (A : Type) (f : A -> A -> bool) (p : decPred A)
    := f ∩ ((fun a _ => to_bool (@decision (p a) (decide_pred p a)))
                             ∩ (fun _ b => to_bool (@decision (p b) (decide_pred p b)))).
  
  Lemma restrict_edge_intersection (A : finType) (f : A -> A -> bool) (p : decPred A) x y
    : restrict_edge f (p:=p) x y = restrict_edge' f p (`x) (`y).
  Proof.
    clear Lab edge root a_edge C.
    destruct x,y. 
    unfold restrict_edge',restrict_edge,intersection_edge. cbn.
    symmetry. destruct (f x x0);cbn;conv_bool;[split;eapply (pure_equiv (D:=decide_pred p));auto|reflexivity].
  Qed.
    
  Lemma restrict_edge_intersection_ex (* unused *)(A : finType) (f : A -> A -> bool) (p : decPred A) x y
  : (f ∩ (fun a _ => if decision (p a) then true else false) ∩ (fun _ b => to_bool (decision (p b)))) x y = true
    -> exists x' y', restrict_edge f (p:=p) x' y' = true /\ (`x') = x /\ (`y') = y.
    cbn.
  Admitted.

  Definition loop_nodes (h : Lab) := DecPred (fun p => loop_contains h p \/ exited h p).

(*  Lemma loop_edge_h_invariant (h : Lab) (H : loop_head h) : loop_nodes h h.
  Proof.
    unfold loop_nodes. cbn. now eapply loop_contains_self. 
  Qed.*)

End cfg.


Notation "↓ H" := (exist (fun x => pure (@predicate (eqtype (type _)) _) x) _ H) (at level 70).

Arguments restrict_edge {_}.

(** * sub_CFG **)

Open Scope prg.

Lemma original_path (L : Type) (P : decPred L) f π (r p : @subtype _ P (decide_pred P))
      (Hpath : Path (fun x y : subtype P => f (`x) (`y)) r p π)
  : Path f (`r) (`p) (ne_map (@proj1_sig L _) π).
Proof.
  induction Hpath.
  - cbn. econstructor.
  - cbn. econstructor;eauto.
Qed.

Lemma original_path' (L : finType) (P : decPred L) f π (r p : @subtype _ P (decide_pred P))
      (Hpath : Path (fun x y : subtype P (D:=decide_pred P) => f (`x) (`y)) r p π)
  : Path (restrict_edge' f P) (`r) (`p) (ne_map (@proj1_sig L _) π).
Proof.
  induction Hpath.
  - cbn. econstructor.
  - cbn. econstructor;eauto.
    rewrite <-restrict_edge_intersection.
    unfold restrict_edge. auto.
Qed.

Definition list_to_ne (* unused *)(A : Type) (l : list A) : option (ne_list A)
  := match l with
     | [] => None
     | a :: l => Some (a :< l)
     end.     

Lemma toSubList_eq (A : Type) (l : list A) (P : decPred A)
      (Hl : forall a, a ∈ l -> P a)
  : map (proj1_sig (P:=fun x => pure P x (D:=decide_pred P))) (toSubList l P) = l.
  induction l; cbn; eauto.
  decide (P a);cbn.
  - f_equal. eapply IHl. intros;eauto.
  - exfalso; eapply n; eauto.
Qed.

Lemma restrict_path_sat_P (L : finType) p q π (f : L -> L -> bool) (P : decPred L)
      (Hp : P p)
      (Hπ : Path (restrict_edge' f P) p q π)
      (x : L)
      (Hin : x ∈ π)
  : P x.
Proof.
  induction Hπ.
  - destruct Hin;[subst;auto|cbn in *;contradiction].
  - cbn in Hin. destruct Hin;[subst|eauto].
    unfold restrict_edge',intersection_edge in H. conv_bool. firstorder.
Qed.

Ltac cstr_subtype H :=
  let Heqqh := fresh "H" in 
  lazymatch type of H with
  | @predicate (eqtype (type ?Lab)) ?P ?y
    => assert (` (exist (fun x => pure P x (D:=decide_pred P)) y (purify H)) = y) as Heqqh by (cbn;auto);
      rewrite <-Heqqh in *; clear Heqqh
  end.

Ltac collapse x y :=
        let Q := fresh "Q" in 
        assert (purify x (D:=decide_pred _) = purify y (D:=decide_pred _)) as Q by (eapply pure_eq);
        rewrite Q in *;
        clear Q.
  
Ltac push_purify H :=
  let H' := fresh "H" in 
  eapply pure_equiv in H as H';
  assert (H = purify H') by eapply pure_eq;
  subst H.

Lemma original_path_reverse:
  forall (L : finType) (r : L) (π : ne_list L) (f : L -> L -> bool) (P : decPred L) (Hr : P r) (x : L) (Hx : P x) l,
    Path (restrict_edge' f P) r (` (↓ purify Hx (D:=decide_pred P)))
         (ne_map (proj1_sig (P:=fun x0 : L => pure P x0)) l) ->
    forall p : P x, Path (restrict_edge f P) (↓ purify Hr) (↓ purify Hx) l.
Proof. 
  intros L r π f P Hr x Hx l Hπ p.
  cbn in *.
  revert dependent x.
  induction l;intros;cbn.
  - destruct a.
    cbn in *. assert (x0 = x /\ r = x) as [Q1 Q2] by (split; inversion Hπ;subst;auto);subst.
    push_purify p0.
    collapse Hr Hx. collapse Hx H.
    econstructor.
  - destruct a.
    cbn in *. assert (x0 = x) as Q by (inversion Hπ;subst;auto);subst.
    push_purify p0.
    collapse Hx H.
    inversion Hπ;subst.
    assert (P b) as Hb.
    { unfold restrict_edge',minus_edge,intersection_edge in H4; conv_bool. firstorder. }
    cstr_subtype Hb.
    econstructor.
    + eapply IHl;eauto. 
    + rewrite restrict_edge_intersection. cbn in *; eauto.
      Unshelve. cbn. auto.
Qed.

Lemma restrict_edge_path_equiv (L : finType) r x π (f : L -> L -> bool) (P : decPred L)
      (Hr : P r)
      (Hx : P x)
      (Hπ : Path (restrict_edge' f P) r x π)
  : match toSubList π P with
    | a :: l => Path (restrict_edge f P) (↓ (purify Hr)) (↓ (purify Hx)) (a :< l)
    | nil => False
    end.
Proof.
  revert dependent x.
  induction π;intros.
  - cbn.
    assert (a = x /\ r = x) as [Q1 Q2] by (split;inversion Hπ;auto);subst.
    decide (P x).
    + cbn.
      collapse Hr Hx. collapse Hx p. econstructor.
    + contradiction. 
  - assert (a = x);subst.
    { inversion Hπ. reflexivity. }
    rewrite nlcons_necons in Hπ.
    specialize (restrict_path_sat_P Hr Hπ) as Hin.
    cstr_subtype Hx.
    setoid_rewrite <-toSubList_eq with (P:=P) in Hπ.
    2: { cbn in Hin. intros; eapply Hin. simpl_nl. cbn. firstorder. }
    rewrite <-ne_map_nlcons in Hπ.
    cbn.
    decide (P x).
    + 
      collapse Hx p.
      eapply original_path_reverse;eauto.
    + contradiction.
Qed.

Lemma subtype_ne_map (A : Type) (P : decPred A) (x : @subtype _ P (decide_pred P))
      (l : ne_list (@subtype _ P (decide_pred P)))
      (Hin : (` x) ∈ ne_map (proj1_sig (P:=fun x => pure P x)) l)
  : x ∈ l.
Proof.
  induction l.
  - cbn in *. destruct Hin;[left;eapply subtype_extensionality;auto|contradiction].
  - cbn in *. destruct Hin;[left;eapply subtype_extensionality;auto|].
    auto.
Qed.

Lemma restrict_edge_subgraph (A : finType) (f g : A -> A -> bool) P
      (Hsub : sub_graph f g)
  : sub_graph (restrict_edge f P) (restrict_edge g P).
Proof.
  unfold sub_graph in *. intros. unfold restrict_edge in *. eapply Hsub; auto.
Qed.

Lemma dom_restrict_subtype `{redCFG} r qh ql P 
      (Hdom : Dom (restrict_edge' edge P) r qh ql)
      (Hr : P r)
      (Hh : P qh)
      (Hl : P ql)
  : Dom (restrict_edge edge P) (↓ (purify Hr)) (↓ (purify Hh)) (↓ (purify Hl)).
Proof.
  unfold Dom. intros.
  eapply original_path' in H0. cbn in *.
  unfold Dom in Hdom.
  eapply Hdom in H0 as H0'.
  (*  eapply loop_head_dom with (qh0:=qh) in H0 as H0'.*)
  - cstr_subtype  Hh.
    eapply subtype_ne_map in H0';auto.
Qed.

Definition loop_contains' (L : Type) edge a_edge (qh q : L)
  := exists p π, (edge ∖ a_edge) p qh = true /\ Path edge q p π /\ qh ∉ tl (rev π).

Ltac to_loop_contains' :=
  match goal with
  | [C : redCFG ?edge ?root ?a_edge |- context [loop_contains ?h ?p]]
    => unfold loop_contains,back_edge,back_edge_b;
      fold (loop_contains' edge a_edge h p)
  end.

Definition exit_edge' (L : finType) (edge a_edge : L -> L -> bool) (h p q : L)
  := loop_contains' edge a_edge h p /\ ~ loop_contains' edge a_edge h q /\ edge p q = true.

Ltac fold_lp_cont' :=
  repeat lazymatch goal with
         | [H : context [exists _ _, (?edge ∖ ?a_edge) _ ?h = true /\ Path ?edge ?q _ _ /\ ?h ∉ tl (rev _) ] |- _]
           => unfold finType_sub_decPred in H;
             fold (loop_contains' edge a_edge h q) in H
         | [H : context [loop_contains' ?edge ?a_edge ?h ?p
                         /\ ~ loop_contains' ?edge ?a_edge ?h ?q /\ ?edge ?p ?q = true] |- _]
           => fold (exit_edge' edge a_edge h p q) in H
         | [ |- context [loop_contains' ?edge ?a_edge ?h ?p
                        /\ ~ loop_contains' ?edge ?a_edge ?h ?q
                        /\ ?edge ?p ?q = true]]
           => fold (exit_edge' edge a_edge h p q)
         | |- context [exists _ _, (?edge ∖ ?a_edge) _ ?h = true /\ Path ?edge ?q _ _ /\ ?h ∉ tl (rev _)]
           => unfold finType_sub_decPred;
             fold (loop_contains' edge a_edge h q)
         end.

Ltac unfold_edge_op := repeat unfold intersection_edge,restrict_edge',minus_edge,union_edge; conv_bool.
Ltac unfold_edge_op' H := repeat (unfold intersection_edge,restrict_edge',minus_edge,union_edge in H);
                          conv_bool.

Lemma restrict_back_edge_intersection (L : finType) (edge a_edge : L -> L -> bool) (P : decPred L)
      (x y : finType_sub P (decide_pred P))
  : (restrict_edge edge P ∖ restrict_edge a_edge P) x y
    = (restrict_edge' edge P ∖ restrict_edge' a_edge P) (` x) (` y).
Proof.
  destruct x,y.
  unfold_edge_op. unfold restrict_edge. cbn. 
  symmetry. destruct (edge x x0),(a_edge x x0);cbn;conv_bool.
  3,4: reflexivity.
  2: split;[split;eapply (pure_equiv (D:=decide_pred P));eauto|reflexivity].
  right.
  decide (P x); decide (P x0); cbn; auto; eapply pure_equiv in p; eapply pure_equiv in p0;
    try contradiction; split; auto.
Qed.           

Lemma restrict_back_edge (L : finType) (edge a_edge : L -> L -> bool) (p h : L) (P : decPred L)
      (Hp : P p)
      (Hh : P h)
      (Hback : (restrict_edge edge P ∖ restrict_edge a_edge P) (↓ (purify Hp)) (↓ (purify Hh)) = true)
  : (edge ∖ a_edge) p h = true.
Proof.
  unfold minus_edge,intersection_edge in *; conv_bool.
  destructH.
  split.
  - rewrite restrict_edge_intersection in Hback0. cbn in *. unfold restrict_edge',intersection_edge in Hback0.
    conv_bool. firstorder.
  - rewrite negb_true_iff in Hback1. eapply negb_true_iff.
    rewrite restrict_edge_intersection in Hback1. cbn in *. unfold restrict_edge',intersection_edge in Hback1.
    conv_bool. firstorder.
Qed.

Lemma map_tl (A B : Type) (f : A -> B) (l : list A)
  : map f (tl l) = tl (map f l).
Proof.
  induction l; cbn in *; eauto.
Qed.

Lemma restrict_loop_contains:
  forall (Lab : finType) (edge : Lab -> Lab -> bool) (a_edge : Lab -> Lab -> bool)
    (P : decPred Lab) (h : Lab) (Hh : pure P h) (p : Lab) 
    (Hp : pure P p),
    loop_contains' (restrict_edge edge P) (restrict_edge a_edge P) (↓ Hh) (↓ Hp) -> loop_contains' edge a_edge h p.
Proof.
  intros Lab edge a_edge P h Hh p Hp HloopA.
  unfold loop_contains' in *.
  destructH. cbn in *.
  eapply original_path in HloopA2. destruct p0. cbn in *.
  push_purify Hh.
  push_purify p0.
  eapply restrict_back_edge in HloopA0.
  exists x;eexists; split_conj; eauto.
  contradict HloopA3. cstr_subtype H. cbn in *.
  rewrite <-to_list_ne_map in HloopA3.
  rewrite <-map_rev in HloopA3.
  rewrite <-map_tl in HloopA3.
  rewrite in_map_iff in HloopA3.
  destructH. destruct x0. cbn in *.
  subst.
  replace (purify H) with p0;auto.
  eapply pure_eq.
Qed.

Lemma toSubList_rcons (A : Type) (l : list A) (P : decPred A) (a : A)
  : toSubList (l ++ [a]) P (D:=decide_pred P) = toSubList l P ++ match decision (P a) with
                                                                 | left Ha => [exist (pure P) a (purify Ha)]
                                                                 | right _ => nil
                                                                 end.
Proof.
  induction l; cbn; eauto.
  - decide (P a); decide (P a); [cbn;eauto;f_equal;f_equal;eapply pure_eq|contradiction|contradiction|reflexivity].
  - decide (P a0);decide (P a0). 2,3: contradiction. 
    + cbn. f_equal. eapply IHl. 
    + eapply IHl.
Qed.

Lemma toSubList_rev (A : Type) (l : list A) (P : decPred A)
  : toSubList (rev l) P (D:=decide_pred P) = rev (toSubList l P).
Proof.
  induction l; cbn in *; eauto.
  rewrite toSubList_rcons.
  decide (P a);decide (P a); try contradiction.
  - cbn. rewrite IHl.
    f_equal. f_equal. f_equal. apply pure_eq.
  - rewrite app_nil_r. eauto.
Qed.

Lemma toSubList_tl_incl (A : Type) (l : list A) (P : decPred A)
  : tl (toSubList l P) ⊆ toSubList (tl l) P (D:=decide_pred P).
Proof.
  induction l; cbn in *; eauto.
  decide (P a);cbn.
  - reflexivity.
  - eapply tl_incl.
Qed.  

Lemma loop_contains_restrict' `{redCFG} h q (P : decPred Lab)
      (Hh : P h)
      (Hq : P q)
      (Hloop : loop_contains' (restrict_edge' edge P) (restrict_edge' a_edge P) h q)
  : loop_contains' (restrict_edge edge P) (restrict_edge a_edge P) (↓ (purify Hh)) (↓ (purify Hq)).
Proof.
  unfold loop_contains' in *.
  destructH.
  decide (P p).
  - eapply restrict_edge_path_equiv in Hloop2 as Hloop2'.
    destruct (toSubList π P) eqn:E;
      [contradiction|].
    exists (↓ (purify p0)), (s :< l).
    split_conj.
    + unfold minus_edge in *. conv_bool. destruct Hloop0. split_conj; rewrite restrict_edge_intersection;cbn;eauto.
    + eapply Hloop2'.
    + Set Printing Coercions. simpl_nl. setoid_rewrite <-E. Unset Printing Coercions.
      contradict Hloop3. rewrite <-toSubList_eq with (P:=P);[|intros;eapply restrict_path_sat_P with (p:=q);eauto].
      2: { apply in_rev. apply tl_incl. auto. }
      eapply in_map_iff. exists (↓ purify Hh). split;cbn;auto.
      eapply toSubList_tl_incl. rewrite toSubList_rev. auto.
  - exfalso.
    unfold restrict_edge', minus_edge, intersection_edge in Hloop0. conv_bool. destructH.
    contradiction.
Qed.

Lemma restrict_exit_edge `{C : redCFG} (P : decPred Lab)
      (p : Lab)
      (Hp : P p)
      (q : Lab)
      (Hq : P q)
      (h : Lab)
      (Hh : P h)
      (Hloop : forall h p : Lab, (exists x, (restrict_edge' edge P ∖ restrict_edge' a_edge P) x h = true)
                            -> loop_contains' edge a_edge h p
                            -> P p
                            -> loop_contains' (restrict_edge' edge P) (restrict_edge' a_edge P) h p)
      (HloopB : loop_contains' (restrict_edge edge P) (restrict_edge a_edge P) (↓ (purify Hh)) (↓ (purify Hp)))
      (HnloopB : ~ loop_contains' (restrict_edge edge P) (restrict_edge a_edge P) (↓ (purify Hh)) (↓ (purify Hq)))
      (HedgeB : restrict_edge' edge P (` (↓ (purify Hp))) (` (↓ (purify Hq))) = true)
  : exit_edge h p q.
Proof.
  unfold exit_edge; split_conj.
  - eapply restrict_loop_contains;eauto.
  - contradict HnloopB. eapply loop_contains_restrict'; eauto.
    eapply Hloop;eauto. unfold loop_contains' in HloopB. destructH.
    clear - HloopB0.
    destruct p0. push_purify p.
    exists x.
    unfold minus_edge,intersection_edge in *. conv_bool. repeat rewrite restrict_edge_intersection in HloopB0.
    cbn in *. firstorder.
  - eapply intersection_subgraph1; unfold restrict_edge' in HedgeB;eauto.
Qed.

Instance sub_CFG
        `{C : redCFG}
        (P : decPred Lab)
        (HP : P root)
        (Hreach : forall p, P p -> exists π, Path (restrict_edge' a_edge P) root p π)
        (Hloop : forall h p, (exists x, (restrict_edge' edge P ∖ restrict_edge' a_edge P) x h = true)
                        -> loop_contains' edge a_edge h p
                        -> P p
                        -> loop_contains' (restrict_edge' edge P) (restrict_edge' a_edge P) h p)
  : @redCFG (finType_sub_decPred P)
            (restrict_edge edge P)
            (↓ (purify HP))
            (restrict_edge a_edge P).
econstructor.
{ (* loop_head_dom *)
  intros.
  destruct qh as [qh Qh].
  destruct ql as [ql Ql].
  push_purify Qh.
  push_purify Ql.
  eapply dom_restrict_subtype.
  unfold Dom.
  intros π Hπ.
  eapply loop_head_dom.
  - eapply restrict_back_edge in H. unfold back_edge, back_edge_b;eauto.
  - eapply subgraph_path' in Hπ;eauto. eapply intersection_subgraph1.
}
{ (* a_edge_incl *)
  eapply restrict_edge_subgraph;eauto.
}
{ (* a_edge_acyclic *)
  unfold acyclic. intros.
  rewrite restrict_edge_intersection in H. destruct p, q; cbn in *.
  eapply a_edge_acyclic.
  - eapply intersection_subgraph1;eauto.
  - eapply original_path in H0;eauto.
}
{ (* a_reachability *)
  destruct q.
  exploit Hreach; [eapply (pure_equiv (D:=decide_pred P));auto|].
  destructH.
  push_purify p.
  eapply restrict_edge_path_equiv in Hreach.
  destruct (toSubList π P);[contradiction|]. eauto.
}
{ (* single_exit *)
  intros h p q [HloopA [HnloopA HedgeA]] h' [HloopB [HnloopB HedgeB]].
  rewrite restrict_edge_intersection in HedgeA,HedgeB.
  destruct p as [p Hp]. destruct q as [q Hq].
  destruct h as [h Hh]. destruct h' as [h' Hh'].
  eapply subtype_extensionality. cbn. 
  apply (@single_exit _ _ _ _ C h p q).
  all: push_purify Hh; push_purify Hh'; push_purify Hq; push_purify Hp.
  all: fold_lp_cont'; eapply restrict_exit_edge; eauto.
}
{ (* no_exit_head *)
  intros h p q [HloopA [HnloopA HedgeA]] Hhead.
  fold_lp_cont'.
  destruct h,p,q.
  eapply no_exit_head.
  - push_purify p0; push_purify p; push_purify p1. eapply restrict_exit_edge;eauto.
    rewrite restrict_edge_intersection in HedgeA. eauto.
  - destruct Hhead. destruct x2. exists x2. eapply restrict_back_edge;eauto.
    Unshelve.
    exact P.
    apply pure_equiv with (D:=decide_pred P);eauto.
    apply pure_equiv with (D:=decide_pred P);eauto.
}
{ (* exit_pred_loop *)
  intros ? ? ? ? [HloopA [HnloopA HedgeA]] Hedge1.
  destruct h,q,qe,e.
  fold_lp_cont'. 
  push_purify p0. push_purify p1. push_purify p2. push_purify p.
  eapply loop_contains_restrict'.
  eapply Hloop.
  - clear - HloopA. destruct HloopA as [x3 [_ [Hthis _]]].
    destruct x3. push_purify p.
    exists x0. cstr_subtype H. cstr_subtype H2. rewrite <-restrict_back_edge_intersection. eauto.
  - eapply exit_pred_loop with (h:=x).
    eapply (restrict_exit_edge (p:=x1) (Hp:=H0) (q:=x2)(Hq:=H1)(Hh:=H2));eauto.
    + rewrite restrict_edge_intersection in HedgeA;eauto.
    + rewrite restrict_edge_intersection in Hedge1.
      eapply intersection_subgraph1;eauto.
  - auto.
}
{ (* no_self_loops *)
  intros.
  destruct q. destruct p.
  intro Heq. eapply subtype_extensionality in Heq.
  eapply no_self_loops;eauto.
}
{ (* root_no_pred *)
  intros.
  destruct p. push_purify p. intro N.
  eapply root_no_pred.
  rewrite restrict_edge_intersection in N.
  eapply intersection_subgraph1 in N. cbn in N. eauto.
}
Qed.

(** * loop_CFG **)

Definition purify_head `{C : redCFG} h
      (H : loop_head h)
  : pure (loop_nodes h) h (D:=decide_pred (loop_nodes h))
  := purify (or_introl (loop_contains_self H)).


Lemma all_sat_restrict_edge'
      (L : Type)
      (f : L -> L -> bool)
      (p q : L)
      (π : ne_list L)
      (Hπ : Path f p q π)
      (P : decPred L)
      (Hsat :  forall x : L, x ∈ π -> P x)
  : Path (restrict_edge' f P) p q π.
Proof.
  induction Hπ.
  - econstructor.
  - econstructor.
    + eapply IHHπ. intros; eapply Hsat. cbn. firstorder.
    + unfold_edge_op; split_conj; eauto; eapply Hsat; cbn; auto.
      right. eapply path_contains_front;eauto.
Qed.

Lemma exit_a_edge `{redCFG} h p q
      (Hexit : exit_edge h p q)
  : a_edge p q = true.
Proof.
  destruct (a_edge p q) eqn:E;[auto|exfalso].
  eapply no_exit_head;eauto.
  unfold exit_edge in Hexit. destructH.
  exists p. unfold back_edge, back_edge_b. unfold_edge_op. split; auto.
  rewrite negb_true_iff; auto.
Qed.

Lemma neconc_app (A : Type) (l l' : ne_list A)
  : l ++ l' = l :+: l'.
Proof.
  induction l;cbn;eauto.
  rewrite IHl. reflexivity.
Qed.

Lemma nl_cons_lr_shift (A : Type) (a b : A) (l : list A)
  : (a :<: (l >: b)) = ((a :< l) :>: b).
Proof.
  revert a.
  induction l; intros; cbn ; eauto.
  fold ((ne_rcons (a :< l) b)). rewrite IHl. reflexivity.
Qed.

Lemma NoDup_app (A : Type) (l l' : list A)
  : NoDup (l ++ l') -> forall a, a ∈ l -> a ∉ l'.
Proof.
  induction l; intros; cbn; [contradiction|].
  inversion H;subst.
  destruct H0; subst.
  - contradict H3. eapply in_app_iff. firstorder.
  - eapply IHl;auto.
Qed.

Lemma acyclic_path_stays_in_loop `{C : redCFG} (h p q : Lab) π
      (Hpath : Path a_edge p q π)
      (Hp : loop_contains h p)
      (Hq : loop_contains h q)
  : forall x, x ∈ π -> loop_contains h x.
Proof.
  enough (h ∉ tl (rev π)) as Hnin.
  - intros.
    eapply subgraph_path' in Hpath;eauto.
    eapply (path_from_elem) in Hpath as Hϕ;eauto. destructH.
    unfold loop_contains in Hq.
    destructH.
    exists p0, (π0 :+ tl ϕ); split_conj; auto.
    + eapply path_app;eauto.
    + destruct ϕ;cbn;[auto|].
      assert (e = q) by (clear - Hϕ0; inversion Hϕ0; subst; eauto);subst.
      rewrite <-nlconc_neconc.
      rewrite <-neconc_app. rewrite rev_app_distr.
      replace (tl (rev ϕ ++ rev π0)) with ((tl (rev ϕ)) ++ rev π0).
      * intro N. eapply in_app_or in N.
       destruct N.
        -- apply Hnin. clear - Hϕ1 H0. destruct (ne_list_nlrcons π). destructH. subst. simpl_nl' Hϕ1. simpl_nl.
           rewrite rev_rcons. cbn.
           eapply postfix_rev_prefix in Hϕ1. rewrite rev_rcons in Hϕ1.
           destruct (ne_list_nlrcons ϕ). destructH;subst. simpl_nl' Hϕ1.
           rewrite nl_cons_lr_shift in Hϕ1. simpl_nl' Hϕ1. rewrite rev_rcons in Hϕ1.
           simpl_nl' H0. rewrite rev_rcons in H0. cbn in H0.
           eapply prefix_cons_cons in Hϕ1.
           eapply prefix_incl in Hϕ1. eapply in_rev in H0. 
           specialize (Hϕ1 h). eapply Hϕ1.
           rewrite <-in_rev. right;auto.
        -- eapply nin_tl_iff in Hq3;auto. destruct Hq3 as [Hq3|Hq3]; [eapply Hq3;eapply in_rev;auto|].
           eapply path_back in Hq2. rewrite Hq2 in Hq3. subst h.
           eapply Hnin. clear - Hϕ1.
           destruct (ne_list_nlrcons π). destructH. rewrite H. simpl_nl. rewrite rev_rcons. cbn.
           rewrite H in Hϕ1. simpl_nl' Hϕ1.
           destruct l';[exfalso|];inversion Hϕ1; subst; cbn in *; try congruence'.
           destruct l'; cbn in *. inversion H2. 1,2: destruct l'; cbn in *; congruence.
           ++ eapply in_or_app. right;firstorder.
           ++ eapply postfix_hd_eq in Hϕ1. subst. eapply in_or_app. firstorder.
      * clear. destruct (ne_list_nlrcons ϕ). destructH. rewrite H. simpl_nl. rewrite rev_rcons. cbn. reflexivity.
  - intro N.
    specialize (a_reachability p) as [ϕ Hϕ].
    eapply dom_loop in Hp.
    eapply dom_dom_acyclic in Hp.
    eapply Hp in Hϕ as Hin.
    eapply path_app in Hpath as Hpath';eauto.
    eapply acyclic_path_NoDup in Hpath' as Hnd. rewrite <-nlconc_to_list in Hnd.
    enough (π ++ tl ϕ = rev (tl (rev π)) ++ ϕ).
    + rewrite H in Hnd.
      eapply NoDup_app;eauto.
      rewrite <-in_rev. auto.
    + clear - Hpath Hϕ.
      destruct (ne_list_nlrcons π). destructH. subst.
      simpl_nl. rewrite rev_rcons. cbn. rewrite rev_involutive.
      eapply path_back in Hpath. simpl_nl' Hpath. subst x.
      destruct ϕ;cbn in *;simpl_nl.
      * inversion Hϕ; subst. rewrite app_nil_r. reflexivity.
      * inversion Hϕ; subst. unfold rcons. rewrite <-app_assoc. cbn. reflexivity.
Qed.

Instance loop_CFG
           `(C : redCFG)
           (h : Lab)
           (H : loop_head h)
  : @redCFG (finType_sub_decPred (loop_nodes h))
            (restrict_edge edge (loop_nodes h))
            (↓ (purify_head H))
            (restrict_edge a_edge (loop_nodes h)).
Proof. (* this proof is broken since I have changed sub_CFG *)
  unfold purify_head. 
  eapply sub_CFG; intros.
  - assert (forall p, loop_contains h p -> exists π : ne_list Lab, Path (restrict_edge' a_edge (loop_nodes h)) h p π) as Hloo.
    {
      clear.
      intros.
      specialize (a_reachability p) as [π Hπ].
      eapply dom_loop with (h0:=h) in H as Hdom;eauto.
      eapply dom_dom_acyclic in Hdom.
      eapply Hdom in Hπ as Hϕ.
      eapply path_from_elem in Hϕ;eauto. destructH.
      exists ϕ. eapply all_sat_restrict_edge';auto.
      intros. left.
      eapply acyclic_path_stays_in_loop;eauto.
      eapply loop_contains_self. eapply loop_contains_loop_head;eauto.
    }
    destruct H0;auto.
    unfold exited in H0. destructH. 
    copy H0 Hexit.
    unfold exit_edge in H0. destructH. exploit Hloo.
    destructH.
    exists (p :<: π). econstructor;eauto.
    unfold_edge_op.
    split_conj;[eapply exit_a_edge;eauto|left;auto|right;eexists;eauto].
  - clear H2.
    enough (loop_contains h h0). 
    + unfold loop_contains' in *.
      destructH' H1.
      exists p0, π. split_conj;[| |apply H5].
      * unfold_edge_op.
        assert (loop_contains h0 p0).
        {
          exists p0, (ne_single p0).
          split_conj;[unfold back_edge; auto|econstructor|contradict H5;cbn in H5;contradiction].
        }
        unfold_edge_op' H3. destruct H3. split_conj;eauto;unfold loop_nodes;cbn;left;auto.
        eapply loop_contains_trans;eauto.
      * specialize (loop_contains_ledge_path H3 H1 H5) as Hle.
        eapply all_sat_restrict_edge';auto.
        intros. unfold loop_nodes. cbn. left. eapply loop_contains_trans;eauto.
    + clear - H0.
      destructH.
      assert (loop_head h0).
      {
        decide (loop_nodes h x);decide (loop_nodes h h0).
        2-4: exfalso;unfold_edge_op' H0; destruct H0; destructH; contradiction.
        cstr_subtype p.
        cstr_subtype p0.
        rewrite <-restrict_back_edge_intersection in H0.
        eapply restrict_back_edge in H0.
        cbn. exists x. auto.
      } 
      unfold_edge_op' H0. destruct H0. destruct H0 as [_ [_ H0]]. destruct H0;auto.
      unfold exited in H0. destructH.
      eapply no_exit_head in H0;contradiction.
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


(* Definition implode_nodes `{C : redCFG}
  := DecPred (fun p => (deq_loop root p
                     \/ (depth p = S (depth root)) /\ loop_head p)).

Definition implode_nodes' `{C : redCFG}
  := DecPred (fun p => (deq_loop root p
                     \/ exists q, edge p q = true /\ loop_head p /\ deq_loop root q)). *)

Definition implode_nodes `{C : redCFG} (r : Lab)
  := DecPred (fun p => (deq_loop r p
                     \/ exists e, exited p e /\ deq_loop r e)).


Definition get_root `(C : redCFG) := root.

Arguments loop_CFG {_ _ _ _} _.

Lemma loop_CFG_head_root (* unused *)`{C : redCFG} (h : Lab)
      (Hhead : loop_head h)
      (D := loop_CFG C h Hhead)
  : get_root D = loop_CFG_elem C h h (loop_contains_self Hhead).
Proof.
  unfold get_root. unfold loop_CFG_elem.
Admitted.


Definition top_level (* unused *)`{redCFG} q := forall h, loop_contains h q -> (h = root \/ h = q).

Arguments loop_CFG {_ _ _ _} (_).

(** * head_exits **)

Definition head_exits_edge `{redCFG} h h' q : bool
  := if decision (exited h' q /\ ~ loop_contains h' h) then true else false. 

Lemma head_exits_edge_spec :
  forall `{redCFG} h h' q, head_exits_edge h h' q = true -> exists p, exit_edge h' p q.
Proof.
  intros. unfold head_exits_edge in H0. decide (exited h' q); cbn;eauto.
  decide (exited h' q /\ ~ loop_contains h' h);[|congruence]. destructH. contradiction.
Qed.

Lemma head_exits_edge_spec_iff :
  forall `{redCFG} h h' q, head_exits_edge h h' q = true <-> (exists p, exit_edge h' p q) /\ ~ loop_contains h' h.
Proof.
  intros. unfold head_exits_edge. decide (exited h' q /\ ~ loop_contains h' h).
  - split;intros;[|reflexivity]. firstorder.
  - split;intros;[congruence|]. simpl_dec' n. destructH. unfold exited in n.
    destruct n as [n|n];[simpl_dec' n; specialize (n p)|]; contradiction.
Qed.

Lemma head_exits_path `{redCFG} h p q :
  head_exits_edge h p q = true -> exists π, Path a_edge p q π.
Proof.
  intros. cbn.
  eapply head_exits_edge_spec in H0.
  destructH.
  copy H0 Hexit.
  unfold exit_edge in H0. destructH.
  eapply loop_reachs_member in H1.
  destructH.
  exists (q :<: π).
  eapply exit_a_edge in Hexit.
  econstructor;eauto.
Qed.

Lemma acyclic_parallel_exit_path `{redCFG} h p q π
      (Hπ : Path a_edge h q π)
      (Hexit : exit_edge h p q)
  : forall x, x ∈ tl π -> loop_contains h x.
Proof.
  destruct π;cbn in *;[contradiction|].
  assert (e = q) by (inversion Hπ;cbn in *;subst;auto);subst.
  inversion Hπ;subst.
  intros.
  eapply acyclic_path_stays_in_loop;eauto.
  - eapply loop_contains_self;unfold exit_edge in Hexit; destructH ;eauto using loop_contains_loop_head.
  - eapply exit_pred_loop;eauto.
    eapply a_edge_incl;eauto.
Qed.

Lemma head_exits_in_path_head_incl `{redCFG} qh ql π
      (Hπ : Path (edge ∪ (head_exits_edge qh)) root ql π)
  : exists ϕ, Path edge root ql ϕ /\ forall (h : Lab), loop_contains h ql -> h ∈ ϕ -> h ∈ π.
Proof.
  remember ql as ql'.
  setoid_rewrite Heqql' at 2.
  assert (deq_loop ql' ql) as Hdeq by (subst;eapply deq_loop_refl).
  clear Heqql'.
  revert dependent ql.
  induction Hπ;intros;cbn;eauto.
  - eexists;split;econstructor;eauto. inversion H1;subst;auto. inversion H2.
  - unfold_edge_op' H0. destruct H0.
    + specialize (IHHπ b). exploit IHHπ;[eapply deq_loop_refl|]. destructH.
      exists (c :<: ϕ). split;[econstructor;eauto|].
      intros. cbn in H2. destruct H2;eauto.
      eapply Hdeq in H1.
      decide (h = c);[left;auto|].
      eapply preds_in_same_loop in H1;eauto.
    + eapply head_exits_path in H0 as Hψ. destruct Hψ as [ψ Hψ].
      specialize (IHHπ c). exploit IHHπ.
      * eapply head_exits_edge_spec in H0. destructH.
        eapply deq_loop_trans;[eapply deq_loop_exiting;eauto|eapply deq_loop_exited;eauto].
      * destructH.
        eexists. split;[eauto using path_app,subgraph_path'|].
        intros.
        eapply in_nl_conc in H2. destruct H2.
        -- left.
           
           eapply head_exits_edge_spec in H0. destructH.
           decide (c = h);[auto|].
           eapply acyclic_parallel_exit_path in Hψ;eauto.
           ++ eapply loop_contains_trans in H1;eauto.
              eapply Hdeq in H1.
              unfold exit_edge in H0. destructH. contradiction.
           ++ destruct Hψ;cbn in *;destruct H2. 1-3: contradiction. auto.
        -- right;eauto using tl_incl. eapply IHHπ1. eapply Hdeq;auto. eapply tl_incl. auto.
Qed.

Lemma head_exits_back_edge `{redCFG} ql qh h :
  ((edge ∪ (head_exits_edge h)) ∖ (a_edge ∪ (head_exits_edge h))) ql qh = true <-> ql ↪ qh.
Proof.
  unfold back_edge,back_edge_b.
  unfold_edge_op. split;intros. 
  - destructH. destruct H1;[eauto|].
    destruct (head_exits_edge h ql qh);cbn in *;congruence.
  - split_conj;[firstorder|firstorder|].
    unfold head_exits_edge.
    decide (exited ql qh /\ ~ loop_contains ql h);[|cbn;auto].
    exfalso.
    unfold exited in a.
    destructH' a.
    eapply no_exit_head;eauto.
    exists ql. unfold back_edge,back_edge_b;conv_bool. unfold_edge_op. eauto.
Qed.

Lemma loop_contains_ledge `{C : redCFG} qh ql
  : ql ↪ qh -> loop_contains qh ql.
Proof.
  intros. exists ql, (ne_single ql). split_conj;[auto|constructor|cbn]. exact (fun x => x).
Qed.

Lemma head_exits_no_self_loop `{redCFG} h p q : head_exits_edge h p q = true -> p <> q.
Proof.
  intros. eapply head_exits_edge_spec in H0.
  destructH.
  unfold exit_edge in H0. destructH.
  eapply loop_contains_loop_head in H1.
  eapply loop_contains_self in H1.
  intro N;subst.
  contradiction.
Qed.

Lemma head_exits_same_connected `{redCFG} h p q π
      (Hpath : Path (a_edge ∪ (head_exits_edge h)) p q π)
  : exists ϕ, Path a_edge p q ϕ.
Proof.
  induction Hpath;cbn;eauto.
  - eexists. econstructor.
  - destructH. unfold_edge_op' H0. destruct H0.
    + eexists. econstructor;eauto.
    + eapply head_exits_path in H0. destructH.
      eexists; eauto using path_app.
Qed.

Lemma head_exits_same_connected' (* unused *)`{redCFG} h p q π
      (Hpath : Path (edge ∪ (head_exits_edge h)) p q π)
  : exists ϕ, Path edge p q ϕ.
Proof.
  induction Hpath;cbn;eauto.
  - eexists. econstructor.
  - destructH. unfold_edge_op' H0. destruct H0.
    + eexists. econstructor;eauto.
    + eapply head_exits_path in H0. destructH.
      eapply subgraph_path' in H0;eauto.
      eexists; eauto using path_app.
Qed.


Ltac ne_r_destruct l :=
  let H := fresh "H" in
  specialize (ne_list_nlrcons l) as H;
  destruct H as [? [? ?]]; subst l.

Lemma union_subgraph1 (L : Type) (f g : L -> L -> bool)
  : sub_graph f (f ∪ g).
Proof.
  unfold sub_graph, union_edge. intros. rewrite H. cbn. reflexivity.
Qed.

Lemma head_exits_loop_equivalence `{redCFG} qh h p
  : loop_contains h p <-> loop_contains' (edge ∪ (head_exits_edge qh)) (a_edge ∪ (head_exits_edge qh)) h p.
Proof.
  split;intros.
  - unfold loop_contains'. unfold loop_contains in H0.
    destructH.
    exists p0, π.
    split_conj.
    + eapply head_exits_back_edge;eauto.
    + clear - H0.
      induction H0;econstructor;eauto. unfold_edge_op. left;auto.
    + auto.
  - copy H0 H0'.
    unfold loop_contains. unfold loop_contains' in H0.
    destructH.
    assert (Path (edge ∪ (head_exits_edge qh)) p p0 π -> h ∉ tl (rev π)
            -> loop_contains h p0
            -> exists π0, Path edge p p0 π0 /\ h ∉ tl (rev π0)).
    {
      clear. intros.
      induction H0.
      - exists (ne_single a). split;eauto. econstructor.
      - exploit' IHPath.
        + cbn in *. contradict H1.
          specialize (ne_list_nlrcons π) as Hπ. destructH. subst π.
          simpl_nl. rewrite rev_rcons. cbn. simpl_nl' H1. rewrite rev_rcons in H1. cbn in *.
          eapply in_or_app. left;auto.
        + unfold_edge_op' H3. destruct H3.
          * exploit IHPath.
            {
              eapply preds_in_same_loop;eauto.
              contradict H1. subst.
              cbn. ne_r_destruct π. simpl_nl. rewrite rev_rcons. cbn. eapply in_or_app. right;firstorder.
            }
            destructH.
            exists (c :<: π0). split;[econstructor;eauto|].
            contradict IHPath1.
            ne_r_destruct π0.
            simpl_nl. cbn. rewrite rev_rcons. cbn. simpl_nl' IHPath1.
            rewrite nl_cons_lr_shift in IHPath1. simpl_nl' IHPath1.  rewrite rev_rcons in IHPath1. cbn in *.
            fold (rcons (rev x0) c) in IHPath1. eapply In_rcons in IHPath1. destruct IHPath1;auto.
            subst h. exfalso. contradict H1. fold (rcons (rev π) c).
            ne_r_destruct π.
            simpl_nl. cbn. rewrite rev_rcons. cbn. eapply in_or_app. right;firstorder.
          * eapply head_exits_edge_spec in H3 as Hexit. destruct Hexit as [qe Hexit].
            assert (loop_contains h b) as Hloop.
            {
              eapply deq_loop_exiting;eauto.
              eapply deq_loop_exited;eauto.
            }
            exploit IHPath.
            destructH.
            eapply head_exits_path in H3. destructH.
            exists (π1 :+ tl π0).
            split.
            -- eapply subgraph_path' in H3; [eapply path_app|];eauto.
            -- rewrite <-nlconc_to_list.
               intro N. rewrite rev_app_distr in N.
               enough (h ∉ rev π1).
               {
                 destruct π0;cbn in N;eapply H4;[eapply tl_incl;auto|].
                 ne_r_destruct π0. cbn in *. simpl_nl' IHPath1. simpl_nl' N. rewrite rev_rcons in N,IHPath1.
                 cbn in *.
                 eapply in_app_or in N. destruct N;[exfalso;apply IHPath1|contradiction].
                 eapply in_or_app. left;auto.
               }
               rewrite <-in_rev.
               clear - H3 Hexit H2 Hloop.
               decide (h = c).
               {
                 subst.
                 exfalso.
                 eapply no_exit_head;eauto using loop_contains_loop_head.
               }      
               inversion H3;subst.
               ++ cbn. firstorder.
               ++ cbn. simpl_dec. split;[auto|].
                  intro Hin.
                  eapply acyclic_path_stays_in_loop in Hin;auto;cycle 1.
                  ** eauto.
                  ** unfold exit_edge in Hexit. destructH. eapply loop_contains_self.
                     eapply loop_contains_loop_head;eauto.
                  ** eapply a_edge_incl in H1.
                     eapply exit_pred_loop;eauto.
                  ** eapply loop_contains_Antisymmetric in Hin. exploit Hin. subst.
                     unfold exit_edge in Hexit; destructH; contradiction.
    }
    exists p0.
    exploit H2.
    {
      rewrite head_exits_back_edge in H1. eapply loop_contains_ledge;eauto.
    }
    destructH.
    eexists;split;eauto.
    eapply head_exits_back_edge;eauto.
Qed.

Lemma exit_edge_pred_exiting `{redCFG} h p q
      (Hexit : exit_edge h p q)
      (p' : Lab)
      (Hedge : edge p' q = true)
  : exit_edge h p' q.
Proof.
  copy Hexit Hexit'.
  unfold exit_edge; unfold exit_edge in Hexit. destructH.
  split_conj;eauto.
  eapply exit_pred_loop;eauto.
Qed.
  
(*Lemma head_exits_exit_edge_destruct `{redCFG} h p q
      (Hexit : exit_edge' (edge ∪ head_exits_edge) (a_edge ∪ head_exits_edge) h p q)
  : exit_edge h p q \/ h = p /\ exists p', *)

Lemma head_exits_exit_edge `{redCFG} qh h p q
      (Hexit : exit_edge' (edge ∪ (head_exits_edge qh)) (a_edge ∪ (head_exits_edge qh)) h p q)
  : exists p', exit_edge h p' q.
Proof.
  unfold exit_edge' in *. destructH.
  unfold_edge_op' Hexit3.
  destruct Hexit3.
  - exists p. unfold exit_edge. split_conj.
    1,2: rewrite head_exits_loop_equivalence;eauto.
    auto.
  - eapply head_exits_edge_spec in H0.
    destructH. exists p0.
    unfold exit_edge in *. destructH.
    split_conj;eauto.
    + eapply loop_contains_trans;eauto. eapply head_exits_loop_equivalence;eauto.
    + rewrite head_exits_loop_equivalence;eauto.
Qed.

Instance head_exits_CFG `(redCFG) qh
  : redCFG (edge ∪ (head_exits_edge qh)) root (a_edge ∪ (head_exits_edge qh)).
econstructor;intros.
{ (* loop_head_dom *)
  unfold Dom. intros π Hpath.
  rewrite head_exits_back_edge in H0.
  eapply loop_contains_ledge in H0.
  eapply head_exits_in_path_head_incl in Hpath;eauto.
  destructH.
  eapply dom_loop in Hpath0 as Hpath';eauto.
}
{ (* a_edge_incl *)
  eapply union_subgraph.
  - exact a_edge_incl.
  - firstorder.
}
{ (* a_edge_acyclic *)
  unfold acyclic. intros p q π Hedge Hπ. eapply head_exits_same_connected in Hπ. destructH.
  unfold union_edge in Hedge; conv_bool. destruct Hedge as [Hedge|Hedge].
  - eapply a_edge_acyclic; eauto.
  - eapply head_exits_no_self_loop in Hedge as Hnself.
    eapply head_exits_path in Hedge. destructH. eapply path_path_acyclic;eauto.
}
{ (* reachability *)
  specialize a_reachability as H0. eapply subgraph_path in H0;eauto.
  unfold sub_graph,union_edge. firstorder. 
}
{ (* single_exit *)
  fold_lp_cont'.
  assert (loop_contains h p /\ loop_contains h' p) as [Hloop Hloop'].
  {
    unfold exit_edge' in *. do 2 destructH.
    split; eapply head_exits_loop_equivalence; eauto.
  }
  eapply loop_contains_either in Hloop;eauto.
  destruct Hloop.
  - eapply head_exits_exit_edge in H0.
    eapply head_exits_exit_edge in H1.
    do 2 destructH.
    eapply single_exit;eauto.
    unfold exit_edge in *.
    do 2 destructH.
    split;auto.
    eapply loop_contains_trans;eauto.
  - eapply head_exits_exit_edge in H0.
    eapply head_exits_exit_edge in H1.
    do 2 destructH.
    eapply single_exit;cycle 1; eauto.
    unfold exit_edge in *.
    do 2 destructH.
    split;auto.
    eapply loop_contains_trans;eauto.
}
{ (* no_head_exit *)
  fold_lp_cont'.
  intro N. destructH.
  eapply head_exits_exit_edge in H0. destructH.
  eapply no_exit_head;eauto.
  unfold loop_head.
  exists p0.
  eapply head_exits_back_edge;eauto.
}
{ (* exit_pred_loop *)
  fold_lp_cont'.
  eapply head_exits_exit_edge in H0. destructH.
  unfold_edge_op' H1.
  destruct H1.
  - copy H1 Hedge. eapply exit_edge_pred_exiting in H1;eauto.
    apply (exit_pred_loop (q:=q)) in H1;eauto.
    rewrite <-head_exits_loop_equivalence;eauto.
  - eapply head_exits_edge_spec in H1.
    destructH.
    copy H0 Hexit.
    unfold exit_edge in H0.
    destructH.
    eapply exit_edge_pred_exiting in H1;eauto.
    eapply single_exit in Hexit;eauto. subst.
    rewrite <-head_exits_loop_equivalence. 
    eauto using loop_contains_self, loop_contains_loop_head.
}
{
  intro Heq.
  eapply no_self_loops;eauto. subst. unfold_edge_op' H0. destruct H0;[auto|].
  eapply head_exits_edge_spec in H0. destructH.
  unfold exit_edge in H0. destructH.
  exfalso. contradict H0. eauto using loop_contains_loop_head,loop_contains_self.
}
{
  intro N. eapply root_no_pred.
  unfold_edge_op' N. destruct N.
  - eauto.
  - eapply head_exits_edge_spec in H0. destructH. unfold exit_edge in H0.
    exfalso.
    destructH.
    eapply root_no_pred;eauto.
} 
Qed.

(* We need LOCAL head exits and also a local headexits property, bc
 * otherwise every loop head becomes a loop_split of itself and any exit in the imploded graph *)
Definition head_exits_property `(C : redCFG) qh := forall h p q, exit_edge h p q -> ~ loop_contains h qh
                                                            -> edge h q = true.

Arguments exit_edge {_ _ _ _} (_).

Lemma head_exits_property_satisfied `(C : redCFG) qh : head_exits_property (head_exits_CFG C qh) qh.
Proof.
  unfold head_exits_property. 
  intros h p q Hexit Hloop. unfold union_edge. conv_bool.
  eapply head_exits_exit_edge in Hexit.
  unfold loop_contains in Hloop. unfold back_edge,back_edge_b in Hloop. fold_lp_cont'.
  rewrite <-head_exits_loop_equivalence in Hloop.
  right.
  rewrite head_exits_edge_spec_iff.
  split;eauto. 
Qed.

Arguments exit_edge {_ _ _ _ _}.

(** implode CFG **)
(* assuming no exit-to-heads *)

Lemma deq_loop_root `{C : redCFG} p
  : deq_loop p root.
Proof.
  unfold deq_loop.
  intros.
  exfalso.
  eapply root_loop_root in H as H'. subst.
  unfold loop_contains in H. destructH.
  eapply back_edge_incl in H0. eapply root_no_pred;eauto.
Qed.

Lemma implode_nodes_root_inv `{C : redCFG} r
  : implode_nodes r root.
Proof.
  unfold implode_nodes. cbn.
  left.
  eapply deq_loop_root.
Qed.

Lemma prefix_ex_cons (* unused *)(A : Type) (l l' : list A) (a : A)
  : Prefix l l' -> exists a', Prefix (a' :: l) (a :: l').
Proof.
  intros Hpre. revert a. induction Hpre; intros b.
  - exists b. econstructor.
  - specialize (IHHpre a). destructH. eexists. econstructor. eauto.
Qed.

Lemma head_exits_property_a_edge (* unused *)`{C : redCFG} qh 
  : head_exits_property C qh -> forall h p q : Lab, exit_edge h p q -> ~ loop_contains h qh -> a_edge h q = true.
Proof.
  intros.
  eapply H in H0 as H2.
  - decide (a_edge h q = true);[auto|exfalso].
    eapply no_exit_head;eauto. unfold loop_head.
    exists h. unfold back_edge,back_edge_b. unfold_edge_op. split;auto.
    eapply negb_true_iff,not_true_is_false. auto.
Qed.      

Definition purify_implode `{redCFG} h :=
  purify (implode_nodes_root_inv h) (D:=decide_pred _).

Lemma exit_edge_dom (* unused *) `{redCFG} h qe e
      (Hexit : exit_edge h qe e)
  : Dom edge root h e.
Proof.
Admitted.

Lemma root_no_acyclic_pred `{redCFG} p
  : a_edge p root <> true.
Proof.
  specialize (a_reachability p) as [π Hπ].
  intro. eapply a_edge_acyclic;eauto.
Qed.
      
Lemma exit_edge_acyclic `{redCFG} h qe e
      (Hexit : exit_edge h qe e)
  : a_edge qe e = true.
Proof.
  copy Hexit Hexit'.
  unfold exit_edge in Hexit.
  destructH.
  destruct (a_edge qe e) eqn:E;[auto|exfalso].
  eapply no_exit_head;eauto.
  eexists; unfold back_edge,back_edge_b; unfold_edge_op.
  split;eauto. eapply negb_true_iff. auto.
Qed.
  
Lemma exit_edge_unique_diff_head `{redCFG} h qe e
      (Hexit : exit_edge h qe e)
      h'
      (Hloop : loop_contains h' h)
      (Hnloop : ~ loop_contains h' e)
  : h' = h.
Proof.
  specialize (a_reachability e) as [π Hπ].
  inversion Hπ;subst e a.
  - exfalso. subst π.
    eapply exit_edge_acyclic in Hexit. exfalso. eapply root_no_acyclic_pred;eauto.
  - eapply a_edge_incl in H1. eapply exit_pred_loop in H1 as H2;eauto.
    eapply single_exit with (p:=b) (q:=c).
    + split;[|split];eauto.
      eapply loop_contains_trans;eauto.
    + split;[|split];eauto.
      contradict Hnloop. eapply loop_contains_trans;eauto.
Qed.

Definition impl_list `{redCFG} (h : Lab) :=
  filter (DecPred (fun q : Lab => (loop_contains h q \/ exited h q)
                        /\ (deq_loop h q
                            \/ exists e, exited q e
                                   /\ deq_loop h e
                           )
                  )
         ).

Definition back_edge'  (L : Type) (edge a_edge : L -> L-> bool) (p q : L)
  := (edge ∖ a_edge) p q = true.

Definition loop_head' (* unused *)(L : Type) (edge a_edge : L -> L-> bool) (h : L)
  := exists p, (edge ∖ a_edge) p h = true.

Lemma implode_nodes_back_edge (* unused *)`{redCFG} h p q
      (Hhead : back_edge' (restrict_edge' edge (implode_nodes h)) (restrict_edge' a_edge (implode_nodes h)) p q)
  : p ↪ q.
Proof.
  unfold back_edge' in *.
  unfold_edge_op' Hhead. destructH.
  decide (implode_nodes h p);[|contradiction].
  decide (implode_nodes h q);[|contradiction].
  destruct Hhead1 as [Hhead1|[Hhead1|Hhead1]];cbn in *.
  2,3:congruence.
  unfold back_edge,back_edge_b. unfold_edge_op. split;auto.
Qed.

Lemma loop_contains'_basic `{redCFG} h p
  : loop_contains' edge a_edge h p = loop_contains h p.
Proof.
  reflexivity.
Qed.

Lemma exit_not_deq `{redCFG} h p q
      (Hexit : exit_edge h p q)
      (Hdeq : deq_loop q h)
  : False.
Proof.
  unfold exit_edge in Hexit. destructH.
  apply Hexit2.
  eapply Hdeq.
  eapply loop_contains_self. eapply loop_contains_loop_head;eauto.
Qed.

Lemma deq_loop_exited' : forall (Lab : finType) (edge : Lab -> Lab -> bool) (root : Lab) (a_edge : Lab -> Lab -> bool)
                           (C : redCFG edge root a_edge) (h qe e : Lab), exit_edge h qe e -> deq_loop h e.
Proof.
  intros.
  eapply deq_loop_exited in H as H'.
  eapply deq_loop_exiting in H as H''.
  eapply deq_loop_trans;eauto.
Qed.

Lemma exit_edge_in_loop (* unused *)`{redCFG} (h1 h2 p1 p2 e1 e2 : Lab)
      (Hexit : exit_edge h1 p1 e1)
      (Hexit' : exit_edge h2 p2 e2)
      (Hloop : loop_contains h1 h2)
      (Hneq : h1 <> h2)
  : loop_contains h1 e2.
  decide (loop_contains h1 e2);[auto|].
  copy Hexit' Hexit''.
  unfold exit_edge in Hexit'. destructH.
  assert (exit_edge h1 p2 e2).
  {
    unfold exit_edge. split_conj;cycle 1.
    + eauto.
    + eauto.
    + eauto using loop_contains_trans.
  }
  eapply single_exit in Hexit'';eauto. contradiction.
Qed.

(*
Lemma impl_list_imploded_path:
  forall (Lab : finType) (edge : Lab -> Lab -> bool) (root : Lab) (a_edge f : Lab -> Lab -> bool)
    (H : redCFG edge root a_edge),
    (forall h p q : Lab, exit_edge h p q -> f h q = true) ->
    forall h p : Lab,
      implode_nodes p ->
      forall π : ne_list Lab,
        Path f root p π ->
        innermost_loop h p ->
        exists π0, Path (restrict_edge' f implode_nodes) root p π0 /\ impl_list h π = π0.
Proof.
  intros Lab edge root a_edge f H Hhe h p H0 π Hπ Hinner.
  (* this lemma should replace the proof (a) in implode_CFG and should suffice to prove case (b)
   * to this end modifications are necessary that are dependent on whether loop_CFG is dropped entirely *)
  
Admitted.  
 *)

Lemma eq_loop_exiting (* unused *)`{redCFG} h p q
      (Hexit : exit_edge h p q)
  : eq_loop h p.
Proof.
  split.
  - eapply deq_loop_exiting;eauto.
  - unfold exit_edge in Hexit.
    destruct Hexit as [Hexit _].
    eapply loop_contains_deq_loop;eauto.
Qed.      

Lemma eq_loop1 (* unused *)`{redCFG} p p' q
  : eq_loop p p' -> deq_loop p q -> deq_loop p' q.
Proof.
  intros. destruct H0.
  eapply deq_loop_trans;eauto.
Qed.

Lemma eq_loop2 `{redCFG} p q q'
  : eq_loop q q' -> deq_loop p q -> deq_loop p q'.
Proof.
  intros. destruct H0.
  eapply deq_loop_trans;eauto.
Qed.

Instance implode_CFG `(H : redCFG) h7 (Hhe : head_exits_property H h7)
  : @redCFG (finType_sub_decPred (implode_nodes h7))
            (restrict_edge edge (implode_nodes h7))
            (↓ purify_implode h7)
            (restrict_edge a_edge (implode_nodes h7)).
Proof.
  eapply sub_CFG;intros.
  - specialize (a_reachability p) as [π Hπ].
    revert dependent p. revert dependent π.
    specialize (well_founded_ind (R:=(@StrictPrefix' Lab)) (@StrictPrefix_well_founded Lab)
                                 (fun π : ne_list Lab => forall (p : Lab),
                                      implode_nodes h7 p ->
                                      Path a_edge root p π
                                      -> exists π0, Path (restrict_edge' a_edge (implode_nodes h7)) root p π0))
      as WFind.
    eapply WFind.
    intros ? IHwf ? ? ?. clear WFind.
    destruct H1.
    + eexists; econstructor.
    + unfold implode_nodes in H0. cbn in H0.
      decide (implode_nodes h7 b).
      * specialize (IHwf π). exploit IHwf;[econstructor;econstructor|].
        destructH.
        eexists; econstructor;eauto.
        unfold_edge_op. split_conj;auto.
      * unfold implode_nodes in n. cbn in n. simpl_dec' n.
        destructH.
        simpl_dec' n1. simpl_dec' n1.  
        enough (exists h, exit_edge h b c).
        {
          destructH.
          enough (h ∈ π).
          {
            eapply path_to_elem in H4;eauto. destructH.
            specialize (IHwf ϕ).
            assert (implode_nodes h7 h) as Himpl.
            {
              destruct H0.
              * right. exists c. split;[exists b|];eauto.
              * exfalso.
                destructH. eapply no_exit_head;eauto.
                unfold exited,exit_edge in H4; destructH. eauto using loop_contains_loop_head.
            }
            exploit IHwf.
            - eapply prefix_ex_cons in H6. destructH. econstructor. cbn. eauto.
            - destructH. 
              exists (c :<: π0). econstructor;eauto. unfold_edge_op. split_conj;eauto.
              eapply head_exits_property_a_edge;eauto.
              contradict n0.
              eapply loop_contains_deq_loop in n0.
              eapply eq_loop_exiting in H3.
              eapply eq_loop2;eauto.
          }
          eapply dom_loop;[unfold exit_edge in H3;destructH;eauto|].
          eapply subgraph_path';eauto.
        }
        simpl_dec' n0. simpl_dec' n0.
        destructH.
        exists x. unfold exit_edge;split_conj;eauto using a_edge_incl.
        destruct H0.
        -- contradict n3. eauto.
        -- destructH.
           destruct H3 as [q Hexit]. 
           decide (x = c).
           ++ exfalso. subst. eapply loop_reachs_member in n2. destructH.
              eapply a_edge_acyclic;eauto.
           ++ 
              intro N.
              eapply exit_edge_unique_diff_head in Hexit;auto;cycle 1.
              ** exact N.
              ** contradict n3. eapply H4;eauto.
              ** contradiction.
  - rewrite loop_contains'_basic in H1.
    unfold loop_contains in H1. rename H1 into Hloop.
    destructH.
    exists p0.
    revert dependent p.
    induction π;intros;inversion Hloop2;subst.
    + exists (ne_single a). split_conj;eauto.
      * unfold_edge_op. split_conj;eauto using back_edge_incl.
        -- admit. (*left;eapply deq_loop_refl.*)
        -- left. unfold back_edge,back_edge_b in Hloop0. unfold_edge_op' Hloop0. firstorder.
      * econstructor.
    + admit. (* FIXME: give intuition *)
Admitted.

Lemma implode_CFG_elem `{C : redCFG} (p h : Lab) (Himpl : implode_nodes h p)
  : finType_sub_decPred (implode_nodes h).
Proof.
  econstructor. unfold pure. instantiate (1:=p).
  decide (implode_nodes h p);eauto.
Defined.

               
Goal forall `(C : redCFG) (h:Lab), (match decision (@loop_head _ _ _ _ C h) with
             | left H => (@finType_sub_decPred Lab (@loop_nodes Lab edge root a_edge C h))
             | right _ => Lab
                               end).
intros. decide (loop_head h);eauto. Show Proof.
Abort.

Definition if_transfm (* unused *): forall (X Y : Type) (A B : Prop) (b : {A} + {B}), (if b then X -> X -> bool else Y -> Y -> bool)
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
             | left H => (↓ purify_head H)

                 (*@finType_sub_elem Lab h (@loop_nodes Lab edge root a_edge C h)
                                           (or_introl (@loop_contains_self Lab edge root a_edge C h H)))*)
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
  destruct d; eauto. 
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
             | Some (exist _ h H) => (↓ purify_head H) 
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

Lemma opt_loop_CFG_elem (* unused *)`{C : redCFG} (p : Lab)
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

Definition local_impl_CFG `(C : redCFG) (h : Lab)
  := implode_CFG (head_exits_CFG C h) h (head_exits_property_satisfied (C:=C) (qh:=h)).

Arguments redCFG : clear implicits.
Arguments implode_nodes {_ _ _ _} _.
Definition local_impl_CFG_type `(C : redCFG) (h : Lab)
  := (finType_sub_decPred (implode_nodes (head_exits_CFG C h) h)).
Arguments redCFG : default implicits.
Arguments implode_nodes : default implicits.

Definition impl_of_original (* unused *)`(C : redCFG) (h : Lab)
  : Lab -> option (local_impl_CFG_type C h).
Proof.
  intro p.
  decide (implode_nodes (head_exits_CFG C h) h p).
  - apply Some. econstructor. eapply purify;eauto.
  - exact None.
Defined.


Arguments loop_contains {_ _ _ _} _.

Lemma head_exits_loop_contains_iff `(C : redCFG) (h p q : Lab)
  : loop_contains C h q <-> loop_contains (head_exits_CFG C p) h q.
Proof.
  setoid_rewrite <-loop_contains'_basic at 2.
  eapply head_exits_loop_equivalence.
Qed.          

Lemma head_exits_deq_loop_inv1 `(C : redCFG) (h p q : Lab)
  : deq_loop (C:=C) p q -> deq_loop (C:=head_exits_CFG C h) p q.
Proof.
  intros.
  unfold deq_loop in *.
  setoid_rewrite <-head_exits_loop_contains_iff.
  eauto.
Qed.

Lemma head_exits_deq_loop_inv2 `(C : redCFG) (h p q : Lab)
  : deq_loop (C:=head_exits_CFG C h) p q -> deq_loop (C:=C) p q.
Proof.
  unfold deq_loop.
  setoid_rewrite <-head_exits_loop_contains_iff.
  eauto.
Qed.

Lemma head_exits_exited_inv1 `(C : redCFG) (qh h p : Lab)
  : exited (C:=C) h p -> exited (C:=head_exits_CFG C qh) h p.
Proof.
  unfold exited, exit_edge.
  setoid_rewrite <-head_exits_loop_contains_iff.
  intros. destructH.
  exists p0. split_conj;eauto.
  eapply union_subgraph1;auto.
Qed.

Lemma head_exits_exited_inv2 `(C : redCFG) (qh h p : Lab)
  : exited (C:=head_exits_CFG C qh) h p -> exited (C:=C) h p.
Proof.
  unfold exited, exit_edge.
  setoid_rewrite <-head_exits_loop_contains_iff.
  intros. destructH.
  unfold_edge_op' H3. destruct H3.
  - exists p0. split_conj;eauto.
  - eapply head_exits_edge_spec in H. destructH. exists p1.
    replace p0 with h in *.
    + unfold exit_edge in H. destructH. split_conj; eauto.
    + eapply exit_edge_unique_diff_head;eauto.
Qed.

Arguments loop_contains {_ _ _ _ _}.

Lemma head_exits_implode_nodes_inv1 `(C : redCFG) (h p : Lab)
  : implode_nodes C h p -> implode_nodes (head_exits_CFG C h) h p.
Proof.
  intro Himpl.
  cbn in Himpl. destruct Himpl.
  - left. eapply head_exits_deq_loop_inv1. eauto.
  - right. destructH. exists e. split; eauto using head_exits_exited_inv1, head_exits_deq_loop_inv1.
Qed.      

Definition impl_of_original' `(C : redCFG) (h p : Lab) (H : implode_nodes C h p)
  : local_impl_CFG_type C h.
Proof.
  econstructor. eapply purify;eauto.
  eapply head_exits_implode_nodes_inv1;eauto.
Defined.

Arguments local_impl_CFG {_ _ _ _} _.

Lemma Lab_dec' `{redCFG} : forall (l l' : Lab), { l = l' } + { l <> l'}.
Proof.
  apply Lab_dec.
Qed.