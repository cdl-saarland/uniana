Require Export CFGloop CFGTac.

Section Restr.
  Context `{C : redCFG}.
  
  Notation "p '-a>b' q" := (a_edge p q) (at level 55).
  Notation "p '-a>' q" := (p -a>b q = true) (at level 55).
  Notation "p '-->b' q" := (edge p q) (at level 55).
  Notation "p '-->' q" := (p -->b q = true) (at level 55, right associativity).
  
  Definition finType_sub_elem (h : Lab) (p : decPred Lab) (H : p h)
    := (exist (fun x : Lab => pure p x) h (purify H)).

  
  Lemma restrict_edge_intersection (A : finType) (f : A -> A -> bool) (p : decPred A) x y
    : restrict_edge f (p:=p) x y = restrict_edge' f p (`x) (`y).
  Proof.
    clear Lab edge root a_edge C.
    destruct x,y. 
    unfold restrict_edge',restrict_edge,intersection_edge. cbn.
    symmetry. destruct (f x x0);cbn;conv_bool;[split;eapply (pure_equiv (D:=decide_pred p));auto|reflexivity].
  Qed.
End Restr.

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

Definition list_to_ne (A : Type) (l : list A) : option (ne_list A)
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
Proof.
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
