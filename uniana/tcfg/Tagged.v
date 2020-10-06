Require Export Precedes CFGancestor TcfgqMonotone TcfgDet TcfgDom.

Require Import Lia MaxPreSuffix.

Section tagged.

  Context `{C : redCFG}.

  Notation "pi -t> qj" := (tcfg_edge pi qj) (at level 50).

  Hint Resolve tcfg_edge_spec : tcfg.


(** * Lemmas about TCFGs **)

(*
Lemma exit_edge_tcfg_edge (h p q : Lab) (j : Tag)
      (Hexit : exit_edge h q p)
  : (q,j) -t> (p,tl j).
Proof.
  cbn. copy Hexit Hexit'.
  unfold exit_edge in Hexit. destructH.
  split;auto.
  unfold eff_tag. decide (edge__P q p);[|contradiction].
  f_equal.
  unfold eff_tag'.
  destruct (edge_Edge e);auto.
  1-3: exfalso.
  - eapply Hexit2. unfold basic_edge in b. destructH. rewrite <-b0. auto.
  - eapply back_edge_eq_loop in b. destruct b. eapply Hexit2. eauto.
  - eapply deq_loop_entry in e0. eapply Hexit2. eauto.
  -
Qed.
*)

(* possibly unused
Lemma exit_succ_exiting (p q h e : Lab) (k i j : Tag) r
      (Hpath : TPath (p,k) (q,j) (r :r: (p,k)))
      (Hexit : exited h e)
      (Hel : (e,i) ∈ r)
  : exists qe n, exit_edge h qe e /\ (e,i) ≻ (qe,n :: i) | r :r: (p,k).
Proof.
*)

  Lemma prec_tpath_pre_tpath p i q j l
        (Hneq : p <> q)
        (Htr : TPath (root,start_tag) (p,i) ((p, i) :: l))
        (Hprec : Precedes fst l (q, j))
    : exists l', TPath (root,start_tag) (q,j) ((q,j) :: l') /\ Prefix ((q,j) :: l') ((p,i) :: l).
  Proof.
    eapply path_to_elem with (r:= (q,j)) in Htr.
    - destructH. exists (tl ϕ).
      assert (ϕ = (q,j) :: tl ϕ) as ϕeq.
      { inversion Htr0;subst a;cbn;eauto. }
      split;eauto.
      + rewrite ϕeq in Htr0;eauto.
      + rewrite ϕeq in Htr1;eauto.
    - eapply precedes_in. econstructor;eauto;cbn;eauto.
  Qed.

  Lemma prec_tpath_tpath p i q j l
        (Htr : TPath (root,start_tag) (p,i) ((p, i) :: l))
        (Hprec : Precedes fst ((p,i) :: l) (q, j))
    : exists l', TPath (root,start_tag) (q,j) ((q,j) :: l').
  Proof.
    inversion Hprec;subst.
    - firstorder.
    - eapply prec_tpath_pre_tpath in Htr;eauto. destructH. eauto.
  Qed.

  Lemma precedes_fst_same_tag {A B : Type} `{EqDec B} (p : A) (i j : B) l
        (Hprec1 : Precedes fst l (p,i))
        (Hprec2 : Precedes fst l (p,j))
    : i = j.
  Proof.
    clear edge root a_edge C.
    dependent induction Hprec1.
    - inversion Hprec2;subst;[reflexivity|]. cbn in H2; contradiction.
    - inversion Hprec2;subst.
      + cbn in H0;contradiction.
      + eapply IHHprec1;eauto.
  Qed.

  Lemma tpath_tag_len_eq p j1 j2 l1 l2
        (Hpath1 : TPath (root, start_tag) (p, j1) l1)
        (Hpath2 : TPath (root, start_tag) (p, j2) l2)
    : length j1 = length j2.
  Proof.
    eapply tag_depth' in Hpath1.
    eapply tag_depth' in Hpath2.
    rewrite Hpath1,Hpath2. reflexivity.
  Qed.

  Lemma tpath_tag_len_eq_elem p q i1 i2 j1 j2 l1 l2
        (Hpath1 : TPath (root, start_tag) (p, i1) l1)
        (Hpath2 : TPath (root, start_tag) (p, i2) l2)
        (Hin1 : (q,j1) ∈ l1)
        (Hin2 : (q,j2) ∈ l2)
    : length j1 = length j2.
  Proof.
    eapply path_to_elem in Hin1;eauto.
    eapply path_to_elem in Hin2;eauto.
    do 2 destructH.
    eapply tpath_tag_len_eq in Hin0;eauto.
  Qed.

  Lemma dom_tpath_prec p q i l
        (Hdom : Dom edge__P root q p)
        (Hpath : TPath (root,start_tag) (p,i) l)
    : exists j, Precedes fst l (q,j).
  Proof. (* used in uniana *)
    (* FIXME *)
    eapply TPath_CPath in Hpath as Hpath'.
    cbn in Hpath'.
    eapply Hdom in Hpath'.
    clear Hdom.
    revert p i Hpath.
    induction l;intros.
    - contradiction.
    - inv_path Hpath.
      + cbn in Hpath'. destruct Hpath';[subst|contradiction]. eexists. econstructor.
      + cbn in Hpath'. decide (p = q).
        * eexists. subst. econstructor.
        * destruct Hpath';[contradiction|].
          exploit' IHl. destruct x. specialize (IHl e t). exploit IHl. destructH.
          eexists. econstructor;eauto.
  Qed.

  Lemma tag_prefix_head h p i j l
        (Hloop : loop_contains h p)
        (Hpath : TPath (root, start_tag) (p,i) l)
        (Hprec : Precedes fst l (h,j))
    : Prefix j i.
  Proof. (* used in uniana *)
    assert (| i | = depth p) as Hpdep.
    { eapply tag_depth_unroot in Hpath;eauto. cbn. symmetry. eapply depth_root. }
    eapply precedes_in in Hprec as Hin.
    eapply path_from_elem in Hin as Hϕ;eauto. destructH.
    assert (| j | = depth h) as Hhdep.
    { eapply tag_depth_unroot2 in Hϕ0;eauto. }
    eapply loop_contains_deq_loop in Hloop as Hdeq.
    eapply deq_loop_depth in Hdeq as Hdepth.
    copy Hdepth Hlenleq.
    rewrite <-Hhdep, <-Hpdep in Hlenleq.
    eapply tagle_monotone with (n:=|j|) in Hϕ0 as Hmon.
    - rewrite take_r_self in Hmon. destruct Hmon.
      + exfalso.
        eapply path_to_elem in Hin as Hπ;eauto. destructH.
        eapply path_app' in Hϕ0 as Hϕπ;eauto.
        eapply loop_tag_dom with (h0:=h) (j0:=take_r (|j|) i) in Hϕπ;eauto.
        2: { rewrite Hhdep. unfold sub_tag. split_conj;eauto. }
        2: { rewrite take_r_length_le;eauto. }
        eapply in_app_or in Hϕπ. destruct Hϕπ.
        * eapply tpath_NoDup in Hpath as Hnd.
          destr_r' ϕ. 1: subst;inv Hϕ0. subst. path_simpl' Hϕ0.
          eapply In_rcons in H0. destruct H0.
          1: { inv H0. rewrite H2 in H. eapply Taglt_irrefl;eauto. }
          clear - H0 Hprec Hpath Hϕ0 Hϕ1 Hnd.
          eapply postfix_eq in Hϕ1. destructH. subst l.
          eapply precedes_app_drop in Hprec. 2: { cbn. rewrite map_rcons. eapply In_rcons. cbn;eauto. }
          eapply NoDup_app_drop in Hnd.
          eapply precedes_rcons in Hprec. 2:eauto. 2:eauto. cbn in Hprec. eauto.
        * inv_path Hπ0. 1: cbn in H0;contradiction.
          eapply in_tl_in in H0.
          eapply path_from_elem in H0;eauto. destructH.
          eapply tagle_monotone with (n:=|j|) in H3.
          -- rewrite take_r_self in H3. rewrite take_r_take_r_leq in H3;eauto.
             eapply Taglt_irrefl. eapply taglt_tagle_trans;eauto.
          -- rewrite take_r_length_le;eauto.
          -- reflexivity.
          -- reflexivity.
          -- eauto.
      + eapply prefix_take_r;eauto.
    - eauto.
    - reflexivity.
    - eapply Hdeq.
    - eauto.
  Qed.

  Lemma root_tag_nil p i j l
        (HPath : TPath (root,start_tag) (p,i) l)
        (Hin : (root,j) ∈ l)
    : j = nil.
  Proof.
    revert dependent p. revert i.
    induction l;intros.
    - inversion HPath. (*subst a0 p i a. cbn in Hin. destruct Hin;[|contradiction].
      inversion H;subst. eauto.*)
    - destruct a. cbn in Hin.
      destruct Hin.
      + inversion H. subst. inversion HPath.
        * reflexivity.
        * exfalso.
          subst a c p i π. destruct b.
          eapply root_no_pred. eapply tcfg_edge_spec; eauto.
      + inversion HPath.
        * subst l. contradiction.
        * destruct b. eapply IHl;eauto.
  Qed.

  Lemma tag_prefix_ancestor a p q i j l
        (Hanc : ancestor a p q)
        (Hpath : TPath (root, start_tag) (p,i) l)
        (Hprec : Precedes fst l (a,j))
    : Prefix j i.
  Proof.
    unfold ancestor in Hanc.
    destruct Hanc as [[Hanc _]|Hanc]; [eapply tag_prefix_head|subst a];eauto.
    replace j with (@nil nat);[eapply prefix_nil|].
    symmetry; eapply root_tag_nil;eauto using precedes_in.
  Qed.

  Hint Unfold Coord.

  Lemma tag_prefix_ancestor_elem a p q r i j k l
        (Hanc : ancestor a p q)
        (Hpath : TPath (root,start_tag) (r,k) ((r,k) :: l))
        (Hprec : Precedes fst ((r,k) :: l) (a,j))
        (Hib : (p,i) ≻* (a,j) | (r,k) :: l)
    : Prefix j i.
  Proof.
    eapply splinter_in in Hib as Hin.
    eapply path_to_elem in Hin;eauto. destructH.
    decide (i = j).
    { subst. reflexivity. }
    eapply tag_prefix_ancestor;eauto.
    eapply path_contains_front in Hin0 as Hfront.
    eapply tpath_NoDup in Hin0.
    eapply tpath_NoDup in Hpath.
    clear - Hprec Hib Hin1 Hpath Hin0 n Hfront. set (l' := (r,k) :: l) in *.
    eapply prefix_eq in Hin1. destructH.
    revert dependent l'. revert dependent ϕ. induction l2';intros.
    - cbn in Hin1. rewrite Hin1 in Hprec. eauto.
    - destruct l'. 1: inversion Hprec.
      inversion Hin1.
      eapply IHl2'. 6:eauto. 1,2:eauto.
      + inversion Hpath. subst. eauto.
      + inversion Hprec;subst.
        * exfalso.
          inversion Hib; subst. 1: contradiction.
          inversion Hpath. subst.
          eapply splinter_cons in H1. eapply splinter_in in H1. contradiction.
        * eauto.
      + subst. clear Hin1. inversion Hib;subst.
        * exfalso.
          inversion Hpath;subst.
          eapply H2.
          eapply in_or_app. right;auto.
        * eauto.
  Qed.

  Lemma first_occ_tag n2 j j1 j2 p t
        (Htag : j = j1 ++ (n2 :: j2))
        (Hpath : TPath (root,start_tag) (p,j) t)
    : exists h, loop_contains h p /\ Precedes fst t (h,n2 :: j2).
  Proof. (* used below *)
    eapply tag_depth' in Hpath as Hdep.
    assert (| n2 :: j2 | <= depth p) as Hleq.
    { rewrite Htag in Hdep. rewrite app_length in Hdep. cbn in Hdep. cbn. lia. }
    eapply ex_depth_head in Hleq;eauto. 2: cbn;lia.
    destructH.
    exists h. split;auto. symmetry in Hleq1.
    eapply loop_tag_dom_prec in Hleq1;eauto.
    eapply prefix_eq. eexists;eauto.
  Qed.

  Lemma first_occ_tag_elem i j j1 n2 j2 p q t
        (Htag : j = j1 ++ (n2 :: j2))
        (Hpath : TPath (root,start_tag) (p,i) t)
        (Hin : (q,j) ∈ t)
    : exists h, loop_contains h q /\ (h,n2 :: j2) ∈ t /\ (q,j) ≻* (h, n2 :: j2) | t.
  Proof. (* used in uniana *)
    eapply path_to_elem in Hpath as Hϕ;eauto. destructH.
    eapply first_occ_tag in Hϕ0 as Hocc;eauto. destructH.
    exists h. split_conj;eauto.
    - eapply precedes_in in Hocc1. eapply prefix_incl;eauto.
    - eapply precedes_in in Hocc1.
      eapply splinter_prefix;eauto.
      destruct ϕ;[contradiction|]. path_simpl' Hϕ0.
      econstructor. eapply splinter_single;eauto.
  Qed.
  (*
  (* possibly not used *)
  Lemma prec_prec_eq l (q : Lab) (j j' : Tag)
        (Hprec1 : Precedes fst l (q,j))
        (Hprec2 : Precedes fst l (q,j'))
    : j = j'.
  Proof.
  Admitted.

  (* possibly not used *)
  Lemma prefix_prec_prec_eq l l' (p q : Lab) (i j j' : Tag)
        (Hpre : Prefix ((p,i) :: l') l)
        (Hprec1 : Precedes fst l (q,j))
        (Hprec2 : Precedes fst ((p,i) :: l') (q,j'))
        (Hnd : NoDup l)
        (Hib : (p,i) ≻* (q,j) | l)
    : j' = j.
  Proof.
  Admitted.

  (* possibly not used *)
  Lemma ancestor_in_before_dominating a p q (i j k : Tag) l
        (Hdom : Dom edge__P root q p)
        (Hanc : ancestor a q p)
        (Hprec__a: Precedes fst ((p,i) :: l) (a,k))
        (Hprec__q: Precedes fst ((p,i) :: l) (q,j))
    : (q,j) ≻* (a,k) | (p,i) :: l.
  Proof.
  Admitted.
*)
  Lemma ancestor_level_connector p q a i j k t
        (Hpath : TPath (root,start_tag) (p,i) t)
        (Hin : (q,j) ∈ t)
        (Hanc  : near_ancestor a p q)
        (Hprec : Precedes fst t (a,k))
        (Hib : (q,j) ≻* (a,k) | t)
    : exists a', Precedes fst t (a',k) /\ (p,i) ≻* (a',k) ≻* (q,j) | t.
  Proof. (* used in uniana *)
    (* a' = pre-header of ocnc_loop _ p q *)
    (* FIXME *)
  Admitted.

  Lemma find_loop_exit h a p i j k n l
        (Hpath : TPath (root,start_tag) (p,i) l)
        (Hpre : Prefix k j)
        (Hib : (a,k) ≻* (h, n :: j) | l)
    : exists qe e, (a,k) ≻* (e,j) ≻* (qe,n :: j) ≻* (h, n :: j) | l /\ (e,j) ≻ (qe,n :: j) | l /\ exit_edge h qe e.
  Proof. (* used in uniana *)
    (* inductively look for the exit *)
    (* FIXME *)
  Admitted.

  Lemma tpath_deq_loop_prefix p q i j t x l y m
        (Hdeq : deq_loop p q)
        (Hpath : TPath (x,l) (y,m) t)
        (Hpre : Prefix j i)
    : (q,j) ≻* (p,i) | t.
  Proof. (* used in uniana *)
    (* easy using monotonicity *)
     (* FIXME *)
  Admitted.

  Hint Resolve precedes_in.

  Lemma dom_dom_in_between  (p q r : Lab) (i j k : Tag) l
        (Hdom1 : Dom edge__P root r q)
        (Hdom2 : Dom edge__P root q p)
        (Hprec : Precedes fst ((p,i) :: l) (q,j))
        (Hin : (r,k) ∈ ((p,i) :: l))
        (Hpath : TPath (root,start_tag) (p,i) ((p,i) :: l))
    : (q,j) ≻* (r,k) | (p,i) :: l.
  Proof. (* used in uniana *)
    (* dom_trans is the key *)
    (* FIXME *)
  Admitted.

  Lemma tpath_exit_nin h q e n j t
        (Hpath : TPath (root, start_tag) (q,n :: j) t)
        (Hloop : loop_contains h q)
        (Hexit : exited h e)
    : (e,j) ∉ t.
  Proof. (* used in uniana *) (* contradict monotoncity *)
    intro N.
    unfold exited in Hexit. destructH.
    unfold exit_edge in Hexit. destructH.
    eapply PathCons in Hexit3;eauto. cycle 1.
  Admitted. (* FIXME *)

  Lemma loop_cutting_elem q p t i j x l
        (Hpath : TPath (x,l) (p,i) ((p,i) :: t))
        (Hib : (p,i) ≻* (q,j) | (p,i) :: t)
        (Hnoh : forall h k, loop_contains h q -> ~ (p,i) ≻* (h,k) ≻* (q,j) | (p,i) :: t)
    : exists t', Path a_edge__P q p t'.
  Proof. (* used in uniana *)
    (* easy using loop_cutting *)

    (* FIXME *)
  Admitted.

  Lemma exit_cascade u p t i j k x l
        (Hdom : Dom edge__P root u p)
        (Hprec : Precedes fst ((p,i) :: t) (u,j))
        (Hpath : TPath (x,l) (p,i) ((p,i) :: t))
    : forall h, loop_contains h u -> ~ (p,i) ≻* (h,k) ≻* (u,j) | (p,i) :: t.
    (* otw. there would be a path through this q to p without visiting u *)
    (* this could even be generalized to CPaths *)
    (* TODO: lift on tpaths, on cpaths we might have duplicates, thus it doesn't work there *)
  Proof. (* used in uniana *) (* FIXME *)
  Admitted.

  (*

  Lemma loop_tag_prec (h p : Lab) (i j : Tag) t
    (Hloop : loop_contains h p)
    (Hpath : TPath (root,start_tag) (p,i) t)
    (Htagle : j ⊴ i)
    (Hdep : |j| = depth h)
    : Precedes fst t (h,j).
  Proof.
  Admitted.
*)

End tagged.
