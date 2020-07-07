Require Import Coq.Classes.EquivDec.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.Decidable.
Require Import Coq.Program.Utils.
Require Import Lists.ListSet.
Require Import List.
Require Import Nat.
Require Import Omega.
Require Import Program.Basics.

Require Import PathSplits Unchanged ListOrderTac FirstDiff.

Section uniana.

  Context `(C : redCFG).

  Notation "p --> q" := (edge p q = true) (at level 55,right associativity).

  Parameter branch: Lab -> option Var.

  Definition is_branch br x := branch br = Some x.

  Parameter val_true : Val -> bool.

  Parameter branch_spec :
    forall p : Lab, match branch p with
         | Some x => exists q q', q <> q' /\ forall s,
                        if val_true (s x)
                        then exists r, eff' (p,s) = Some (q, r)
                        else exists r', eff' (p,s) = Some (q',r')
         | None => forall q q' : Lab, edge p q = true -> p --> q' -> q = q'
               end.

  (** * Uniformity-concretizer **)

  Definition UniState := Var -> bool.

  Parameter abs_uni_eff : UniState -> UniState.

  (** ** Definition **)

  Definition uni_state_concr (uni : UniState) : State -> State -> Prop :=
    fun s => fun s' => forall x, uni x = true -> s x = s' x.

  Parameter local_uni_corr : forall uni p i q j s s' qs qs',
      uni_state_concr uni s s' ->
      eff (p, i, s) = Some (q, j, qs) ->
      eff (p, i, s') = Some (q, j, qs') ->
      uni_state_concr (abs_uni_eff uni) qs qs'.

  Definition Uni := Lab -> Var -> bool.

  Definition uni_concr (u : Uni) : Hyper :=
    fun ts => forall t t', ts t -> ts t' ->
                   forall x p i s s', In (p, i, s) (`t) ->
                                 In (p, i, s') (`t') ->
                                 u p x = true -> s x = s' x.

  Definition uni_meet (u1 u2 : Uni) : Uni
    := fun (p : Lab) (x : Var) => u1 p x || u2 p x.

  Infix "⊓" := uni_meet (at level 70).

  (** ** Meet-preserving **)

  Lemma uni_concr_meet_preserve (u1 u2 : Uni) (ts : Traces)
    : uni_concr (u1 ⊓ u2) ts <-> uni_concr u1 ts /\ uni_concr u2 ts.
  Proof.
    split;intros H.
    - unfold uni_concr in *. split;intros.
      1: eapply H;cycle 2;eauto 1.
      2: symmetry;eapply H;cycle 2;eauto 1.
      all: unfold uni_meet;conv_bool.
      1: left. 2: right. all: eauto.
    - unfold uni_concr;intros. destruct H. unfold uni_meet in H4. conv_bool. destruct H4.
      + eapply H;cycle 2;eauto.
      + eapply H5;cycle 2;eauto.
  Qed.

  Definition uni_branch (uni : Uni) :=
    (fun s : Lab
     => match (branch s) with
       | Some x => uni s x
       | None => false
       end
    ).

  (** * Uniformity-transformer **)
  (** ** Definition **)

  Definition uni_trans (uni : Uni) (unch : @Unch Lab) : Uni :=
    fun (p : Lab)
    => if decision (p = root) then uni root
      else fun (x : Var) => (join_andb (map ((uni_branch uni)) (splitsT p)))
                      (* the predecessor is only included in split set if p is an exit *)
                      &&  (join_andb (map (fun q => abs_uni_eff (uni q) x) (preds p)))
                    || join_orb (map (fun q => (negb (decision (q = p)))
                                                 && uni q x
                                                 && join_andb (map ((uni_branch uni))
                                                                   (rel_splits p q)))
                                    (unch_trans unch p x)).

  (** ** Lemmas **)

  Lemma uni_trans_root_inv :
    forall uni unch x, uni_trans uni unch root x = uni root x.
  Proof.
    intros.
    unfold uni_trans.
    decide (root = root).
    reflexivity.
    exfalso. apply n. reflexivity.
  Qed.

  Lemma uni_branch_uni_succ p br q1 q2 i k j1 j2 s1 s2 uni l1 l2
        (Hpath1 : Tr ((p,i,s1) :: l1))
        (Hpath2 : Tr ((p,i,s2) :: l2))
        (Hsucc1 : (q1,j1) ≻ (br,k) | ((p,i) :: map fst l1))
        (Hsucc2 : (q2,j2) ≻ (br,k) | ((p,i) :: map fst l2))
        (Hunibr : uni_branch uni br = true)
        (HCuni : forall (x : Var) (p : Lab) (i : Tag) (s s' : State),
            (p, i, s) ∈ l1 -> (p, i, s') ∈ l2 -> uni p x = true -> s x = s' x)
    : q1 = q2.
  Proof.
    unfold uni_branch in Hunibr. cbn in Hunibr.
    specialize (branch_spec br) as Hbr.
    destruct (branch br) eqn:E; [|congruence]. destructH.
    replace ((p,i) :: map fst l1) with (map fst ((p,i,s1) :: l1)) in Hsucc1 by (cbn;eauto).
    replace ((p,i) :: map fst l2) with (map fst ((p,i,s2) :: l2)) in Hsucc2 by (cbn;eauto).
    eapply2 tr_lift_succ Hsucc1 Hsucc2;eauto. do 2 destructH.
    specialize (HCuni v br k r0 r).
    exploit HCuni.
    1,2: eapply in_succ_in2;eauto.
    specialize (Hbr1 r0) as Hbr1'.
    specialize (Hbr1 r).
    destruct (val_true (r0 v)) eqn:Heq1, (val_true (r v)) eqn:Heq2.
    2,3: rewrite HCuni in Heq1; congruence.
    all:do 2 destructH.
    - enough (q1 = q /\ q2 = q) by (subst';eauto).
      split.
      eapply tr_succ_eff' with (s:=s1) (q'0:=q);eauto.
      eapply tr_succ_eff' with (s:=s2) (q'0:=q);eauto.
    - enough (q1 = q' /\ q2 = q') by (subst';eauto).
      split.
      eapply tr_succ_eff' with (s:=s1) (q'0:=q');eauto.
      eapply tr_succ_eff' with (s:=s2) (q'0:=q');eauto.
  Qed.

  Lemma uni_branch_uni_succ' p br q1 q2 i k j1 j2 uni l1 l2 s1 s2
        (Hpath1 : Tr ((p,i,s1) :: l1))
        (Hpath2 : Tr ((p,i,s2) :: l2))
        (Hsucc1 : (q1,j1) ≻ (br,k) | ((p,i) :: map fst l1))
        (Hsucc2 : (q2,j2) ≻ (br,k)| ((p,i) :: map fst l2))
        (Hunibr : uni_branch uni br = true)
        (HCuni : forall (x : Var) (p : Lab) (i : Tag) (s s' : State),
            (p, i, s) ∈ l1 -> (p, i, s') ∈ l2 -> uni p x = true -> s x = s' x)
    : q1 = q2 /\ j1 = j2.
  Proof.
    assert (q1 = q2) by (eapply uni_branch_uni_succ with (q1:=q1) (l1:=l1) ;eauto).
    split;[eauto|subst].
    eapply eff_tag_det'.
    2: eapply succ_in_tpath_eff_tag;[clear Hpath1;spot_path|];eauto;cbn;
      eauto using succ_in_cons_cons.
    clear Hpath2 Hsucc2.
    eapply succ_in_tpath_eff_tag;[spot_path|];eauto.
  Qed.

  Lemma uni_branch_succ_p p q br i j k s1 s2 r r' l1 l2 l2' uni
        (Htr1 : Tr ((p, i,s1) :: (q, j,r) :: l1))
        (Htr2 : Tr ((p, i,s2) :: (br, k,r') :: l2))
        (Hsplit : uni_branch uni br = true)
        (HCuni : forall (x : Var) (p : Lab) (i : Tag) (s s' : State),
            (p, i, s) ∈ ((q, j, r) :: l1) ->
            (p, i, s') ∈ ((br, k, r') :: l2) -> uni p x = true -> s x = s' x)
        (Hpost : Postfix (((q, j) :: l2') :r: (br, k)) ((q, j) :: map fst l1))
    : False.
  Proof.
    destruct (hd (q, j) (rev ((q, j) :: l2'))) eqn:E.
    assert ((e, t) ≻ (br, k) | ((q, j) :: map fst l1)) as Hsucc1.
    {
      eapply postfix_succ_in;eauto.
      rewrite cons_rcons'.
      rewrite E.
      eapply succ_in_rcons2.
    }
    eapply uni_branch_uni_succ' with (q1:=e) (q2:=p) (j1:=t) (j2:=i) in HCuni;cbn;eauto.
    * subst'.
      eapply2 tr_tpath_cons2 Htr1 Htr2;eauto.
      eapply tpath_NoDup in Htr1.
      inversion  Htr1. eapply H1. eapply postfix_incl;eauto.
      eapply In_rcons. right.
      rewrite cons_rcons'. eapply In_rcons. left. eauto.
    * eapply succ_cons. eauto.
    * cbn. eapply succ_in_cons_cons.
  Qed.

  Lemma uni_branch_non_disj p i br k s1 s2 l1 l2 l1' l2' uni p1 p2
        (Hpath1 : Tr ((p,i,s1) :: l1))
        (Hpath2 : Tr ((p,i,s2) :: l2))
        (Hpost1 : Postfix ((p1 :: l1') :r: (br, k)) (map fst l1))
        (Hpost2 : Postfix ((p2 :: l2') :r: (br, k)) (map fst l2))
        (Hdisj : Disjoint (p1 :: l1') (p2 :: l2'))
        (Hsplit : uni_branch uni br = true)
        (HCuni : forall (x : Var) (p : Lab) (i : Tag) (s s' : State),
            (p, i, s) ∈ l1 ->
            (p, i, s') ∈ l2 -> uni p x = true -> s x = s' x)
    : False.
  Proof.
    specialize (cons_rcons' p1 l1') as Hl1'.
    specialize (cons_rcons' p2 l2') as Hl2'.
    set (p1' := hd p1 (rev (p1 :: l1'))) in *.
    set (p2' := hd p2 (rev (p2 :: l2'))) in *.
    enough (p1' = p2').
    - eapply disjoint1 in Hdisj. eapply Hdisj.
      + rewrite Hl2'. eapply In_rcons. left. reflexivity.
      + rewrite Hl1'. eapply In_rcons. left. auto.
    - destruct (p1') as [q1 j1] eqn:Heq1.
      destruct (p2') as [q2 j2] eqn:Heq2.
      eapply uni_branch_uni_succ' with (q1:=q1) (q2:=q2) (j1:=j1) (j2:=j2) (l1:=l1) in Hsplit;eauto.
      1: subst';reflexivity.
      1,2: eapply succ_cons; eapply postfix_succ_in;eauto.
      + rewrite Hl1'. eapply succ_in_rcons2.
      + rewrite Hl2'. eapply succ_in_rcons2.
  Qed.
  Arguments uni_branch_non_disj : clear implicits.


  Lemma uni_same_tag p q i j1 j2 s1 s2 r1 r2 uni l1 l2
        (Htr1 : Tr ((p,i,s1) :: (q,j1,r1) :: l1))
        (Htr2 : Tr ((p,i,s2) :: (q,j2,r2) :: l2))
        (Hsplit : (join_andb (map ((uni_branch uni)) (splitsT p))) = true)
        (HCuni : forall (x : Var) (p : Lab) (i : Tag) (s s' : State),
            (p, i, s) ∈ ((q,j1,r1)::l1) ->
            (p, i, s') ∈ ((q,j2,r2)::l2) ->
            uni p x = true -> s x = s' x)
    : j2 = j1.
  Proof.
    decide' (j1 == j2);[reflexivity|exfalso].
    assert (forall s j r l (Htr : Tr ((p, i, s) :: (q, j, r) :: l)),
               tcfg_edge (q, j) (p, i)) as Htcfg.
    {
      clear. intros.
      eapply Tr_EPath in Htr;[|cbn;eauto]. destructH. eapply EPath_TPath in Htr. cbn in Htr.
      inversion Htr. cbn in H.
      inversion H0;subst; [destruct l;cbn in H9;[|congruence]|].
      + inversion H9;subst;eauto.
      + destruct l;[congruence|]. cbn in H8. eauto.
    }
    copy c Hneq.
    eapply (tag_eq_loop_exit (p:=p) (q:=q) (i:=i)) in c. 2,3: eapply Htcfg;eauto. clear Htcfg.
    eapply tr_lc_lt with (j3:=j1) (j4:=j2) in Htr1 as Hlc;eauto;destructH' Hlc.
    specialize (get_innermost_loop_spec q) as Hspec.
    destruct (get_innermost_loop q) ;[|contradiction].
    destruct brk as [br k].
    eapply lc_disj_exit_lsplits in c as Hsplits;eauto; cycle 1.
    - spot_path.
    - spot_path.
    - unfold last_common in Hlc. destructH.
      destruct l1',l2'.
      + cbn in *. eapply2 postfix_hd_eq Hlc0 Hlc2.
        subst'. congruence.
      +
        cbn in Hlc0.
        destruct p0.
        eapply2' postfix_hd_eq Hlc0 Hlc2 Hlc0' Hlc2'. symmetry in Hlc0'. subst'.
        clear Hlc0 Hlc1 Hlc3 Hlc5.
        eapply join_andb_true_iff in Hsplit;eauto;cycle 1.
        eapply uni_branch_succ_p with (j:=j2);eauto.
        intros;symmetry;eapply HCuni;eauto.
      + cbn in Hlc2.
        destruct p0.
        eapply2' postfix_hd_eq Hlc0 Hlc2 Hlc0' Hlc2'. subst'.
        clear Hlc2 Hlc1 Hlc3 Hlc5.
        eapply join_andb_true_iff in Hsplit;eauto;cycle 1.
        eapply uni_branch_succ_p with (j:=j1);eauto.
      + eapply (uni_branch_non_disj) with (br:=br) (l1:=(q,j1,r1) :: l1) ;eauto;cbn;eauto.
        eapply join_andb_true_iff with (x:=br) in Hsplit.
        cbn in Hsplit. auto.
        auto.
  Qed.

  Hint Resolve Conf_dec.

  Hint Unfold Coord.
  Hint Unfold Tag.
  Hint Immediate tpath_NoDup.
  Hint Resolve precedes_in.


  Lemma prefix_succ_in (A : Type) (a b : A) l l'
        (Hpre : Prefix l l')
        (Hsucc : a ≻ b | l)
    : a ≻ b | l'.
  Proof.
    induction Hpre;eauto.
    eapply IHHpre in Hsucc.
    unfold succ_in in Hsucc. destructH. exists l1, (a0 :: l2). rewrite Hsucc. cbn; reflexivity.
  Qed.

  Local Ltac lc_ex_succ_pre_post :=
    eapply prefix_succ_in; eauto;
    eapply postfix_succ_in; eauto;
    eapply succ_in_rcons2.

  Lemma last_common_ex_succ (A : Type) `{EqDec A eq} (a1 a2 a1' a2' c : A) ll1 ll2 l1 l2
        (Hpre1 : Prefix (a1 :: l1) ll1)
        (Hpre2 : Prefix (a2 :: l2) ll2)
        (Hnin1 : a1' ∉ (a2 :: l2))
        (Hnin2 : a2' ∉ (a1 :: l1))
        (Hsucc1 : a1' ≻ a1 | ll1)
        (Hsucc2 : a2' ≻ a2 | ll2)
        (Hneq : a1 <> a2)
        (Hlc : last_common (a1 :: l1) (a2 :: l2) c)
    : exists (b1 b2 : A), b1 ≻ c | ll1 /\ b2 ≻ c | ll2 /\ b1 <> b2.
  Proof.
    unfold last_common in Hlc. destructH.
    specialize (rcons_destruct l1') as Hl1'.
    specialize (rcons_destruct l2') as Hl2'.
    destruct Hl1', Hl2'; subst; cbn in Hlc0,Hlc2.
    - eapply2' postfix_hd_eq Hlc0 Hlc2 Heq1 Heq2; subst. congruence.
    - destructH. subst. eapply postfix_hd_eq in Hlc0. subst.
      exists a1', a. split_conj;eauto.
      + lc_ex_succ_pre_post.
      + contradict Hnin1. eapply postfix_incl;eauto. rewrite In_rcons. rewrite In_rcons. firstorder 0.
    - destructH. subst. eapply postfix_hd_eq in Hlc2. subst.
      exists a, a2'. split_conj;eauto.
      + lc_ex_succ_pre_post.
      + contradict Hnin2. eapply postfix_incl;eauto. rewrite In_rcons. rewrite In_rcons. subst. firstorder 0.
    - repeat destructH; subst.
      exists a0, a. split_conj.
      + lc_ex_succ_pre_post.
      + lc_ex_succ_pre_post.
      + intro Heq; subst. eapply disjoint1 in Hlc1.
        unfold Disjoint in Hlc1. destruct Hlc1. clear - H0.
        eapply H0; eapply In_rcons; left; eauto.
  Qed.

  Lemma find_divergent_branch u p l1 l2 i j1 j2
        (Hunch : Dom edge__P root u p)
        (Hprec1 : Precedes fst l1 (u, j1))
        (Hprec2 : Precedes fst l2 (u, j2))
        (Htr1 : TPath (root, start_tag) (p, i) ((p, i) :: l1))
        (Htr2 : TPath (root, start_tag) (p, i) ((p, i) :: l2))
        (Hneq : p <> u)
        (Hjneq : j1 <> j2)
    : exists br : Lab,
      br ∈ rel_splits p u /\
      (exists (k k1 k2 : Tag) (q1 q2 : Lab),
          (q1, k1) ≻ (br, k) | (p,i) :: l1 /\ (q2, k2) ≻ (br, k) | (p,i) :: l2 /\ q1 <> q2).
  Proof.
    specialize (ex_near_ancestor u p) as [a [Hanc Ha_near]].
    eapply ancestor_dom1 in Hanc as Hanc1. eapply ancestor_dom2 in Hanc as Hanc2.
    eapply dom_tpath_prec with (l:=(p,i) :: l1) in Hanc2 as Hanc21;eauto. destructH' Hanc21.
    eapply dom_tpath_prec with (l:=(p,i) :: l2) in Hanc2 as Hanc22;eauto. destructH' Hanc22.

    assert (j0 = j); [|subst j0].
    {
      eapply ancestor_sym in Hanc;eapply tag_prefix_ancestor in Hanc21 as Ha_pre1;eauto.
      eapply tag_prefix_ancestor in Hanc22 as Ha_pre2; eauto.
      eapply prec_tpath_tpath in Hanc21;eauto. destructH.
      eapply prec_tpath_tpath in Hanc22;eauto. destructH.
      eapply prefix_length_eq;eauto;eapply tpath_tag_len_eq;eauto.
    }


    enough ((u,j1) ≻* (a,j) | (p,i) :: l1) as Hib1.
    enough ((u,j2) ≻* (a,j) | (p,i) :: l2) as Hib2.

    2: eapply dom_dom_in_between;eauto.
    3: eapply dom_dom_in_between;eauto.
    2,3: econstructor;cbn;eauto.

    assert (Prefix j i) as Hprei by (eapply tag_prefix_ancestor;[eapply ancestor_sym| |];eauto).
    assert (Prefix j j1) as Hprej1
      by (eapply tag_prefix_ancestor_elem with (l:=l1);eauto).
    assert (Prefix j j2) as Hprej2
        by (eapply tag_prefix_ancestor_elem with (l:=l2);eauto).
    (* uses hib12 *)

    assert (exists j1', j1 = j1' ++ j) as [j1' Hj1] by (eapply prefix_eq;eauto).
    assert (exists j2', j2 = j2' ++ j) as [j2' Hj2] by (eapply prefix_eq;eauto).

    assert (j1' <> j2') as c'.
    {
      subst j1 j2. intro c'. rewrite c' in Hjneq. eapply Hjneq. reflexivity.
    }

    eapply Pr_cont with (c:=(p,i)) in Hprec1;[|cbn;eauto].
    eapply Pr_cont with (c:=(p,i)) in Hprec2;[|cbn;eauto].
    (* find the first difference in the tag suffices *)
    eapply first_diff in c';eauto.
    2: assert (| j1 | = | j2 |) as Hlen;
      [(eapply (tpath_tag_len_eq_elem (l1:=(p,i)::l1)) ;eauto;eapply precedes_in;eauto)|].
    2: { subst j1 j2. repeat rewrite app_length in Hlen. clear - Hlen. omega. }
    2,3: intro N; eapply c'; subst;
      eapply precedes_in in Hprec1;eapply precedes_in in Hprec2;
          eapply tpath_tag_len_eq_elem in Hprec1;eauto;
            do 2 rewrite app_length in Hprec1;exfalso.
    3:destruct j1';cbn in Hprec1; [congruence|omega].
    2:destruct j2';cbn in Hprec1;[congruence|omega].
    rename c' into Htag. destructH.
    subst j1' j2'. rewrite <-app_assoc in Hj1,Hj2. rewrite <-app_comm_cons in Hj1,Hj2.
    (* find the head of the divergent loop *)
    eapply first_occ_tag_elem with (t:=(p,i) :: l1) in Hj1 as Hocc1;eauto;
      eauto using precedes_in.
    eapply first_occ_tag_elem in Hj2 as Hocc2;eauto;
      eauto using precedes_in.
    do 2 destructH.
    (* show that it is the same head in both traces *)
    assert (h0 = h);[|subst h0].
    {
      eapply eq_loop_same. 2,3: eauto using loop_contains_loop_head.
      eapply loop_contains_either in Hocc3;eauto.
      destruct Hocc3.
      - eapply loop_contains_deq_loop in H. split;auto.
        eapply deq_loop_depth_eq;eauto.
        erewrite <-tag_depth;eauto.
        erewrite <-tag_depth. 3: eapply precedes_in;eauto. 2:eauto.
        cbn. reflexivity.
      - eapply loop_contains_deq_loop in H. split;auto.
        eapply deq_loop_depth_eq;eauto.
        erewrite <-tag_depth. 3:eapply precedes_in;eauto. 2:eauto.
        erewrite <-tag_depth. 3:eapply precedes_in;eauto. 2:eauto.
        cbn. reflexivity.
    }
    (* find node on ancestor-depth that is between u & p *)
    eapply2 ancestor_level_connector Hanc21 Hanc22. (* uses hib12 *)
    4,8: split;[eapply ancestor_sym|];eauto. all:eauto.
    2,3: clear - Ha_near;intros;destructH;eauto.
    (*clear Hib1 Hib2.*)
    destruct Hanc21 as [a1' [Hanc21 Hanc11]]. destruct Hanc22 as [a2' [Hanc22 Hanc12]].
    assert (Prefix j (l' ++ j)) as Hexit1.
    { eapply prefix_eq. eexists;reflexivity. }
    copy Hexit1 Hexit1'.
    eapply find_loop_exit with (a0:=a1') (n:=a1) (h0:=h) (l:= (p,i)::l1) in Hexit1;eauto.
    eapply find_loop_exit with (a0:=a2') (n:=a2) in Hexit1';eauto.

    2,3: unfold Tag in *; resolve_succ_rt.
    destruct Hexit1 as [qe1 [e1 [Hexit__seq1 [Hexit__succ1 Hexit__edge1]]]].
    destruct Hexit1' as [qe2 [e2 [Hexit__seq2 [Hexit__succ2 Hexit__edge2]]]].
    assert ((qe1, a1 :: l' ++ j) ∈ ((p,i) :: l1)) as Hin1 by find_in_splinter.
    assert ((qe2, a2 :: l' ++ j) ∈ ((p,i) :: l2)) as Hin2 by find_in_splinter.
    eapply2 path_to_elem Hin1 Hin2; eauto.
    destruct Hin1 as [η1 [Hη1 Hpreη1]]. destruct Hin2 as [η2 [Hη2 Hprenη2]].
    assert (exists brk, last_common η1 η2 brk) as Hlc.
    {
      destr_r' η1;subst;[inversion Hη1|]. destr_r' η2;subst;[inversion Hη2|].
      path_simpl' Hη1. path_simpl' Hη2.
      eapply ne_last_common.
    }
    destruct Hlc as [[br k] Hlc].
    enough (η1 = (qe1, a1 :: l' ++ j) :: tl η1) as ηeq1.
    enough (η2 = (qe2, a2 :: l' ++ j) :: tl η2) as ηeq2.
    rewrite ηeq1 in Hlc; rewrite ηeq2 in Hlc.
    2,3: let f := fun Q => clear - Q; inversion Q;subst;cbn;eauto in
         only 2:f Hη1; f Hη2.

    (* I should use a fine-tuned version of the base case of this lemma here instead of the lemma itself *)
    (* Now take the paths br -->* qe1 -> e1 and br --> qe2 -> ledge. These construct a loop_split *)
    (* FIXME *)
    eapply lc_disj_exits_lsplits with (h0:=h) (e3:=e1) (e4:=e2) (i0:=l'++j) in Hlc as Hsplit;eauto.
(*    4: { intro N. inversion N. contradiction. }*)
    all: cycle 1.
    {
      clear - ηeq1 Hη1 Hexit__edge1 Hexit__succ1 Htr1. econstructor. cbn.
      + rewrite ηeq1 in Hη1. eauto.
      + eapply succ_in_path_edge;cycle 1;eauto.
    }
    {
      clear - ηeq2 Hη2 Hexit__edge2 Hexit__succ2 Htr2.  econstructor. cbn.
      + rewrite ηeq2 in Hη2. eauto.
      + eapply succ_in_path_edge;cycle 1;eauto.
    }
    1,2: eapply tpath_NoDup;eauto.
    repeat splice_splinter.
    2-4: eauto.
    exists br; split.
    3-5: eapply tpath_NoDup;eauto.
    - eapply rel_splits_spec. exists h.
      destruct Hsplit as [Hsplit|Hsplit].
      + exists e1.
        repeat lazymatch goal with
               | [H : context C [l2] |- _ ] => clear H
               | [H : context C [qe2] |- _ ] => clear H
               | [H : context C [j2] |- _ ] => clear H
               end.
        split_conj;eauto.
        1: unfold exited;eauto.
        assert (deq_loop u e1) as Hdeq.
        {
          clear - Hexit__edge1 Hocc0.
          eapply deq_loop_trans;cycle 1.
          - eapply deq_loop_exited;eauto.
          - eapply deq_loop_trans;cycle 1.
            + eapply deq_loop_exiting;eauto.
            + eapply loop_contains_deq_loop;eauto.
        }
        eapply (loop_cutting_elem (t:=l1)).
        -- eapply Htr1.
        -- econstructor.
           instantiate (1 := l' ++ j).
           eapply splinter_single.
           unfold Tag in *. find_in_splinter.
        -- intros h0 k0 Hloop0. eapply Hdeq in Hloop0. eapply exit_cascade in Hunch;eauto.
           ++ contradict Hunch.
              instantiate (1 := k0).
              eapply succ_rt_combine;eauto;[eauto| | find_succ_rel].
              eapply tpath_NoDup. eauto.
              eapply (succ_rt_trans) with  (b:=(e1, l' ++ j));eauto;[eauto| |find_succ_rel].
              eapply tpath_NoDup;eauto.
              eapply tpath_deq_loop_prefix; eauto.
              eapply prefix_eq. rewrite app_cons_assoc in Hj1. eexists;eauto.
        -- unfold exited. eauto.
      + exists e2.
        repeat lazymatch goal with
               | [H : context C [l1] |- _ ] => clear H
               | [H : context C [qe1] |- _ ] => clear H
               | [H : context C [j1] |- _ ] => clear H
               end.
        split_conj;eauto.
        1: unfold exited;eauto.
        assert (deq_loop u e2) as Hdeq.
        {
          clear - Hexit__edge2 Hocc0.
          eapply deq_loop_trans;cycle 1.
          - eapply deq_loop_exited;eauto.
          - eapply deq_loop_trans;cycle 1.
            + eapply deq_loop_exiting;eauto.
            + eapply loop_contains_deq_loop;eauto.
        }
        eapply (loop_cutting_elem (t:=l2)).
        -- eapply Htr2.
        -- econstructor.
           instantiate (1 := l' ++ j).
           eapply splinter_single.
           unfold Tag in *. find_in_splinter.
        -- intros h0 k0 Hloop0. eapply Hdeq in Hloop0. eapply exit_cascade in Hunch;eauto.
           ++ contradict Hunch.
              instantiate (1 := k0).
              eapply succ_rt_combine;eauto;[ eauto| | find_succ_rel].
              eauto. eapply tpath_NoDup;eauto.
              eapply (succ_rt_trans) with (b:=(e2, l' ++ j));eauto;[eauto| |find_succ_rel].
              eapply tpath_NoDup;eauto.
              eapply tpath_deq_loop_prefix; eauto.
              eapply prefix_eq. rewrite app_cons_assoc in Hj2. eexists;eauto.
        -- unfold exited;eauto.
    - exists k.
      eapply last_common_ex_succ in Hlc; eauto.
      2: unfold Tag in *; rewrite <-ηeq1;eauto.
      2: unfold Tag in *; rewrite <-ηeq2;eauto.
      4: contradict Htag0; inversion Htag0; eauto.
      clear - Hlc Htr1 Htr2. destructH. destruct b1, b2. exists l, l0, e, e0. split_conj;eauto.
      contradict Hlc3. inversion Hlc3;subst;eauto. f_equal.
      eapply eff_tag_det'; eapply tpath_succ_eff_tag; unfold Coord in *; cycle 1; eauto.
      1: unfold Tag in *; rewrite <-ηeq2.
      2: unfold Tag in *; rewrite <-ηeq1.
      eapply (tpath_exit_nin (h:=h) (q:=qe2));eauto;
        clear - Hexit__edge1 Hexit__edge2; unfold exit_edge in *;unfold exited;
          [|exists qe1]; firstorder 0.
      eapply (tpath_exit_nin (h:=h) (q:=qe1));eauto;
        clear - Hexit__edge1 Hexit__edge2; unfold exit_edge in *;unfold exited;
          [|exists qe2]; firstorder 0.
  Qed.

  Lemma unch_same_tag p u i s1 s2 j1 j2 r1 r2 l1 l2 x uni unch
        (Hunibr : join_andb (map ((uni_branch uni)) (rel_splits p u)) = true)
        (Hunch : u ∈ unch_trans unch p x)
        (HCunch1 : unch_concr' (unch_trans unch) l1)
        (HCunch2 : unch_concr' (unch_trans unch) l2)
        (Hprec1 : Precedes lab_of l1 (u, j1, r1))
        (Hprec2 : Precedes lab_of l2 (u, j2, r2))
        (HCuni : forall (x : Var) (p : Lab) (i : Tag) (s s' : State),
            (p, i, s) ∈ l1 -> (p, i, s') ∈ l2 -> uni p x = true -> s x = s' x)
        (Htr1 : Tr ((p, i, s1) :: l1))
        (Htr2 : Tr ((p, i, s2) :: l2))
        (Hneq : p <> u)
    : j1 = j2.
  Proof.
    assert (forall p i s l (Htr : Tr ((p, i, s) :: l)),
               TPath (root, start_tag) (p, i) ((p, i) :: map fst l)) as Htr_path.
    {
      clear;intros.
      eapply Tr_EPath in Htr;[|reflexivity]. destructH.
      eapply EPath_TPath' in Htr;cbn. 2-4: reflexivity. assumption.
    }
    decide (j1 = j2);[eauto|exfalso].
    specialize (@find_divergent_branch u p (map fst l1) (map fst l2) i j1 j2) as Hwit.
    unfold Tag in *.
    exploit Hwit.
    - eapply unch_dom;eauto.
    - eapply prec_lab_prec_fst;eauto.
    - eapply prec_lab_prec_fst;eauto.
    - destructH.
      eapply join_andb_true_iff in Hunibr;eauto.
      eapply uni_branch_uni_succ
        with (q1:=q1) (q2:=q2) (uni:=uni) in HCuni;eauto.
  Qed.

  Lemma neq_sym (A : Type) (a b : A) : a <> b -> b <> a.
  Proof.
    intros H Q. rewrite Q in H. contradiction.
  Qed.

  Lemma uni_same_lab p q1 q2 i j1 j2 s1 s2 r1 r2 uni l1 l2
        (Htr1 : Tr ((p,i,s1) :: (q1,j1,r1) :: l1))
        (Htr2 : Tr ((p,i,s2) :: (q2,j2,r2) :: l2))
        (Hsplit : (join_andb (map ((uni_branch uni)) (splitsT p))) = true)
        (HCuni : forall (x : Var) (p : Lab) (i : Tag) (s s' : State),
            (p, i, s) ∈ ((q1,j1,r1)::l1) -> (p, i, s') ∈ ((q2,j2,r2)::l2)
            -> uni p x = true -> s x = s' x)
    : q2 = q1.
  Proof.
    eapply tr_lc_lt in Htr1 as LC_lt;eauto. destructH' LC_lt.
    decide (q2 = q1)  as [ Heq | Hneq ]; [ eauto | exfalso ].
    eapply (neq_sym) in Hneq.
    eapply last_common_sym in LC_lt.
    destruct brk as [br k].
    eapply lc_join_split in LC_lt as LC_join;eauto.
    Unshelve. all:cycle 3. exact p. exact i.
    - unfold last_common in LC_lt. destructH.
      eapply join_andb_true_iff in Hsplit;eauto.
      destruct l1',l2'.
      (* we have l1 = nil -> (br,k) = (q1,j1). but:  l1' = nil <-> (br,k) = (q1,j1) *)
      + cbn in *. eapply2 postfix_hd_eq LC_lt0 LC_lt2.
        subst'. congruence.
      + (* since (br,k) = (q1,j1) & uniform, we have that (p,i) succeeds (br,k) thus
         (p,i) ∈ l2, thus double occurence of the same instance in t2 --> contradiction *)
        cbn in LC_lt0.
        destruct p0.
        eapply2' postfix_hd_eq LC_lt0 LC_lt2 LC_lt0' LC_lt2'. symmetry in LC_lt0'. subst'.
        clear LC_lt0 LC_lt1 LC_lt3 LC_lt5.
        eapply uni_branch_succ_p with (q:=q2) (br:=br);eauto.
        intros;symmetry;eapply HCuni;eauto.
      + (* since (br,k) = (q2,j2) & uniform, we have that (p,i) succeeds (br,k) thus
         (p,i) ∈ l1, thus double occurence of the same instance in t1 --> contradiction *)
        cbn in LC_lt0.
        destruct p0.
        eapply2' postfix_hd_eq LC_lt0 LC_lt2 LC_lt0' LC_lt2'. symmetry in LC_lt2'. subst'.
        clear LC_lt2 LC_lt1 LC_lt3 LC_lt5.
        eapply (@uni_branch_succ_p p q1 br i j1 k s1 s2 r1 r2);eauto.
      + (* successor of br is the same because of uniformity and in l1' & l2',
           thus l1' & l2' are not disjoint --> contradiction *)
        eapply (uni_branch_non_disj p i br k _ _ ((q1,j1,r1)::l1)
                                    ((q2,j2,r2)::l2) (l1') (l2'));
          cbn;eauto.
    - spot_path.
    - spot_path.
  Qed.

  Ltac reduce_uni_concr HCuni Hpre1 Hpre2 :=
    clear - HCuni Hpre1 Hpre2; eapply2 prefix_incl Hpre1 Hpre2; intros; eapply HCuni;eauto.

  (** * Correctness **)

  Lemma uni_correct :
    forall uni unch ts,
      sem_hyper (red_prod (uni_concr uni) (lift (unch_concr unch))) ts ->
      uni_concr (uni_trans uni unch) ts.
  Proof.
    intros uni unch ts Hred.
    unfold sem_hyper in Hred.
    destruct Hred as [ts' [Hconcr Hstep]].
    unfold uni_concr.
    intros t t' Hsem Hsem' x p i s s' HIn HIn' Htrans.

    assert (unch_concr (unch_trans unch) t) as HCunch. {
      destruct Hconcr as [_ Hunch].
      unfold lift in *; subst.
      apply unch_correct. assumption.
    }

    assert (unch_concr (unch_trans unch) t') as HCunch'. {
      destruct Hconcr as [ _ Hunch].
      unfold lift in *; subst.
      apply unch_correct. assumption.
    }

    destruct Hconcr as [HCuni  _].

    subst.
    unfold uni_trans in Htrans.
    assert (X := Hsem). destruct X as [t1 [k1 [Hts1 Hteq1]]].
    assert (X := Hsem'). destruct X as [t2 [k2 [Hts2 Hteq2]]].
    decide (p = root); [ subst | ].
    - eapply HCuni; [eapply Hts1|apply Hts2| | | apply Htrans].
      + specialize (root_prefix t1) as [s0 rp]. apply root_start_tag in HIn as rst. subst i.
        eapply prefix_cons_in in rp as rp'.
        assert (Prefix (`t1) (`t)) as pre_t.
        { rewrite Hteq1. cbn. econstructor. econstructor. }
        eapply prefix_trans with (l2:=`t1) (l3:=`t) in rp; eauto.
        apply prefix_cons_in in rp. eapply tag_inj in HIn; [| apply rp].
        subst s0. eauto.
      + specialize (root_prefix t2) as [s0 rp]. apply root_start_tag in HIn as rst. subst i.
        eapply prefix_cons_in in rp as rp'.
        assert (Prefix (`t2) (`t')) as pre_t.
        { rewrite Hteq2. cbn. econstructor. econstructor. }
        eapply prefix_trans with (l2:=`t2) (l3:=`t') in rp; eauto.
        apply prefix_cons_in in rp. eapply tag_inj in HIn'; [| apply rp].
        subst s0. eauto.
    - conv_bool.
      destruct Htrans as [[Htrans Hpred] | Hunch].
      (* The uni/hom case *)
      + rewrite Hteq1 in HIn. rewrite Hteq2 in HIn'.
        eapply in_pred_exists in HIn; try eassumption;
          [|setoid_rewrite <-Hteq1; exact (proj2_sig t)].
        eapply in_pred_exists in HIn'; try eassumption;
          [|setoid_rewrite <-Hteq2; exact (proj2_sig t')].
        destruct HIn as [q [j [r [HIn Hstep]]]].
        destruct HIn' as [q' [j' [r' [HIn' Hstep']]]].
        assert (q ∈ (preds p)) as Hqpred
            by (eapply in_preds;eauto using step_conf_implies_edge,root_no_pred).

        eapply prefix_in_list in HIn as Hpre1. destruct Hpre1 as [l1 Hpre1].
        eapply prefix_in_list in HIn' as Hpre2. destruct Hpre2 as  [l2 Hpre2].

        eapply prefix_trace in Hpre1 as Htr1 ; [|destruct t1; eauto].

        eapply prefix_trace in Hpre2 as Htr2; [|destruct t2;eauto].
        specialize (HCuni t1 t2 Hts1 Hts2).
        cut (q' = q); intros; subst.
        * cut (j' = j); intros; subst.
          -- eapply (@local_uni_corr (uni q) q j p i r r' s s'); try eassumption.
             ** unfold uni_state_concr. intros.
                unfold uni_concr in HCuni .
                eapply (HCuni x0 q j); eassumption.
             ** eapply join_andb_true_iff in Hpred; try eassumption.
          -- eapply uni_same_tag;eauto.
             1,2: econstructor;eauto;eauto.
             reduce_uni_concr HCuni Hpre1 Hpre2.
        * clear HCunch HCunch'.
          eapply uni_same_lab ; eauto.
          1,2: econstructor;eauto;eauto. cbn in HCuni.
          reduce_uni_concr HCuni Hpre1 Hpre2.
      (* The unch case *)
      + rename Hunch into H.
        eapply join_orb_true_iff in H.
        destruct H as [u H].
        conv_bool.
        destruct H as [Hunch [[Hneq' Huni] Hunibr]].
        decide (u = p);cbn in Hneq';[congruence|clear Hneq'].
        copy HCunch HCunch1.
        copy HCunch' HCunch2.
        specialize (HCunch p i s u x HIn Hunch).
        specialize (HCunch' p i s' u x HIn' Hunch).
        destruct HCunch as [j [r [Hprec Heq]]]; try eassumption.
        destruct HCunch' as [j' [r' [Hprec' Heq']]]; try eassumption.
        rewrite <- Heq. rewrite <- Heq'.
        cut (j = j'); intros.
        * subst j'. eapply HCuni. eapply Hts1. eapply Hts2. 3: eauto.
          all: eapply precedes_step_inv.
          -- setoid_rewrite Hteq1 in Hprec. apply Hprec.
          -- rewrite <-Hteq1. destruct t; eauto.
          -- cbn. eauto.
          -- setoid_rewrite Hteq2 in Hprec'. apply Hprec'.
          -- rewrite <-Hteq2. destruct t'; eauto.
          -- cbn;eauto.
        * unfold Precedes' in Hprec,Hprec'. destructH' Hprec. destructH' Hprec'.
          eapply prefix_trace in Hprec0 as Htr1 ; [|destruct t; eauto].
          eapply prefix_trace in Hprec'0 as Htr2; [|destruct t';eauto].
          rewrite Hteq1 in Hprec0. cbn in Hprec0.
          eapply prefix_cons_cons in Hprec0.
          rewrite Hteq2 in Hprec'0. cbn in Hprec'0.
          eapply prefix_cons_cons in Hprec'0.
          eapply unch_same_tag with (l1:=l').
          3: eapply (@unch_concr'_pre _ _ _ _ _ _ t l'); eauto; rewrite Hteq1;cbn;econstructor;eauto.
          3: eapply (@unch_concr'_pre _ _ _ _ _ _ t' l'0);eauto;rewrite Hteq2;cbn;econstructor;eauto.
          1,2,6-8: eauto.
          -- inversion Hprec1;subst;eauto;congruence.
          -- inversion Hprec'1;subst;eauto;congruence.
          -- specialize (HCuni t1 t2 Hts1 Hts2).
             reduce_uni_concr HCuni Hprec0 Hprec'0.
  Qed.

End uniana.
