Require Export TcfgLoop.
Require Import Lia.

(** * Monotonicity & Freshness of tags **)

(** ** Lemmas **)

Section cfg.

  Context `{C : redCFG}.

  Notation "pi -t> qj" := (tcfg_edge pi qj) (at level 50).

  Lemma take_len_id (A : Type) (l : list A)
    : take (|l|) l = l.
  Proof.
    induction l;cbn;eauto.
    rewrite IHl;eauto.
  Qed.

  Lemma take_r_len_id (A : Type) (l : list A)
    : take_r (|l|) l = l.
  Proof.
    unfold take_r. eapply rev_rev_eq. rewrite rev_involutive.
    rewrite <-rev_length. eapply take_len_id.
  Qed.

  Lemma tagle_prefix i j
        (Hpre : Prefix i j)
    : i ⊴ j.
  Proof.
    eapply prefix_eq in Hpre. destructH. subst j.
    induction l2'.
    - cbn. reflexivity.
    - cbn. eapply Tagle_cons. eauto.
  Qed.

  Lemma take_postfix (A : Type) (l : list A) n
    : Postfix (take n l) l.
  Proof.
    eapply postfix_eq.
    revert l.
    induction n;intros;cbn.
    - eexists;eauto.
    - destruct l;cbn.
      + econstructor;eauto.
      + specialize (IHn l). destructH. eexists. f_equal. eauto.
  Qed.

  Lemma take_r_prefix (A : Type) (l : list A) n
    : Prefix (take_r n l) l.
  Proof.
    eapply postfix_rev_prefix'.
    unfold take_r. rewrite rev_involutive.
    eapply take_postfix.
  Qed.

  Lemma take_r_nil (A : Type) n
    : @take_r A n [] = [].
  Proof.
    unfold take_r. cbn. rewrite take_nil. cbn. auto.
  Qed.
  Notation "x ◁ y" := (x ⊴ y /\ x <> y) (at level 70).

  Lemma tagle_or i j
        (Htag : i ⊴ j)
    : |i| <= |j| \/ i ◁ j.
  Proof.
    induction Htag;cbn.
    - left. lia.
    - destruct IHHtag.
      + left. do 2 rewrite app_length. cbn. lia.
      + right. econstructor.
        * econstructor;eauto.
        * destruct H. contradict H0. eapply rcons_eq1. eauto.
    - right. econstructor.
      + econstructor;eauto.
      + intro N. eapply rcons_eq2 in N. lia.
  Qed.

  Lemma take_rcons_ex (A : Type) n (l : list A)
        (Hlen : S n <= |l|)
    : exists a, take (S n) l = take n l ++[a].
  Proof.
    revert l Hlen.
    induction n;intros.
    - cbn. destruct l;[cbn in Hlen;lia|].
      eexists;eauto.
    - destruct l;[cbn in Hlen;lia|].
      rewrite take_one. 2: lia.
      replace (S (S n) - 1) with (S n) by lia.
      rewrite take_one. 2: lia.
      replace (S n - 1) with n by lia.
      specialize (IHn l). exploit IHn.
      + cbn in Hlen. lia.
      + destructH. rewrite IHn. eexists;cbn;eauto.
  Qed.

  Lemma take_r_cons_ex (A : Type) n (l : list A)
        (Hlen : S n <= |l|)
    : exists a, take_r (S n) l = a :: take_r n l.
  Proof.
    rewrite <-rev_length in Hlen.
    specialize (take_rcons_ex Hlen) as H. destructH.
    eexists. unfold take_r. rewrite <-rev_rcons.
    rewrite <-rev_rev_eq. eauto.
  Qed.

  Lemma taglt_eq i j
        (Htlt : i ◁ j)
        (Hlen : |i| = |j|)
    : exists k0 k1 k2 n1 n2, i = k1 ++ n1 :: k0 /\ j = k2 ++ n2 :: k0 /\ n1 < n2.
  Proof.
    destruct Htlt. induction H.
    - cbn in *. symmetry in Hlen. eapply length_zero_iff_nil in Hlen. subst. contradiction.
    - exploit IHTagle.
      + contradict H0. subst. reflexivity.
      + do 2 rewrite app_length in Hlen. clear - Hlen. lia.
      + destructH. do 5 eexists. split_conj;[| |eauto].
        1,2: rewrite <-cons_rcons_assoc; rewrite app_assoc; f_equal; eauto.
    - do 5 eexists. split_conj;[| |eauto].
      1,2: reflexivity.
  Qed.

  Lemma tagle_app_app i j k
    : i ⊴ j -> i ++ k ⊴ j ++ k.
  Proof.
    revert i j. induction k;intros;cbn;eauto.
    - do 2 rewrite <-app_nil_end. eauto.
    - rewrite app_cons_assoc. setoid_rewrite app_cons_assoc at 2.
      eapply IHk. eapply Tagle_rcons;eauto.
  Qed.

  Lemma taglt_cons i j n m
        (Hlen : |i| = |j|)
        (Htlt : i ◁ j)
    : n :: i ◁ m :: j.
  Proof.
    eapply taglt_eq in Htlt;eauto.
    destructH. subst i j.
    split.
    - rewrite app_cons_assoc. setoid_rewrite app_cons_assoc at 2.
      do 4 rewrite app_comm_cons.
      eapply tagle_app_app.
      econstructor;eauto.
    - intro N. inversion N. subst.
      rewrite app_cons_assoc in H1. setoid_rewrite app_cons_assoc in H1 at 2.
      eapply app_inv_tail in H1.
      eapply rcons_eq2 in H1. subst. lia.
  Qed.

  Lemma taglt_tagle i j
        (Htlt : i ◁ j)
    : i ⊴ j.
  Proof.
    firstorder.
  Qed.

  Lemma tagle_taglt_iff i j
    : i ⊴ j <-> i ◁ j \/ i = j.
  Proof.
    split;intros.
    - decide (i = j);[right|left];eauto.
    - destruct H.
      + destruct H;eauto.
      + subst. reflexivity.
  Qed.

  Notation "p '>=' q" := (deq_loop p q).

  Lemma tl_len (A : Type) (l : list A)
    : |tl l| = |l| - 1.
  Proof.
    induction l;cbn;eauto. lia.
  Qed.

  Lemma take_rcons_drop (A : Type) (l : list A) n a
        (Hle : n <= | l |)
    : take n (l ++[a]) = take n l.
  Proof.
    revert l Hle.
    induction n;[cbn;eauto|];intros.
    rewrite rcons_cons'.
    cbn.
    destruct l;cbn.
    - cbn in Hle. lia.
    - cbn in Hle.
      f_equal. eapply IHn. lia.
  Qed.

  Lemma take_r_drop (A : Type) (l : list A) n a
        (Hle : n <= | l |)
    : take_r n (a :: l) = take_r n l.
  Proof.
    unfold take_r.
    rewrite rev_cons. rewrite take_rcons_drop.
    - reflexivity.
    - rewrite rev_length. auto.
  Qed.

  Lemma take_r_tl_eq (A : Type) (l : list A)
    : tl l = take_r (|l| - 1) l.
  Proof.
    rewrite <- tl_len.
    destruct l;eauto. unfold tl in *.
    rewrite take_r_drop;[|eauto].
    rewrite take_r_len_id. reflexivity.
  Qed.

  Lemma tagle_take_r (i j : Tag) (n : nat)
        (Htgl : i ⊴ take_r n j)
    : i ⊴ j.
  Proof.
    rewrite Htgl. eapply prefix_tagle. eapply take_r_prefix.
  Qed.

  Lemma take_r_rcons (A : Type) (l : list A) n a
    : take_r (S n) (l :r: a) = take_r n l :r: a.
  Proof.
    unfold take_r.
    rewrite <-rev_cons.
    rewrite <-rev_rev_eq.
    rewrite rev_rcons.
    rewrite take_one;[|lia].
    cbn.
    replace (n - 0) with n by lia.
    reflexivity.
  Qed.

  Lemma tagle_take_r_leq (i j : Tag) (n : nat)
        (Hleq : |i| <= n)
        (Htgl : i ⊴ j)
    : i ⊴ take_r n j.
  Proof.
    revert n Hleq.
    induction Htgl;intros;cbn.
    - econstructor.
    - rewrite app_length in Hleq. cbn in Hleq.
      destruct n0.
      { exfalso. lia. }
      rewrite take_r_rcons.
      econstructor.
      eapply IHHtgl. lia.
    - destruct n0.
      { exfalso. rewrite app_length in Hleq. cbn in Hleq. lia. }
      rewrite take_r_rcons.
      econstructor;eauto.
  Qed.

  Lemma tagle_STag (i : Tag)
    : i ⊴ STag i.
  Proof.
    induction i;cbn;eauto.
    - reflexivity.
    - eapply Tagle_cons2. lia.
  Qed.

  Lemma take_r_len_leq (A : Type) (l : list A) n
    : |take_r n l| <= n.
  Proof.
    unfold take_r.
    rewrite rev_length.
    rewrite take_length.
    eapply Nat.le_min_r.
  Qed.

  (** ** Weak monotonicity **)

  Lemma tcfg_monotone' p i t q j t' h
        (Hpath : TPath (root,start_tag) (p,i) t)
        (Hsuff : Postfix t' t)
        (Hel : (q,j) ∈ t')
        (Hincl : forall r k, (r,k) ∈ t' -> loop_contains h r)
    : take_r (depth h) j ⊴ i.
  Proof.
    eapply postfix_eq in Hsuff. destructH. subst t.
    revert p i Hpath Hel Hincl. induction t';intros. 1: contradiction. inversion Hpath.
    - subst p i a0. destruct t'.
      + cbn in H4. subst l2' a. destruct Hel;[|contradiction]. inversion H. subst q j.
        rewrite take_r_nil. econstructor.
      + exfalso. cbn in H4. congruence.
    - subst a a0 c π. destruct b as [p' i'].
      destruct Hel as [Hel|Hel].
      { inversion Hel. subst. eapply tagle_prefix. eapply take_r_prefix. }
      eapply tcfg_edge_destruct' in H4. destruct H4 as [Q|[Q|[Q|Q]]]. all: destruct Q as [Htag Hedge].
      + rewrite <-Htag in *.
        rewrite IHt'. 2:eauto. all:eauto. reflexivity.
      + rewrite Htag in *. rewrite IHt'. 2:eauto. all:eauto. eapply Tagle_cons. reflexivity.
      + subst i. rewrite IHt'. 2:eauto. all:eauto.
        eapply tagle_STag.
      + subst i.
        rewrite take_r_tl_eq. eapply tagle_take_r_leq;cycle 1.
        * eapply IHt'. eauto. all:eauto.
        * rewrite <-tl_len.
          setoid_rewrite tag_depth at 2.
          -- rewrite take_r_len_leq.
             eapply deq_loop_depth.
             eapply loop_contains_deq_loop.
             eapply Hincl. left;eauto.
          -- eapply Hpath.
          -- left;eauto.
  Qed.

  Lemma splinter_strict_suffix (L : Type) `{EqDec L eq} (e: L -> L -> Prop) x y z π
        (Hpath : Path e x y π)
        (Hsp : splinter_strict [y;z] π)
    : exists ϕ, Path e z y ϕ /\ Postfix ϕ π /\ 2 <= |ϕ|.
  Proof.
    inversion Hpath;subst.
    - exfalso. inversion Hsp;subst. inversion H1. inversion H2.
    - assert (z ∈ π0) as Hel.
      + inversion Hsp;subst;eapply splinter_strict_incl;eauto.
      + eapply path_from_elem in Hel;eauto.
        destructH. exists (y :: ϕ). split_conj.
        * econstructor;eauto.
        * eapply postfix_cons;eauto.
        * destruct ϕ;[inversion Hel0|]. cbn. lia.
  Qed.

  Require Import GetSucc.


  Lemma taglt_tagle_trans (i j k : Tag)
    : i ◁ j -> j ⊴ k -> i ◁ k.
  Proof.
    intros. split;[destruct H;transitivity j;eauto|].
    destruct H.
    contradict H1. subst i.
    eapply antisymmetry;eauto.
  Qed.

  Lemma tagle_nil_eq (i : Tag)
    : i ⊴ [] -> i = [].
  Proof.
    intros. inversion H;subst;eauto;try congruence'.
  Qed.

  Lemma tagle_taglt_trans (i j k : Tag)
    : i ⊴ j -> j ◁ k -> i ◁ k.
  Proof.
    intros. split;[destruct H0;transitivity j;eauto|].
    destruct H0.
    contradict H1. subst i.
    eapply antisymmetry;eauto.
  Qed.

  Lemma filter_nil (A : Type) (f : decPred A) l
        (Hnil : filter f l = [])
    : forall x, x ∈ l -> ~ f x.
  Proof.
    induction l;intros;cbn.
    - contradiction.
    - destruct H;subst.
      + cbn in Hnil. decide (f x);[congruence|auto].
      + eapply IHl;eauto. cbn in Hnil. decide (f a);[congruence|auto].
  Qed.

  Lemma loop_contains_depth_lt h p
        (Hloop : loop_contains h p)
    : depth p > 0.
  Proof.
    unfold depth.
    match goal with |- length ?x > 0 => enough (x <> []) end.
    - enough (depth p <> 0). 1:unfold depth in *;lia.
      contradict H.
      eapply length_zero_iff_nil. eauto.
    - intro N. eapply filter_nil;eauto.
  Qed.

  Lemma tcfg_head_taglt h q j k t
        (Hloop : loop_head h)
        (Hpath : TPath (root,start_tag) (q,j) t)
        (Hedge : (q,j) -t> (h,k))
    : j ◁ k.
  Proof.
    eapply tcfg_edge_destruct' in Hedge. destruct Hedge as [Q|[Q|[Q|Q]]].
    all: destruct Q as [Heq Hedge];subst.
    1,4:exfalso.
    - eapply basic_edge_no_loop2;eauto.
    - unfold eexit_edge in Hedge. destructH. eapply no_exit_head;eauto.
    - split.
      + eapply Tagle_cons. reflexivity.
      + intro N. eapply cons_neq;eauto.
    - destruct j.
      + exfalso. eapply loop_contains_ledge in Hedge.
        eapply tag_depth' in Hpath. cbn in Hpath.
        eapply loop_contains_depth_lt in Hedge. lia.
      + cbn. split;[eapply tagle_STag|intro N;inversion N]. lia.
  Qed.

  Lemma postfix_eq_app (A : Type) (l l' : list A)
    : Postfix l (l ++ l').
  Proof.
    induction l;cbn.
    - eapply postfix_nil.
    - eapply postfix_cons. auto.
  Qed.

  (** ** Freshness **)

  Lemma tcfg_fresh p i t
        (Hpath : TPath (root,start_tag) (p,i) t)
        (Hsp : splinter_strict [(p,i);(p,i)] t)
    : False.
  Proof.
    eapply splinter_strict_suffix in Hsp;eauto.
    destructH.
    copy Hsp0 Hpath'.
    eapply TPath_CPath in Hsp0. cbn in Hsp0.
    eapply p_p_ex_head in Hsp0;eauto.
    2: { rewrite map_length. lia. }
    destructH.
    (* destruct ϕ *)
    destr_r' ϕ. all: subst ϕ. 1:cbn in Hsp3;lia.
    destruct l. 1: cbn in Hsp3; lia.
    path_simpl' Hpath'. cbn in Hpath'. path_simpl' Hpath'. rename x into y.
    let tac Q :=
        rewrite map_rcons in Q;rewrite map_cons in Q;unfold fst in Q at 1 3
                               in tac Hsp1; tac Hsp4.
    (* some ridiculous simplifications *)
    assert (forall z, z ∈ ((p :: map fst l :r: p)) <-> z ∈ (p :: map fst l)) as H2cons.
    { clear. intros. cbn. setoid_rewrite In_rcons. firstorder. }
    rewrite H2cons in Hsp1. setoid_rewrite H2cons in Hsp4.
    remember (find (fun y => decision (fst y = h)) ((p,i) :: l)) as x. symmetry in Heqx.
    destruct x;cycle 1. (* show the existence of such x *)
    { fold (fst (p,i)) in Hsp1. rewrite <-map_cons in Hsp1.
      eapply in_fst in Hsp1. destructH. eapply find_none in Heqx. 2:eapply Hsp1. cbn in Heqx.
      decide (h = h);inversion Heqx. contradiction. }
    eapply find_some in Heqx. destructH.
    destruct p1 as [e k]. cbn in Heqx1. decide (e = h);[|inversion Heqx1].
    subst e. clear Heqx1.
    remember (get_pred (h,k) (p,i) ((p,i) :: l)) as rj.
    destruct rj as [r j].
    specialize (get_pred_cons (p,i) Heqx0) as Hsucc.
    rewrite <-Heqrj in Hsucc. copy Hsp2 Hsp2'.
    eapply postfix_eq in Hsp2. destructH.
    assert (TPath (root,start_tag) (p,i) ((p,i)::l2')) as Hpath0.
    { eapply path_prefix_path. 2: eapply Hpath. 1:eauto. eapply prefix_eq.
      eexists;eauto. rewrite <-app_assoc in Hsp2. eauto. }
    eapply path_to_elem in Hpath' as Hpath_r.
    2: { cbn. right. eapply in_succ_in2. cbn in Hsucc;eauto. }
    destructH.
    eapply path_app' in Hpath_r0 as Hpath_r'. 2: eapply Hpath0.
    assert (take_r (depth h) i ⊴ j) as Hij.
    {
      eapply tcfg_monotone'.
      instantiate (2 := r).
      - eapply Hpath_r'.
      - instantiate (1:=ϕ).
        eapply postfix_eq_app.
      - eapply path_contains_back;eauto.
      - intros. eapply Hsp4. eapply H2cons.
        eapply prefix_incl in H;eauto.
        eapply in_map with (f:=fst) in H. cbn in H. rewrite map_rcons in H. cbn in H.
        cbn;eauto.
    }
    assert (j ◁ k) as Hjk. {
      eapply tcfg_head_taglt.
      - eapply loop_contains_loop_head. eapply Hsp4. left. auto.
      - eapply Hpath_r'.
      - eapply succ_in_path_edge; cycle 1;eauto.
    }
    assert (k = take_r (depth h) k) as Hkeq.
    {
      replace (depth h) with (|k|). 1:symmetry;eapply take_r_len_id.
      eapply tag_depth. 1: eapply Hpath. eapply postfix_incl;eauto.
    }
    assert (take_r (depth h) k ⊴ take_r (depth h) i) as Hki.
    {
      eapply tagle_take_r_leq. 1: eapply take_r_len_leq.
      eapply tcfg_monotone'. 1: eapply Hpath. 1:eauto.
      - eapply in_succ_in1;eauto.
      - intros. eapply Hsp4.
        eapply H2cons.
        eapply in_map with (f:=fst) in H. cbn in H. rewrite map_rcons in H. cbn in H.
        cbn;eauto.
    }
    rewrite <-Hkeq in Hki.
    eapply tagle_taglt_trans in Hjk;eauto.
    eapply taglt_tagle_trans in Hjk;eauto.
    destruct Hjk. eapply H0. reflexivity.
  Qed.

  (* TODO: move ex_entry proof to this point. it does not require any assumptions,
thus it should be possible *)
  Lemma tcfg_fresh_head' h p i k t
        (Hpath : TPath (root,start_tag) (h,0::k) t)
        (Hloop : loop_contains h p)
        (Hsp : splinter_strict [(h,0::k);(p,i)] t)
        (Hpre : Prefix k i)
    : False.
  (*
   * find entry of h corresponding to (p,i) in t with tag 0::k', where Prefix k' i.
   * bc freshness we have 0::k <> 0::k', thus bc |k|=|k'| also k <> k' cntrdiction.
   *)
  Admitted.

  Lemma take_r_leq_id (A : Type) (l : list A) n
        (Hlen : |l| <= n)
    : take_r n l = l.
  Proof.
    unfold take_r.
    rewrite take_eq_ge.
    - rewrite rev_involutive. reflexivity.
    - rewrite rev_length. lia.
  Qed.

  (** ** Strong monotonicity **)

  Lemma tcfg_monotone p i t q j a
        (Hpath : TPath (root,start_tag) (p,i) t)
        (Hel : (q,j) ∈ t)
        (Hdeqp : p >= a)
        (Hdeqq : q >= a)
    : take_r (depth a) j ⊴ i.
  Proof.
    revert p i q j a Hpath Hel Hdeqp Hdeqq. induction t;intros;inversion Hpath.
    - symmetry in H1,H2. subst. destruct Hel as [Hel|Hel];inversion Hel. subst q j.
      rewrite take_r_nil. econstructor.
    - subst. destruct b as [p' i'].
      destruct Hel as [Hel|Hel].
      { inversion Hel. subst. eapply tagle_prefix. eapply take_r_prefix. }
      eapply tcfg_edge_destruct' in H4. destruct H4 as [Q|[Q|[Q|Q]]].
      1-4:destruct Q as [Htag Hedge].
      +
        rewrite <-Htag in *.
        rewrite IHt;eauto.
        * reflexivity.
        * destruct Hedge as [[Hedge _] _]. transitivity p;eauto.
      + decide (eq_loop a0 p).
        * specialize (IHt _ _ _ _ p' H3 Hel). exploit IHt. 1: reflexivity.
          { transitivity p.
            - rewrite <-e. eauto.
            - eapply deq_loop_entry;eauto.
          }
          subst i. rewrite e.
          setoid_rewrite <-depth_entry;eauto.
          destruct j.
          -- rewrite take_r_nil. econstructor.
          -- copy IHt IHt'.
             eapply tagle_taglt_iff in IHt.
             destruct IHt.
             ++ assert (depth p' = |i'|) as Hpieq.
                { symmetry. eapply tag_depth';eauto. }
                rewrite Hpieq in *.
                decide (|n :: j| <= |i'|).
                ** rewrite take_r_leq_id. 2: lia.
                   eapply Tagle_cons. rewrite take_r_leq_id in IHt'. 2: lia. eauto.
                ** assert (S (|i'|) <= |n :: j|) as n1. 1: clear - n0;lia.
                   specialize (take_r_cons_ex n1) as Q. destructH' Q. rewrite Q.
                   eapply taglt_tagle. eapply taglt_cons. 2:eauto.
                   unfold take_r. rewrite rev_length,take_length,rev_length.
                   clear - n1. rewrite Nat.min_r. auto. lia.
             ++ exfalso.
                eapply tcfg_fresh_head'.
                ** cbn in Hpath. eapply Hpath.
                ** instantiate (1:=q).
                   eapply deq_loop_head_loop_contains.
                   --- rewrite <-e. eauto.
                   --- destruct Hedge. auto.
                ** econstructor. eapply splinter_strict_single;eauto.
                ** rewrite <- H. eapply take_r_prefix.
        (* contradiction to freshness:
         * find an acyclic path from p' to q, then argue it has the same tag prefix as q
         * contradiction to strict freshness *)
        (* there should be a contradiction somewhere along these lines:
         * deq_loop q p, thus there is an acyclic path from p' to q.
         * thus there is header containing p' on q --> q, well,
         * and then we need stuff from the freshness proof sketch,
         * looks like this induction scheme is broken *)
        (**)
        * rewrite Htag in *.
          rewrite IHt;eauto.
          eapply Tagle_cons. reflexivity.
          -- simpl_dec' n. destruct n;try contradiction.
             intros h' Hh'.
             eapply deq_loop_entry_or in Hedge.
             ++ destruct Hedge;eauto. subst. exfalso. clear - H Hh'. eauto using loop_contains_deq_loop.
             ++ eapply Hdeqp in Hh'. eauto.
      + rewrite Htag in *.
        rewrite IHt. 2,3,5:eauto.
        * eapply tagle_STag.
        * eapply back_edge_eq_loop in Hedge. destruct Hedge. transitivity p;eauto.
      + subst i.
        rewrite take_r_tl_eq. eapply tagle_take_r_leq;cycle 1.
        * eapply IHt. eauto. all:eauto. transitivity p;eauto. destruct Hedge.
          eapply deq_loop_exited;eauto.
        * rewrite <-tl_len.
          setoid_rewrite tag_depth at 2.
          -- rewrite take_r_len_leq.
             eapply deq_loop_depth.
             exact Hdeqp.
          -- eapply Hpath.
          -- left;eauto.
  Qed.

  (** ** Corollaries **)

  Lemma tcfg_monotone_deq p q i j t
        (Hdeq : deq_loop p q)
        (Hpath : TPath (root, start_tag) (p, i) t)
        (Hel : (q,j) ∈ t)
    : j ⊴ i.
  Proof.
    eapply tcfg_monotone in Hpath as Hmon;eauto. 2:reflexivity.
    erewrite <-tag_depth in Hmon;eauto.
    rewrite take_r_len_id in Hmon. eauto.
  Qed.

  (*
Lemma eff_tag_unfresh q j t p
      (Hpath : TPath (root,start_tag) (q,j) t)
      (Hedge : edge__P q p)
      (Hel : (p,eff_tag' j Hedge) ∈ t)
  : False.
Proof.
  set (j':=eff_tag' j Hedge) in *.
  eapply PathCons with (edge:=tcfg_edge) in Hpath;cycle 1.
  - instantiate (1:=(p,j')). split;eauto. subst j'. unfold eff_tag.
    decide (edge__P q p);[|contradiction].
    erewrite eff_tag'_eq. reflexivity.
  - eapply tcfg_fresh;eauto.
    econstructor. eapply splinter_strict_single;eauto.
Qed.
   *)

  Lemma succ_in_tpath_tcfg_edge
    : forall (p q : Lab) (i j : Tag) (t : list Coord) (a b : Coord),
      TPath a b t -> (p, i) ≻ (q, j) | t -> tcfg_edge (q,j) (p,i).
    (* PROVEME (analogous to below lemma) *)
  Admitted.

  (* TODO: remove (after proof is adjusted to above lemma) *)
  Lemma succ_in_tpath_eff_tag p q i j t a b
        (Hpath : TPath a b t)
        (Hsucc : (p,i) ≻ (q,j) | t)
    : eff_tag q p j = Some i.
  Proof.
    unfold succ_in in Hsucc. destructH.
    revert dependent t. revert b. induction l2; cbn in *; intros.
    - rewrite Hsucc in Hpath. unfold TPath in Hpath. destruct b.
      inversion Hpath. subst. destruct b. inversion H3;subst;destruct H5;eauto.
    - destruct t. 1: inversion Hpath.
      inversion Hsucc. subst. inversion Hpath;subst. 1: congruence'.
      eauto.
  Qed.

End cfg.
