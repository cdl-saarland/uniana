Require Export NinR.


  Lemma last_common'_in1 (A : Type) `(EqDec A eq) (l1 l2 l1' l2' : list A) (a : A)
        (Hlc : last_common' l1 l2 l1' l2' a)
    : a ∈ l1.
  Proof.
    unfold last_common' in Hlc. destructH.
    eapply postfix_incl;eauto.
  Qed.

  Lemma last_common'_in2 (A : Type) `(EqDec A eq) (l1 l2 l1' l2' : list A) (a : A)
        (Hlc : last_common' l1 l2 l1' l2' a)
    : a ∈ l2.
  Proof.
    eapply last_common'_sym in Hlc.
    eapply last_common'_in1;eauto.
  Qed.

Section disj.

  Context `{C : redCFG}.

  Infix "⊴" := Tagle (at level 70).

  Notation "p '-a>b' q" := (a_edge p q) (at level 55).
  Notation "p '-a>' q" := (p -a>b q = true) (at level 55).
  Notation "p '-->b' q" := (edge p q) (at level 55).
  Notation "p '-->' q" := (p -->b q = true) (at level 55, right associativity).

  Variable (t1 t2 : list (Lab * Tag)) (r1 r2 : list (Lab * Tag)) (q1 q2 s : Lab) (j1 j2 k : Tag).
  Hypotheses (Hlc : last_common' t1 t2 r1 r2 (s,k))
             (Hpath1 : TPath (root,start_tag) (q1,j1) t1)
             (Hpath2 : TPath (root,start_tag) (q2,j2) t2)
             (*           (Hneq : r1 <> r2) (* <-> r1 <> nil \/ r2 <> nil *)*)
             (Hloop : eq_loop q1 q2)
             (Htag : tl j1 = tl j2)
             (Htagleq : hd 0 j1 <= hd 0 j2).

  Hypothesis (Hdep : depth s = depth q1).

  Lemma s_eq_q1
    : eq_loop s q1.
  Proof.
    eapply dep_eq_impl_head_eq in Hdep;eauto.
  Qed.

  Lemma k_eq_j1
    : k = j1.
  Proof.
    symmetry.
    eapply prefix_length;eauto.
    - eapply j1_prefix_k;eauto.
    - clear Hpath2. erewrite tag_depth;eauto.
      + erewrite tag_depth.
        * symmetry;eapply Hdep.
        * eapply Hpath1.
        * eapply last_common'_in1;eauto.
      + eapply path_contains_front;eauto.
  Qed.

  Lemma ex_entry_r1 h i
        (Hel : (h,i) ∈ r1)
        (Hndeq : ~ deq_loop q1 h)
        (Hexit : exists e : Lab, exited h e /\ deq_loop q1 e)
    : (h,0 :: tl i) ∈ r1.
  Proof.
    eapply ex_entry_elem in Hpath1 as Hentry.
    - enough ((h, 0 :: tl i) ∈ (r1 :r: (s,k))).
      { eapply In_rcons in H. destruct H;[|auto].
        exfalso. inversion H. subst h.
        specialize (s_eq_q1) as Q. destruct Q. contradiction.
      }
      unfold last_common' in Hlc.
      destructH.
      eapply postfix_eq in Hlc0. destructH' Hlc0.
      eapply succ_NoDup_app.
      3: eapply In_rcons;left;reflexivity.
      + setoid_rewrite <-Hlc0. eauto.
      + setoid_rewrite <-Hlc0. eapply tpath_NoDup;eauto.
    - split.
      + eapply loop_contains_self.
        destructH. unfold exited,exit_edge in Hexit0. destructH.
        eapply loop_contains_loop_head;eauto.
      + eapply deq_loop_refl.
    - rewrite s_eq_q1. contradict Hndeq. eapply loop_contains_deq_loop;eauto.
    - eapply lc_succ_rt1;eauto.
  Qed.

  Lemma prefix_length_leq (A : Type) (l l' : list A)
        (Hpre : Prefix l l')
    : | l | <= | l' |.
  Proof.
    clear - Hpre.
    induction Hpre.
    - reflexivity.
    - cbn. omega.
  Qed.

End disj.

(** Close and reopen section to instantiate with other variables **)

Section disj.

  Context `{C : redCFG}.

  Infix "⊴" := Tagle (at level 70).

  Notation "p '-a>b' q" := (a_edge p q) (at level 55).
  Notation "p '-a>' q" := (p -a>b q = true) (at level 55).
  Notation "p '-->b' q" := (edge p q) (at level 55).
  Notation "p '-->' q" := (p -->b q = true) (at level 55, right associativity).

  Variable (t1 t2 : list (Lab * Tag)) (r1 r2 : list (Lab * Tag)) (q1 q2 s : Lab) (j1 j2 k : Tag).
  Hypotheses (Hlc : last_common' t1 t2 r1 r2 (s,k))
             (Hpath1 : TPath (root,start_tag) (q1,j1) t1)
             (Hpath2 : TPath (root,start_tag) (q2,j2) t2)
             (*           (Hneq : r1 <> r2) (* <-> r1 <> nil \/ r2 <> nil *)*)
             (Hloop : eq_loop q1 q2)
             (Htag : tl j1 = tl j2)
             (Htagleq : hd 0 j1 <= hd 0 j2).

  Hypothesis (Hdep : depth s = depth q1).

  Lemma s_eq_q1'
    : eq_loop s q1.
  Proof.
    eapply s_eq_q1.
    3: eauto. all: eauto.
  Qed.

  Section same_tag.
    Variable (r3 : list (Lab * Tag)) (q3 : Lab).
    Hypotheses (Hpre : Prefix r3 r2) (Hhd : hd_error (r3 :r: (s,k)) = Some (q3,j1)).

    Lemma r3_tpath
      : TPath (s,k) (q3,j1) (r3 :r: (s,k)).
    Proof.
      unfold last_common' in Hlc. destructH.
      eapply postfix_path in Hlc2;eauto.
      eapply prefix_rcons in Hpre.
      rewrite rcons_cons' in Hpre.
      rewrite rcons_cons' in Hhd. cbn in Hhd. inversion Hhd.
      eapply path_prefix_path in Hpre.
      - rewrite <-rcons_cons' in Hpre. eauto.
      - eauto.
      - eauto.
    Qed.

    Lemma disjoint3
      : Disjoint r1 r3.
    Proof.
      eapply disjoint_subset.
      - reflexivity.
      - eapply prefix_incl;eauto.
      - unfold last_common' in Hlc. destructH. eauto.
    Qed.

    Local Definition t3 := r3 :r: (s,k) ++ prefix_nincl (s,k) t2.

    Lemma t3_postfix
      : Postfix (r3 :r: (s,k)) t3.
    Proof.
      eapply postfix_eq. exists (prefix_nincl (s,k) t2). unfold t3.
      reflexivity.
    Qed.

    Lemma t2_eq
      : t2 = r2 :r: (s,k) ++ prefix_nincl (s,k) t2.
    Proof.
      unfold last_common' in Hlc. destructH.
      clear - Hpath2 Hlc2.
      eapply postfix_eq in Hlc2. destructH.
      enough (l2' = prefix_nincl (s,k) t2).
      { rewrite <-H. eauto. }
      rewrite Hlc2.
      eapply tpath_NoDup in Hpath2.
      setoid_rewrite Hlc2 in Hpath2. clear Hlc2.
      induction r2;cbn.
      - destruct (s == s).
        + destruct (k == k).
          * reflexivity.
          * congruence.
        + congruence.
      - destr_let. cbn in Hpath2. destruct (s == e).
        + destruct (k == t).
          * exfalso. inversion Hpath2.
            eapply H1. eapply in_or_app. left. eapply in_or_app. right. left.
            f_equal. rewrite e0. reflexivity.  rewrite e1. reflexivity.
          * eapply IHl. inversion Hpath2. eauto.
        + eapply IHl.
          inversion Hpath2. eauto.
    Qed.

    Lemma t3_prefix
      : Prefix t3 t2.
    Proof.
      rewrite t2_eq. eapply prefix_eq.
      unfold t3. eapply prefix_eq in Hpre as Hpre'. destructH' Hpre'.
      rewrite Hpre'. eexists.
      rewrite app_assoc.
      rewrite <-app_rcons_assoc. reflexivity.
    Qed.

    Lemma t3_tpath
      : TPath (root,start_tag) (q3,j1) t3.
    Proof.
      unfold t3.
      replace (prefix_nincl (s,k) t2) with (tl ((s,k) :: prefix_nincl (s,k) t2)) by (cbn;eauto).
      eapply path_app'.
      - eapply path_prefix_path;eauto.
        eapply prefix_eq. setoid_rewrite t2_eq at 1.
        rewrite <-app_cons_assoc. eexists. reflexivity.
      - eapply r3_tpath.
    Qed.

    Lemma q3_eq_loop
      : eq_loop q3 q1.
    Proof.
      decide (r3 = []).
      {
        subst. cbn in Hhd. inversion Hhd. subst.
        eapply s_eq_q1;eauto.
      }
      enough (deq_loop q3 q1).
      {
        split;auto.
        eapply deq_loop_depth_eq;eauto.
        setoid_rewrite <-tag_depth at 2.
        - erewrite tag_depth.
          + reflexivity.
          + eapply Hpath1.
          + eapply path_contains_front;eauto.
        - eapply t3_tpath.
        - eapply path_contains_front;eauto. eapply t3_tpath.
      }
      rewrite Hloop.
      replace q3 with (fst (q3,j1)) by (cbn;eauto).
      eapply r2_in_head_q;eauto.
      destruct r3;[contradiction|]. cbn in Hhd.
      eapply prefix_incl;eauto. left. inversion Hhd. reflexivity.
    Qed.

    Lemma last_common_t3_r3
      : last_common' t3 t1 r3 r1 (s,k).
    Proof.
      unfold last_common' in *. destructH. split_conj;eauto.
      - eapply t3_postfix;eauto.
      - eapply Disjoint_sym. eapply disjoint3.
      - contradict Hlc5. eapply prefix_incl;eauto.
    Qed.

    Hint Resolve t3_tpath t3_prefix t3_postfix last_common_t3_r3 q3_eq_loop.

    (** Now all properties of r1 or r3 also hold for r3,
        we can use eapply3 to apply corresponding lemmas **)

    Ltac eapply3 H :=
      eapply H;
      try (lazymatch goal with
           | |- last_common' _ _ _ _ _ =>
             tryif eapply last_common_t3_r3
             then idtac
             else eapply last_common'_sym;eapply last_common_t3_r3
           end
          );
      try eapply Hpath1;try eapply Hpath2;try eapply t3_tpath;
      eauto;
      try (rewrite q3_eq_loop;eauto).

    Ltac eapply3' H Q :=
      eapply H in Q;
      try (lazymatch goal with
           | |- last_common' _ _ _ _ _ =>
             tryif eapply last_common_t3_r3
             then idtac
             else eapply last_common'_sym;eapply last_common_t3_r3
           end
          );
      try eapply Hpath1;try eapply Hpath2;try eapply t3_tpath;
      eauto;
      try (rewrite q3_eq_loop;eauto).

    Hint Rewrite q3_eq_loop.

    Lemma disj_node
      : Disjoint (map fst r1) (map fst r3).
    Proof.
    Admitted.
  End same_tag.

  (** * For j1 = j2, r1 and r2 are disjoint **)

  Lemma lc_eq_disj
        (Hjeq : j1 = j2)
    : Disjoint (map fst r1) (map fst r2).
  Proof.
    eapply disj_node; [reflexivity| ].
    instantiate (1:=q2).
    unfold last_common' in Hlc. destructH.
    eapply postfix_path in Hpath2;eauto.
    rewrite rcons_cons' in Hpath2.
    eapply path_front in Hpath2. rewrite Hjeq.
    destruct r2;cbn in *;inversion Hpath2; reflexivity.
  Qed.

  Print Assumptions lc_eq_disj.
  (** * For j1 <> j2, there is a disjoint prefix **)

  Lemma lc_neq_disj
        (Hjneq : j1 <> j2)
    : exists r', Prefix ((get_innermost_loop' q1) :: r') (map fst r2)
            /\ Disjoint (map fst r1) r'.
  Proof.
    exists (map fst (while (DecPred (fun x : Coord => Prefix j1 (snd x))) r2)).
    split.
    - admit. (*bc j1 <> j2 the front of while... is not (_,q2), thus strictly a prefix and
               a backedge source *) (* FIXME *)
    - eapply disj_node.
      + eapply while_prefix. reflexivity.
      + (* bc backedge source front of while... has tag j1 *) (* FIXME *)  admit.
  Admitted.

End disj.
