Require Export TcfgLoop Disjoint.
Require Import MaxPreSuffix Lia.



Lemma path_nlrcons_edge {A : Type} (a b c : A) l f
      (Hpath : Path f b c (l :r: a :r: b))
  : f b a.
Proof.
  revert dependent c.
  induction l; intros; inversion Hpath; subst; cbn in *.
  - inversion H3. subst b0 b;auto. inversion H5.
  - congruence'.
  - eauto.
Qed.

Section cfg.
  Context `(C : redCFG).
  Lemma geq_tag_suffix_deq (p q : Lab) l t i j
        (Hpath : TPath (root,start_tag) (q,j) t)
        (Hpost : Postfix l t)
        (HForall : Forall (DecPred (fun xl => |j| <= |snd xl|)) l)
        (Hel : (p,i) ∈ l)
    : deq_loop p q.
  Proof.
    rewrite Forall_forall in HForall. cbn in HForall.
    revert dependent t. revert dependent p. revert i.
    rinduction l.
    - contradiction.
    - eapply In_rcons in Hel. destruct Hel.
      + subst a.
        specialize (rcons_destruct l0) as Hl0. destruct Hl0;[|destructH];subst l0.
        * cbn in *.
          inversion Hpath;subst;eapply postfix_hd_eq in Hpost;
            inversion Hpost;subst;eapply deq_loop_refl.
        * copy Hpost Hpost'.
          eapply postfix_path in Hpost;eauto.
          eapply path_nlrcons_edge in Hpost.
          destruct a.
          destruct (tag_deq_or_entry Hpost) as [Hdeq|Hentry].
          -- eapply deq_loop_trans;eauto. eapply H;eauto.
             ++ eapply postfix_step_left;eauto.
          -- eapply tag_entry_iff in Hentry;eauto. subst t0.
             assert (|j| <= |i|) as Hleq.
             { specialize (HForall (p,i));cbn in HForall.
               eapply HForall. eapply In_rcons. left;reflexivity.
             }
             intros h Hloop.
             decide (h = e).
             ++ subst h. exfalso.
                assert (|j| < |0 :: i|) as Hleq'.
                { cbn. lia. }
                eapply loop_contains_deq_loop in Hloop.
                eapply deq_loop_depth in Hloop.
                enough (|0 :: i| <= |j|) by lia.
                erewrite tag_depth;eauto.
                erewrite tag_depth;eauto.
                ** inversion Hpath;cbn;auto.
                ** eapply postfix_incl;eauto.
             ++ eapply preds_in_same_loop;cycle 1;eauto 1.
                ** unfold tcfg_edge in Hpost. destructH. auto.
                ** eapply H;eauto.
                   --- eapply postfix_step_left;eauto.
      + eapply H;eauto.
        * eapply postfix_step_left;eauto.
  Qed.

  Lemma geq_tag_suffix_tag_tl_eq (p q : Lab) l t i j
        (Hpath : TPath (root,start_tag) (q,j) t)
        (Hpost : Postfix l t)
        (HForall : Forall (DecPred (fun xl => |j| <= |snd xl|)) l)
        (Hel : (p,i) ∈ l)
    : take_r (| tl j |) i = tl j.
  Proof.
    rewrite Forall_forall in HForall. cbn in *.
    eapply prefix_take_r.
    revert dependent t. revert dependent p. revert i.
    rinduction l.
    - contradiction.
    - eapply In_rcons in Hel. destruct Hel.
      + subst a.
        specialize (rcons_destruct l0) as Hl0. destruct Hl0;[|destructH];subst l0.
        * cbn in *.
          inversion Hpath;subst;eapply postfix_hd_eq in Hpost;
            inversion Hpost;subst;cbn.
          -- econstructor;auto.
          -- clear. induction j;cbn;econstructor;auto. econstructor.
        * copy Hpost Hpost'.
          eapply postfix_path in Hpost;eauto.
          eapply path_nlrcons_edge in Hpost.
          destruct a.
          (* everything outside these brackets [ *)
          exploit' H.
          specialize (H t0 e).
          exploit H.
          1: { eapply postfix_step_left;eauto. }
          specialize (tcfg_edge_destruct Hpost) as Hdestr.
          assert (|j| <= |i|) as Hji.
          { specialize (HForall (p,i)). cbn in *. eapply HForall.
            eapply In_rcons;auto. }
          destruct Hdestr as [Hn|[He|[Hb|Hx]]]. all: subst;auto.
          -- assert (|j| < |0 :: i|) by (cbn;lia).
             inversion H.
             ++ exfalso. subst l0. rewrite <-H3 in H0. clear - H0.
                destruct j;cbn in *;lia.
             ++ subst. auto.
          -- destruct i.
             { destruct j.
               - cbn. econstructor.
               - cbn in Hji. lia.
             }
             destruct j. 1: { cbn. eapply prefix_nil. }
             cbn in *.
             assert (|j| < |n :: i|) by (cbn;lia).
             inversion H.
             ++ exfalso. subst l0. subst j. cbn in Hji. lia.
             ++ subst. econstructor. auto.
          -- eapply prefix_trans;eauto. clear; induction i;cbn;econstructor;eauto. econstructor.
          (* ] could be generalized, it is the same in this and the other geq_tag_suffix lemma *)
      + eapply H;eauto.
        * eapply postfix_step_left;eauto.
  Qed.

  Lemma while'_front_In (A : Type) (e : A -> A -> Prop) (P : decPred A) (l : list A) (a b : A)
        (Hpath : Path e a b l)
        (HP : P b)
    : b ∈ while' P l.
  Proof.
    destruct Hpath;cbn.
    - decide (P a);try contradiction. left. auto.
    - decide (P c);try contradiction. left. auto.
  Qed.

  Lemma ex_entry' (h p q : Lab) (i j : Tag) t
        (Hin : innermost_loop h q)
        (Hnin : ~ loop_contains h p)
        (Hpath : TPath (root,start_tag) (q,j) t)
        (Hord : (q,j) ≻* (p,i) | t)
    : (h,0 :: tl j) ≻* (p,i) | t.
  Proof.
    remember (while' (DecPred (fun xl => |j| <= |snd xl|)) t) as t'.
    assert (Postfix t' t) as Hpost.
    { eapply while'_postfix;subst t';eauto. }
    assert (forall xl, xl ∈ t' -> loop_contains h (fst xl)) as Hloop.
    { intros. destruct xl as [x l]. eapply geq_tag_suffix_deq in H.
      4: subst t'; eapply while'_Forall.
      all: cbn;eauto;destruct Hin as [Hin _];eauto.
    }
    inversion Hpost.
    - subst. eapply splinter_cons in Hord. eapply splinter_in in Hord.
      specialize (Hloop (p,i)).
      exploit Hloop.
      + rewrite H0; auto.
      + cbn in Hloop. contradiction.
    - subst l.
      specialize (rcons_destruct t') as Ht'.
      destruct Ht'. (* t' is not empty *)
      { enough ((q,j) ∈ t') as H00 by (rewrite H0 in H00;cbn in H00;contradiction).
        subst.
        eapply while'_front_In;eauto. cbn. lia. }
      destructH.
      destruct a0 as [h' k].
      eapply postfix_ex_cons in H. destructH. erewrite H1 in H.
      assert (h' = h); [|subst h'].
      { (*
         * h' is a header
         * it has an incoming edge from outside of h
         *)
        destruct a'.
        eapply entry_through_header;cycle 1.
        - destruct Hin as [Hin1 Hin2].
          enough (deq_loop h' h).
          { eapply H2. eapply loop_contains_self. eapply loop_contains_loop_head;auto. }
          eapply deq_loop_trans; eauto.
          + eapply geq_tag_suffix_deq. 2:eapply Hpost. all: eauto.
            * rewrite Heqt'. eapply while'_Forall.
            * rewrite H0. eapply In_rcons. left. auto.
          + eapply loop_contains_deq_loop;auto.
        - rewrite H0 in H.
          eapply postfix_path in H;eauto 1.
          instantiate (1:=e).
          eapply path_nlrcons_edge in H.
          unfold tcfg_edge in H. destructH. eauto.
        - eapply while'_max in H as H1';eauto. cbn in H1'. contradict H1'.
          eapply loop_contains_deq_loop in H1'.
          eapply innermost_eq_loop in Hin.
          rewrite Hin in H1'.
          eapply postfix_incl in H.
          eapply path_to_elem in Hpath as Hpath'.
          2: { eapply H. eapply In_rcons. left. reflexivity. }
          destructH.
          eapply deq_loop_le;cycle 1;eauto.
      }
      eapply while'_max in H as Hmax;[|eauto]. cbn in Hmax.
      destruct a'. cbn in *. assert (|l| < |j|) as Hmax' by lia.
      assert (|j| <= |k|) as Hjk.
      { assert ((h,k) ∈ t') by (rewrite H0;eapply In_rcons;eauto).
        rewrite Heqt' in H2.
        eapply while'_forall in H2. cbn in H2. auto. }
      assert (|l| < |k|) by lia.
      eapply tag_entry_lt in H2.
      + destruct j.
        { exfalso. cbn in Hmax'. lia. }
        assert (j = tl k).
        { replace j with (tl (n :: j)) by (cbn;auto). erewrite <-geq_tag_suffix_tag_tl_eq.
          - rewrite take_r_tl;eauto. cbn. rewrite H2. cbn. cbn in Hmax.
            rewrite H2 in Hjk. cbn in Hjk. lia.
          - eauto.
          - eapply Hpost.
          - subst t'. eapply while'_Forall.
          - rewrite H0. eapply In_rcons. left. eauto.
        }
        rewrite H2 in H3. cbn in H3. cbn. subst j k.
        clear - Hpost Heqt' H0 H H1 Hpath Hord Hin Hnin.
        eapply postfix_eq in Hpost. destructH.
        rewrite H1,Hpost.
        rewrite consAppend.
        eapply splinter_app; eapply splinter_single.
        * rewrite H0. eapply In_rcons. auto.
        * eapply splinter_cons in Hord. eapply splinter_in in Hord.
          rewrite Hpost in Hord. eapply in_app_or in Hord. destruct Hord;auto.
          exfalso.
          rewrite Heqt' in *.
          eapply geq_tag_suffix_deq in Hpath;cycle 1.
          -- eapply while'_postfix. symmetry. eauto.
          -- rewrite Heqt'. eapply while'_Forall.
          -- rewrite Heqt'. eauto.
          -- eapply Hnin. eapply Hpath. eapply Hin.
      + rewrite H0 in H. eapply postfix_path in H;eauto.
        cbn in H. eapply path_nlrcons_edge in H. eauto.
  Qed.

  Lemma ex_entry'' (h p q : Lab) (i j j' k : Tag) t
        (Hin : loop_contains h q)
        (Hnin : ~ loop_contains h p)
        (Hpath : TPath (p,i) (q,j) t)
        (Hleni : | i | = depth p)
        (Heq : j = j' ++ k)
        (Hlen : | k | = depth h - 1)
    : (h,0 :: k) ∈ t.
  Proof.
    revert j' j q Heq Hpath Hin.
    induction t;intros;inv_path Hpath.
    - contradiction.
    - destruct x as [u l].
      decide (loop_contains h u).
      + right.
        eapply tcfg_edge_destruct' in H0.
        destruct H0 as [[H0 H1]|[[H0 H1]|[[H0 H1]|[H0 H1]]]].
        * eapply IHt. all: cycle 1; eauto.
        * destruct j'.
          -- exfalso. admit.
          -- eapply IHt. all: cycle 1; eauto. cbn in H0. inversion H0. eauto.
        * destruct j'.
          -- admit.
          -- destruct l;cbn in H0;[congruence|].
             eapply IHt. all: cycle 1; eauto.
             instantiate (1:=(n0 :: j')). cbn. inv H0. reflexivity.
        * destruct l.
          -- admit.
          -- cbn in H0. eapply IHt. all: cycle 1; eauto. instantiate (1:=n :: j').
             cbn. rewrite H0. reflexivity.
      + eapply entry_through_header in Hin as Hin'. 2:eauto. 2: destruct H0;eauto.
        subst q.
        assert (entry_edge u h) as Hentry.
        { split. 1: eapply loop_contains_loop_head;eauto. split;destruct H0;eauto. }
        rewrite <-tag_entry_iff in Hentry;eauto.
        assert (| j' ++ k | = depth h) by admit.
        destruct j'.
        * exfalso.
          cbn in H1, Hentry. destruct k;[congruence|]. rewrite <-H1 in Hlen. cbn in Hlen. lia.
        * destruct j'.
          -- cbn in Hentry. inv Hentry. left. reflexivity.
          -- exfalso.
             rewrite <- H1 in Hlen. cbn in Hlen.
             rewrite app_length in Hlen. lia.
  Admitted.

    (* (tl (take_r (depth h) j)) *)
  Lemma ex_entry (h p q : Lab) (i j : Tag) t
        (Hin : innermost_loop h q)
        (Hnin : ~ loop_contains h p)
        (Hpath : TPath (p,i) (q,j) t)
    : (h,0 :: tl j) ∈ t.
  Proof.

  Admitted.

End cfg.

Section diadef.
  Context `{C : redCFG}.

  Infix "-->" := edge__P.
  Infix "-t>" := tcfg_edge (at level 70).
  Class DiamondPaths (s u1 u2 p1 p2 q1 q2 : Lab)
        (k i l1 l2 j1 j2 : Tag)
        (r1 r2 : list (Lab * Tag)) :=
    {
      Dsk1 : (s,k) -t> (u1,l1);
      Dsk2 : (s,k) -t> (u2,l2);
      Dpath1 : TPath (u1,l1) (p1,i) ((p1,i) :: r1);
      Dpath2 : TPath (u2,l2) (p2,i) ((p2,i) :: r2);
      Dqj1 : hd (s,k) r1 = (q1,j1);
      Dqj2 : hd (s,k) r2 = (q2,j2);
      Ddisj : Disjoint r1 r2;
      Dloop : eq_loop q1 q2;
      Dlen : | k | = depth s
    }.

  (* It is not possible to define TeqPaths for empty r1 or r2 in a meaningful way *)
  Class TeqPaths (u1 u2 q1 q2 : Lab)
        (l1 l2 j1 j2 : Tag)
        (r1 r2 : list (Lab * Tag)) :=
    {
      Tpath1 : TPath (u1,l1) (q1,j1) ((q1,j1) :: r1);
      Tpath2 : TPath (u2,l2) (q2,j2) ((q2,j2) :: r2);
      Tdisj : Disjoint ((q1,j1) :: r1) ((q2,j2) :: r2);
      Tloop : eq_loop q1 q2;
      Tjj_len : |j1| = |j2|;
                          Ttl_eq : tl j1 = tl j2;
      Tlj_eq1 : l1 = j1 \/ l1 = 0 :: j1;
      Tlj_eq2 : l2 = j1 \/ l2 = 0 :: j1 \/ loop_contains u2 q1;
      Tj_len : | j1 | = depth q1
    }.
End diadef.

Ltac diamond_subst_qj D :=
  lazymatch type of D with
  | DiamondPaths _ _ _ _ _ ?q1 ?q2 _ _ _ _ ?j1 ?j2 (?qj1 :: ?r1) _
    => replace qj1 with (q1,j1) in *;
      [clear qj1|destruct D;
                 lazymatch goal with
                 | Q : hd _ (qj1 :: _) = _ |- _ => cbn in Q; eauto
                 end
      ]
  | _ => idtac
  end;
  lazymatch type of D with
  | DiamondPaths _ _ _ _ _ ?q1 ?q2 _ _ _ _ ?j1 ?j2 _ (?qj2 :: ?r2)
    => replace qj2 with (q2,j2) in *;
      [clear qj2|destruct D;
                 lazymatch goal with
                 | Q : hd _ (qj2 :: _) = _ |- _ => cbn in Q; eauto
                 end
      ]
  | _ => idtac
  end.

Ltac inv_nil_Dpaths D :=
  let Q := fresh "Q" in
  lazymatch type of D with
  | DiamondPaths ?s _ _ _ _ ?q1 ?q2 ?k _ _ _ ?j1 ?j2 [] _
    => assert ((s,k) = (q1,j1)) as Q;
      [destruct D; lazymatch goal with
                   | H: hd (s,k) [] = (q1,j1) |- _
                     => cbn in H;auto
                   end
      |symmetry in Q;inv Q]
  | _ => idtac
  end;
  lazymatch type of D with
  | DiamondPaths ?s _ _ _ _ ?q1 ?q2 ?k _ _ _ ?j1 ?j2 _ []
    => assert ((s,k) = (q2,j2)) as Q;
      [destruct D; lazymatch goal with
                   | H: hd (s,k) [] = (q2,j2) |- _
                     => cbn in H;auto
                   end
      |symmetry in Q;inv Q]
  | _ => idtac
  end.

Ltac inv_Dpaths D := diamond_subst_qj D; inv_nil_Dpaths D.

Lemma DiamondPaths_sym `(C : redCFG) s u1 u2 p1 p2 q1 q2 k i l1 l2 j1 j2 r1 r2
      (D : DiamondPaths s u1 u2 p1 p2 q1 q2 k i l1 l2 j1 j2 r1 r2)
  : DiamondPaths s u2 u1 p2 p1 q2 q1 k i l2 l1 j2 j1 r2 r1.
Proof.
  destruct D.
  econstructor;eauto.
  - eapply Disjoint_sym;eauto.
  - symmetry. eauto.
Qed.

Lemma Dpath_uq1 `(D : DiamondPaths)
      (Hnnil : r1 <> nil)
  : TPath (u1,l1) (q1,j1) r1.
Proof.
  destruct r1.
  - contradiction.
  - inv_Dpaths D. destruct D. inv_path Dpath3. eauto.
Qed.

Lemma Dpath_uq2 `(D : DiamondPaths)
      (Hnnil : r2 <> nil)
  : TPath (u2,l2) (q2,j2) r2.
Proof.
  destruct r2.
  - contradiction.
  - inv_Dpaths D. destruct D. inv_path Dpath4. eauto.
Qed.

Lemma Dpath_sq1 `(D : DiamondPaths)
  : TPath (s,k) (q1,j1) (r1 ++ [(s,k)]).
Proof.
  destruct r1.
  - cbn. inv_Dpaths D. econstructor.
  - inv_Dpaths D.
    eapply path_rcons.
    + eapply Dpath_uq1;eauto. congruence.
    + eapply Dsk1.
Qed.

Lemma Dpath_sq2 `(D : DiamondPaths)
  : TPath (s,k) (q2,j2) (r2 ++ [(s,k)]).
Proof.
  eapply Dpath_sq1.
  eapply DiamondPaths_sym;eauto.
Qed.

Lemma j_len1 `(D : DiamondPaths)
  : | j1 | = depth q1.
Proof.
Admitted.

Lemma j_len2 `(D : DiamondPaths)
  : | j2 | = depth q2.
Proof.
  eapply j_len1; eauto using DiamondPaths_sym.
Qed.

Lemma jj_len `(D : DiamondPaths)
  : |j1| = |j2|.
Proof.
Admitted.

Lemma tl_eq `(D : DiamondPaths)
  : tl j1 = tl j2.
Admitted.

Section disj.

  Infix "-->" := edge__P.
  Infix "-t>" := tcfg_edge (at level 70).

  Context `(D : DiamondPaths).
  Hypothesis (Hjle : j1 ⊴ j2).

  Lemma s_deq_q
    : deq_loop s q1.
  Proof.
    clear Hjle.
    intros h Hh.
    eapply loop_contains_innermost in Hh as Hinner. destructH.
    eapply eq_loop_innermost in Hinner as Hinner'. 2: eapply Dloop.
    eapply innermost_loop_deq_loop;eauto. 2:eapply Dloop in Hh;auto.
    destruct r1, r2; inv_Dpaths D.
    1-3: lazymatch goal with
         | H : innermost_loop ?h' s |- _ => destruct H;eauto
         end.
    decide (loop_contains h' s);[assumption|exfalso].
    copy Hinner Hinner''.
    eapply Dpath_sq1 in D as Hsq1.
    eapply Dpath_sq2 in D as Hsq2.
    eapply ex_entry in Hinner;eauto.
    eapply ex_entry in Hinner';eauto.
    eapply tl_eq in D as Htl.
    rewrite Htl in Hinner.
    eapply In_rcons in Hinner.
    eapply In_rcons in Hinner'.
    destruct Hinner, Hinner'.
    1-3: lazymatch goal with
         | H: (?h', _ ) = (s,k) |- _ => inv H
         end;
      eapply n;destruct Hinner'';eauto using loop_contains_self.
    eapply Ddisj;eauto.
  Qed.

  Lemma r1_incl_head_q : forall x, x ∈ map fst r1 -> deq_loop x q1.
    clear Hjle.
  Admitted.

  Lemma u1_deq_q
        (Hnnil : r1 <> [])
    : deq_loop u1 q1.
  Proof.
    eapply r1_incl_head_q.
    destruct r1;[contradiction|].
    destruct D.
    inv_path Dpath3.
    eapply path_contains_back in H.
    fold (fst (u1,l1)).
    eapply in_map;eauto.
  Qed.

  Lemma r2_incl_head_q : forall x, x ∈ map fst r2 -> deq_loop x q1.
  Proof.
    clear Hjle.
  Admitted.

  Lemma u2_deq_q
        (Hnnil : r2 <> [])
    : deq_loop u2 q1.
  Proof.
    clear Hjle.
  Admitted.

  Lemma no_back : forall x : Lab, x ∈ (q1 :: map fst r1) -> ~ loop_contains x q1.
  Proof. (* Hjle needed *)
  Admitted.

  Lemma no_back2
        (Htageq : j1 = j2)
    : forall x : Lab, x ∈ (q2 :: map fst r2) -> ~ loop_contains x q1.
  Proof.
    clear Hjle.
  Admitted.

  Section disj_eqdep.
    Hypothesis (Hdeq : deq_loop q1 s).

    Lemma lj_eq1
      : l1 = j1 \/ l1 = 0 :: j1.
    Proof. (* Hjle needed *)
    Admitted.

    Lemma lj_eq2
      : l2 = j1 \/ l2 = 0 :: j1 \/ loop_contains u2 q1.
    Proof. (* Hjle needed *)
    Admitted.

  End disj_eqdep.

End disj.
