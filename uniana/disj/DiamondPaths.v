Require Export TcfgqMonotone Disjoint.
Require Import MaxPreSuffix Lia.

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

End cfg.

Section diadef.
  Context `{C : redCFG}.

  Infix "-->" := edge__P.
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

Hint Immediate DiamondPaths_sym : diamond.

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

Hint Resolve Dsk1 Dsk2 Dpath1 Dpath2 Dqj1 Dqj2 Ddisj Dloop Dlen : diamond.
Hint Resolve Dpath_uq1 Dpath_uq2 Dpath_sq1 Dpath_sq2 : diamond.

Lemma u_len1 `(D : DiamondPaths)
  : | l1 | = depth u1.
Proof.
  rewrite <-tcfg_edge_depth_iff.
  all:eauto with diamond.
Qed.

Lemma u_len2 `(D : DiamondPaths)
  : | l2 | = depth u2.
Proof.
  rewrite <-tcfg_edge_depth_iff.
  all:eauto with diamond.
Qed.

Hint Resolve u_len1 u_len2 : diamond.

Lemma j_len1 `(D : DiamondPaths)
  : | j1 | = depth q1.
Proof.
  destruct r1.
  - inv D. cbn in Dqj3. inv Dqj3. assumption.
  - assert (p :: r1 <> nil) by congruence.
    eapply tag_depth_unroot; eauto with diamond.
Qed.

Lemma j_len2 `(D : DiamondPaths)
  : | j2 | = depth q2.
Proof.
  eapply j_len1; eauto using DiamondPaths_sym.
Qed.

Lemma i_len1 `(D : DiamondPaths)
  : | i | = depth p1.
Proof.
  destruct D.
  inv_path Dpath3.
  - eapply u_len1. econstructor;eauto.
  - assert ((p1,i) :: r1 <> nil) by congruence.
    eapply tag_depth_unroot;eauto with diamond.
    eapply u_len1. econstructor;eauto.
Qed.

Lemma i_len2 `(D : DiamondPaths)
  : | i | = depth p2.
Proof.
  eapply DiamondPaths_sym in D.
  eapply i_len1;eauto.
Qed.

Lemma jj_len `(D : DiamondPaths)
  : |j1| = |j2|.
Proof.
  erewrite j_len1. 2:eapply D.
  erewrite j_len2. 2:eapply D.
  rewrite Dloop. reflexivity.
Qed.


Lemma edge_qp1 `(D : DiamondPaths)
  : (q1,j1) -t> (p1,i).
Proof.
  destruct D.
  inv_path Dpath3;[cbn in Dqj3;inv Dqj3|].
  all:inv_path Dpath4;[cbn in Dqj4;inv Dqj4|].
  1: eassumption.
  1:destruct r2;[inv H|path_simpl2' H];cbn in Dqj4.
  2,3: destruct r1;[inv H|path_simpl2' H];cbn in Dqj3.
  3:destruct r2;[inv H1|path_simpl2' H1];cbn in Dqj4.
  all: subst p;eassumption.
Qed.

Lemma edge_qp2 `(D : DiamondPaths)
  : (q2,j2) -t> (p2,i).
Proof.
  eapply edge_qp1.
  eauto with diamond.
Qed.

Lemma tl_eq `(D : DiamondPaths)
  : tl j1 = tl j2.
Proof.
  eapply edge_qp1 in D as Hqp1.
  eapply edge_qp2 in D as Hqp2.
  eapply tcfg_edge_destruct' in Hqp1.
  eapply tcfg_edge_destruct' in Hqp2.
  eapply j_len1 in D as Hlen1.
  eapply j_len2 in D as Hlen2.
  eapply jj_len in D as Hlenjj.
  eapply i_len1 in D as Hleni1.
  eapply i_len2 in D as Hleni2.
  destruct Hqp1 as [Hqp1|[Hqp1|[Hqp1|Hqp1]]].
  all: destruct Hqp2 as [Hqp2|[Hqp2|[Hqp2|Hqp2]]].
  all: destruct Hqp1 as [Htag1 Hedge1].
  all: destruct Hqp2 as [Htag2 Hedge2].
  all: match goal with
       | H : eexit_edge _ _, Q : eexit_edge _ _ |- _
         => rewrite <- Htag1, <- Htag2;reflexivity
       | H : entry_edge _ _, Q : entry_edge _ _ |- _
         => destruct i;[congruence|];inv Htag1;inv Htag2;reflexivity
       | H : entry_edge _ _ |- _
         => exfalso;subst i;eapply f_equal with (f:=@length nat) in Htag2
       | H : eexit_edge _ _ |- _
         => exfalso;subst i;eapply f_equal with (f:=@length nat) in Htag2
       | _ => subst i
       end.
  all:destruct j1,j2;cbn in *;eauto;try congruence.
  all:try lia.
  all: match goal with
       | H : eexit_edge _ _ |- _
         => eapply depth_exit in H;lia
       end.
Qed.

Section disj.

  Infix "-->" := edge__P.

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
    eapply ex_entry_innermost in Hinner;eauto.
    2: eapply Dlen.
    eapply ex_entry_innermost in Hinner';eauto.
    2: eapply Dlen.
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

  Lemma tag_eq_take_r
    : forall h q' k', (q',k') ∈ r1 -> deq_loop q' h -> deq_loop s h -> take_r (depth h) k' = take_r (depth h) k.
  Proof.
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

Lemma diamond_teq `(C : redCFG)
      (s u1 u2 p1 p2 q1 q2 : Lab) (k i l1 l2 j1 j2 : Tag) r1 r2
      (Hdeq : deq_loop q1 s)
      (Hjle : j1 ⊴ j2)
      (D : DiamondPaths s u1 u2 p1 p2 q1 q2 k i l1 l2 j1 j2 ((q1,j1) :: r1) ((q2,j2) :: r2))
  : TeqPaths u1 u2 q1 q2 l1 l2 j1 j2 (r1) (r2).
Proof.
  copy D D'.
  destruct D.
  inv_path Dpath3. inv_path Dpath4.
  econstructor; eauto using tl_eq, lj_eq1, lj_eq2, jj_len, j_len1.
Qed.

Lemma diamond_qj_eq1 `(C : redCFG) s u1 u2 p1 p2 q1 q2 k i l1 l2 j1 j2 qj1 r1 r2
      (D : DiamondPaths s u1 u2 p1 p2 q1 q2 k i l1 l2 j1 j2 (qj1 :: r1) r2)
  : qj1 = (q1,j1).
Proof.
  destruct D. cbn in Dqj3. auto.
Qed.

Lemma diamond_qj_eq2 `(C : redCFG) s u1 u2 p1 p2 q1 q2 k i l1 l2 j1 j2 qj2 r1 r2
      (D : DiamondPaths s u1 u2 p1 p2 q1 q2 k i l1 l2 j1 j2 r1 (qj2 :: r2))
  : qj2 = (q2,j2).
Proof.
  destruct D. cbn in Dqj4. auto.
Qed.
