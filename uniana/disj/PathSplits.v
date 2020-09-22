Require Export LoopSplits SplitsSound.

Notation "pi -t> qj" := (tcfg_edge pi qj) (at level 50).
Lemma both_exit_or_teq `(C : redCFG) q1 q2 p j1 j2 i
      (Hedge1 : (q1,j1) -t> (p,i))
      (Hedge2 : (q2,j2) -t> (p,i))
  : exists h, exit_edge h q1 p /\ exit_edge h q2 p \/ j1 = j2 /\ deq_loop p q1.
Proof.
Admitted.

Lemma edge_edge_loop `(C : redCFG) q1 q2 p
      (Hedge1 : edge__P q1 p)
      (Hedge2 : edge__P q2 p)
  : eq_loop q1 q2.
Proof.
Admitted.

(** * Corollaries **)

Lemma hd_nnil (A : Type) (l : list A) a b
      (Hnnil : l <> nil)
  : hd a l = hd b l.
Proof.
  induction l;[contradiction|cbn;eauto].
Qed.

Theorem lc_join_split `{C : redCFG} t1 t2 (p q1 q2 s : Lab) (i j1 j2 k : Tag)
        (* it is important to cons qj's in front of the t's *)
        (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
        (Hneq : q1 <> q2)
        (Hpath1 : TPath (root,start_tag) (p,i) ((p,i) :: (q1,j1) :: t1))
        (Hpath2 : TPath (root,start_tag) (p,i) ((p,i) :: (q2,j2) :: t2))
  : s ∈ splitsT p.
Proof.
  eapply splitsT_spec.
  destruct Hlc.
  destructH.
  exists ((p,i) :: x), ((p,i) :: l2'),
  (fst (hd (p,i) (rev x))), (fst (hd (p,i) (rev l2'))), k, i,
  (snd (hd (p,i) (rev x))), (snd (hd (p,i) (rev l2'))).
  all: destruct x, l2'.
  all: inv_path Hpath1; eapply postfix_path in H0 as Hpath1';eauto.
  all: inv_path Hpath2; eapply postfix_path in H2 as Hpath2';eauto.
  all: cbn in H0,H2; eapply postfix_hd_eq in H0 as H0'; eapply postfix_hd_eq in H2 as H2'.
  all: tryif inv H0' then idtac else subst;
    tryif inv H2' then idtac else subst.
  1: contradiction.
  all: split_conj.
  7,14: eapply tag_depth';eauto.
  19: { admit. }
  3,9,15: eauto.
  1,5,7,10,15: cbn.
  1,3:econstructor.
  1,3: right;congruence.
  1: left;congruence.
  all: rewrite <-surjective_pairing.
  1,8: eapply PathCons with (b:=(q2,j2));eauto.
  5,8: eapply PathCons with (b:=(q1,j1));eauto.
  all: try (rewrite cons_rcons' in Hpath2';
            eapply path_rcons_rinv in Hpath2' as Hpath2'';
            eapply path_nlrcons_edge in Hpath2' as Hedge2;
            rewrite <-cons_rcons' in Hpath2'').
  all: try (rewrite cons_rcons' in Hpath1';
            eapply path_rcons_rinv in Hpath1' as Hpath1'';
            eapply path_nlrcons_edge in Hpath1' as Hedge1;
            rewrite <-cons_rcons' in Hpath1'').
  all: try (replace (hd (p, i) (rev ((q2, j2) :: l2'))) with (hd (q2, j2) (rev ((q2, j2) :: l2')));
            [|eapply hd_nnil;cbn;intro N;congruence']).
  all: try (replace (hd (p, i) (rev ((q1, j1) :: x))) with (hd (q1, j1) (rev ((q1, j1) :: x)));
            [|eapply hd_nnil;cbn;intro N;congruence']).
  all:now eauto.
Admitted.
