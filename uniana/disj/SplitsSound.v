Require Export Splits SplitsT.

Definition inner' := fun (A : Type) (l : list A) => rev (tl (rev (tl l))).

Lemma inner_inner' (A : Type) (l : list A)
  : inner l = inner' l.
Proof.
  unfold inner, inner'.
  destruct l;cbn;eauto.
  destr_r' l;subst l;cbn;eauto.
  rewrite rev_rcons. cbn.
  rewrite rev_involutive.
  rewrite rev_rcons. cbn.
  rewrite rev_involutive.
  reflexivity.
Qed.

Lemma inner_rtl (A : Type) (l : list A) (a : A)
  : inner (a :: l) = r_tl l.
Proof.
  rewrite inner_inner'.
  unfold inner',r_tl in *.
  cbn.
  reflexivity.
Qed.

Lemma inner_tl (A : Type) (l : list A) (a : A)
  : inner (l ++ [a]) = tl l.
Proof.
  unfold inner.
  rewrite rev_rcons.
  cbn.
  rewrite rev_involutive.
  reflexivity.
Qed.

Lemma inner_eval_lr (A : Type) (l : list A) (a b : A)
  : inner (a :: l ++ [b]) = l.
Proof.
  rewrite <-cons_rcons_assoc.
  rewrite inner_tl.
  cbn.
  reflexivity.
Qed.

Lemma r_tl_rcons (A : Type) (l : list A) (a : A)
  : r_tl (l ++ [a]) = l.
Proof.
  unfold r_tl.
  rewrite rev_rcons. cbn.
  rewrite rev_involutive.
  reflexivity.
Qed.

Lemma inner_empty_iff (A : Type) (l : list A) (a b : A)
  : inner (a :: b :: l) = [] <-> l = nil.
Proof.
  destruct l;cbn.
  - firstorder.
  - split;intro H;[|congruence].
    specialize (cons_rcons a0 l) as Hspec. destructH. rewrite Hspec in H.
    rewrite inner_rtl in H.
    rewrite <-cons_rcons_assoc in H.
    rewrite r_tl_rcons in H.
    congruence.
Qed.

Ltac path_simpl2' H :=
  let Q:= fresh "Q" in
  lazymatch type of H with
  | Path ?e ?x ?y (?z :: ?π) =>
    replace y with z in *; [ | symmetry;eapply path_front;eauto ]
  | Path ?e ?x ?y (?π ++ [?z]) => replace x with z in *; [ | symmetry;eapply path_back; eauto ]
  end.

Ltac inv_path H :=
  try path_simpl' H;
  let x := fresh "x" in
  inversion H as [ | ? x ]; subst;
  match goal with
  | Q : Path _ _ x _ |- _ => path_simpl2' Q
  | Q : Path _ _ _ [] |- _ => inversion Q
  | |- _ => idtac
  end.

Lemma path_acyclic_no_loop (L : Type) (e : L -> L -> Prop) (a b c : L) (π : list L)
      (Hacy : acyclic e)
  : ~ Path e a a (b :: c :: π).
Proof.
  intro N.
  inv_path N.
  eapply Hacy;eauto.
Qed.

Lemma path_single (L : Type) (e : L -> L -> Prop) (a b c : L)
      (Hpath : Path e a b [c])
  : a = b /\ b = c.
Proof.
  inversion Hpath.
  - subst; eauto.
  - inversion H3.
Qed.

Section splits_sound.

  Context `{C : redCFG}.

  Infix "-->" := edge__P.
  Infix "-t>" := tcfg_edge (at level 70).

  Lemma tcfg_acyclic
    : acyclic tcfg_edge.
    (* FIXME: tcfg_edge is NOT acyclic (although *rooted* TPaths are) *)
  Admitted.

  Lemma tcfg_edge_edge (q p : Lab) (i j : Tag)
        (Hedge : (q,j) -t> (p,i))
    : q --> p.
  Admitted.

  Hint Resolve tcfg_edge_edge : tcfg.

  Lemma inhom_loop_exits (s u1 u2 q1 q2 e1 e2 : Lab) r1 r2 (k i l1 l2 : Tag) (n1 n2 : nat)
        (Hsk1 : (s,k) -t> (u1,l1))
        (Hsk2 : (s,k) -t> (u2,l2))
        (Hpath1 : TPath (u1,l1) (e1,i) ((e1,i) :: r1))
        (Hpath2 : TPath (u2,l2) (e2,i) ((e2,i) :: r2))
        (Hei1 : hd (s,k) r1 = (q1,n1 :: i))
        (Hei2 : hd (s,k) r2 = (q2,n2 :: i))
        (Hdisj : Disjoint r1 r2)
        (Hloop : eq_loop q1 q2)
    : exists r1' r2', edge__P s u1 /\  edge__P s u2
                 /\ HPath u1 e1 (e1 :: r1') /\ HPath u2 e2 (e2 :: r2')
                 /\ Disjoint r1' r2'.
  Proof.
  Admitted.

  Definition nexit_edge q p := forall h, ~ exit_edge h q p.

  Lemma two_edge_exit_cases (q1 q2 p : Lab)
        (Hedge1 : q1 --> p)
        (Hedge2 : q2 --> p)
    : (exists h, exit_edge h q1 p /\ exit_edge h q2 p)
      \/ nexit_edge q1 p /\ nexit_edge q2 p.
  Proof.
  Admitted.

  Lemma nexit_injective q1 q2 p1 p2 j1 j2 i
        (Hedge1 : (q1,j1) -t> (p1,i))
        (Hedge2 : (q2,j2) -t> (p2,i))
        (Hnexit1 : nexit_edge q1 p1)
    : j1 = j2.
  Admitted.

  Lemma expand_hpath (π : list Lab) q p
        (Hπ : HPath q p π)
    : exists ϕ, CPath q p ϕ /\ π ⊆ ϕ.
  Proof.
    induction Hπ.
    - exists [a]. split; [ constructor | auto ].
    - unfold head_rewired_edge in H.
      destruct H as [ [ H _ ] | H ].
      + destruct IHHπ as [ ϕ [ Hϕ Hsub ]].
        exists (c :: ϕ). split.
        * econstructor; eassumption.
        * unfold incl in *. firstorder.
      + unfold exited in H.
        unfold exit_edge in H.
        destruct H as [p [Hcont [Hncont Hedge]]].
        eapply loop_reachs_member in Hcont.
        destruct Hcont as [σ Hσ].
        destruct IHHπ as [ϕ [Hϕ Hincl]].
        exists (c :: σ ++ tl ϕ).
        split.
        * econstructor.
          -- eapply path_app'. eassumption.
             eauto using subgraph_path'.
          -- eassumption.
        * unfold incl in *. intros.
          destruct H.
          -- subst. eauto.
          -- eapply Hincl in H. simpl. right.
             eapply in_or_app.
             destruct ϕ; [ inversion H |].
             eapply in_inv in H.
             destruct H.
             ++ left. subst. inv Hϕ; eauto using path_contains_back.
             ++ right. eauto.
  Qed.

  Lemma contract_cpath (π : list Lab) q p
           (Hπ : CPath p q π)
           (Hdeq : deq_loop p q)
           (Hnin : forall x, x ∈ tl π -> ~ loop_contains x q)
    : exists ϕ, HPath p q ϕ /\ ϕ ⊆ π.
  Admitted.

  Ltac spot_path := admit.

  Lemma tag_exit_eq' h p q i j
        (Hedge : (p,i) -t> (q,j))
        (Hexit : exit_edge h p q)
    : exists n, i = n :: j.
  Admitted.

  Lemma acyclic_path_NoDup (L : Type) `{EqDec L eq} (ed : L -> L -> Prop) (π : list L) p q
        (Hpath : Path ed p q π)
        (Hacy : acyclic ed)
    : NoDup π.
  Proof.
    induction Hpath.
    - econstructor;eauto. econstructor.
    - econstructor;eauto.
      intro N.
      eapply path_from_elem in N;eauto.
      destructH.
      eapply Hacy;eauto.
  Qed.
  Lemma acy_path_incl_cons (L : Type) `{EqDec L eq} (ed : L -> L -> Prop) (π ϕ : list L) p q
        (Hpath : Path ed p q π)
        (Hincl : π ⊆ (q :: ϕ))
        (Hacy : acyclic ed)
    : tl π ⊆ ϕ.
  Proof.
    inv_path Hpath;cbn;eauto.
    unfold incl in *.
    intros a Ha.
    specialize (Hincl a). exploit Hincl.
    destruct Hincl;subst.
    - eapply acyclic_path_NoDup in Hpath;eauto.
      inv Hpath. contradiction.
    - auto.
  Qed.

  Theorem splits_sound p
    : splitsT p ⊆ splits p.
  Proof.
    intros s Hin.
    eapply splitsT_spec in Hin.
    destructH.
    (* contradict π and ϕ (the paths from (u,l) to (p,i)) being empty *)
    destruct π as [|pi1 r1]; destruct ϕ as [|pi2 r2]; cbn in Hin1, Hin6.
    1: tauto.
    1: inversion Hin0.
    1: inversion Hin2.
    unfold TPath in Hin0. path_simpl' Hin0.
    unfold TPath in Hin2. path_simpl' Hin2.
    eapply edge_path_hd_edge in Hin0 as Hqp1;eauto.
    eapply edge_path_hd_edge in Hin2 as Hqp2;eauto.
    destruct r1 as [|[q1 j1] r1]; destruct r2 as [|[q2 j2] r2];
        unfold hd in Hqp1,Hqp2.
    - tauto.
    - eapply splits_spec. admit. (* I need a lemma for these symmetric cases,
                                      only one Hpath is non-trivial (use contraction) *)
    - admit.
    - specialize (@two_edge_exit_cases q1 q2 p) as Hcase.
      exploit Hcase.
      1,2: eapply edge_path_hd_edge;eauto with tcfg; spot_path.
      destruct Hcase.
      + destructH.
        eapply tag_exit_eq' in H0 as Hn1. destruct Hn1 as [n1 Hn1];eauto.
        eapply tag_exit_eq' in H1 as Hn2. destruct Hn2 as [n2 Hn2];eauto.
        eapply inhom_loop_exits in Hin2 as Hinhom.
        4: eapply Hin0.
        all: eauto.
        2,3: rewrite hd_map_fst_snd; eapply pair_equal_spec;split;eauto.
        2: {
          eapply eq_loop_exiting in H0; eapply eq_loop_exiting in H1.
          cbn. rewrite <-H0, <-H1; reflexivity.
        }
        destructH.
        eapply splits_spec.
        exists (p :: r1'), (p :: r2'), u1, u2.
        split_conj;eauto. cbn.
        destruct r1';[|left;congruence].
        destruct r2';[|right;congruence].
        exfalso.
        inv_path Hinhom1. inv_path Hinhom3.
        eapply tcfg_edge_det in Hin3;eauto. subst l2.
        inv_path Hin0. inv_path Hin2.
        eapply Hin1.
        1,2: eapply path_contains_back;eauto.
      + destructH.
        eapply nexit_injective in H0;eauto.
        rewrite <-H0 in *.
        decide (deq_loop q1 s).
        * (* this is given by lemma 4.13 *)
          assert (Disjoint (q1 :: map fst r1) (q2 :: map fst r2)) as Hdisj by admit.
          subst j2.
          inv_path Hin0. inv_path Hin2.
          eapply splits_spec.
          eapply TPath_CPath in H.  cbn in H.
          eapply TPath_CPath in H2. cbn in H2.
          eapply contract_cpath in H.
          eapply contract_cpath in H2.
          2,4: admit. (* r1 ⊆ h_q *)
          2,3: admit. (* r1 ⊆ h_q & no back edge *)
          repeat destructH.
          exists (p :: ϕ0), (p :: ϕ), u1, u2.
          split_conj;eauto.
          1,2: econstructor;eauto;unfold head_rewired_edge;left;split;destruct Hqp1,Hqp2;eauto.
          1,2: admit. (* contradiction to eq_loop q1 q2 and no back edges *)
          2,3: destruct Hin3,Hin4;eauto.
          2: cbn;inv_path H2;cbn;left;congruence.
          cbn.
          eapply disjoint_subset;eauto.
        * assert (exists e1 r1', Path tcfg_edge (u1, l1) (e1, j1) ((e1,j1) :: r1')) as [e1 [r1' He1]]
              by admit.
          assert(Prefix ((e1,j1) :: r1') ((q1,j1) :: r1)) as Hpre1 by admit.
          assert (exists e2 r2', Path tcfg_edge (u2, l2) (e2, j1) ((e2,j1) :: r2')) as [e2 [r2' He2]]
              by admit.
          assert(Prefix ((e2,j1) :: r2') ((q2,j1) :: r2)) as Hpre2 by admit.
          eapply inhom_loop_exits in He2 as Hinhom.
          4: eapply He1.
          all:eauto.
          2,3,5: admit. (* because exit edges given by cnc stuff *)
          2: {
            eapply disjoint_subset. 1,2: eapply prefix_incl;eapply prefix_cons;eauto.
            eauto.
          }
          eapply splits_spec.
          destructH.
          (* contract paths from e1 & e2 to p (they're on the same level)
           * append these to r1'0 & r2'0, et voila there the disjoint head rewired paths (using 4.13)
           * side conditions are also easy
           *)
          admit.
  Admitted.

End splits_sound.
