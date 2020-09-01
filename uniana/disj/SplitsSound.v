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

  Lemma incl_app c
        (π ϕ : list Lab)
        (Hincl : π ⊆ ϕ)
    : (c :: π) ⊆ (c :: ϕ).
  Proof.
    unfold incl in *. firstorder.
  Qed.
    
  Lemma basic_edge_loop_contains a b x
        (Hedge : basic_edge a b)
        (Hinner : loop_contains x a)
    : loop_contains x b.
  Proof.
    specialize (loop_contains_loop_head Hinner) as Hhead.
    destruct Hedge as [Hedge _].
    eauto using loop_contains_deq_loop, back_edge_eq_loop, deq_loop_head_loop_contains, eq_loop1.
  Qed.

  Lemma back_edge_loop_contains a b x
        (Hedge : back_edge a b)
        (Hinner : loop_contains x a)
    : loop_contains x b.
  Proof.
    specialize (loop_contains_loop_head Hinner) as Hhead.
    eauto using loop_contains_deq_loop, back_edge_eq_loop, deq_loop_head_loop_contains, eq_loop1.
  Qed.

  Lemma back_edge_innermost h l
        (Hbe : back_edge l h)
    : innermost_loop h l.
  Proof.
    destruct (back_edge_eq_loop Hbe) as [H1 H2].
    unfold innermost_loop.
    eauto using loop_contains_ledge.
  Qed.

  Lemma innermost_unique a b c
        (Ha : innermost_loop a c)
        (Hb : innermost_loop b c)
    : a = b.
  Proof.
    destruct Ha as [Ha Ha'].
    destruct Hb as [Hb Hb'].
    unfold deq_loop in *.
    eauto using loop_contains_Antisymmetric.
  Qed.

  Lemma back_edge_src_no_loop_head
        a b
        (Hbe : back_edge b a)
    : ~ loop_head b.
  Proof.
    intro. eapply no_self_loops.
    - eapply Hbe.
    - eapply innermost_unique. unfold innermost_loop. unfold deq_loop.
      eauto using loop_contains_self.
      eauto using back_edge_innermost.
  Qed.

  Lemma deq_loop_entry_not_deq_loop
        a b c
        (Hdeq : deq_loop a b)
        (Hentry : entry_edge b c)
    : ~ deq_loop a c.
  Proof.
  Admitted.

  Lemma in_path_ex_prefix_not_in p q π x
        (Hπ : CPath p q π)
        (Hin : x ∈ π)
        : exists ϕ, Prefix (x :: ϕ) π /\ x ∉ ϕ.
  Proof.
    revert dependent q.
    induction π.
    - inv Hin.
    - intros.
      replace a with q in *.
      + decide (x ∈ π).
        * destruct π; [ inv i |].
          destruct (IHπ i e) as [ϕ [Hpre Hnin]].
          -- inv Hπ. enough (b = e).
             ++ subst. eassumption.
             ++ eauto using path_front.
          -- exists ϕ. split; [| eassumption ].
             econstructor. eassumption.
        * inv Hin.
          -- exists π. split; [ econstructor | eassumption ].
          -- contradiction.
      + eauto using path_front.
  Qed.

  Lemma prefix_singleton p q π h
        (Hπ : CPath p q π)
        (Hpre : Prefix [h] π)
    : p = h.
  Proof.
    induction Hπ.
    - inv Hpre.
      + reflexivity.
      + inv H1.
    - inv Hpre.
      + inv Hπ.
      + eauto.
  Qed.

  Lemma head_unique h b x y
        (Hh : loop_contains h x)
        (Hb : loop_contains b y)
        (Heq : eq_loop h b)
    : h = b.
  Proof.
    unfold eq_loop in Heq.
    unfold deq_loop in *.
    destruct Heq as [H1 H2].
    eapply loop_contains_Antisymmetric; eauto using loop_contains_loop_head, loop_contains_self.
  Qed.

  Lemma prefix_edge_exists a b p q π ϕ
        (Hπ : Path edge__P p q π)
        (Hpre : Prefix (a :: b :: ϕ) π)
    : b --> a.
  Proof.
    induction Hπ.
    - inv Hpre. inv H1.
    - inversion Hpre; [| eauto ].
      subst. inv Hπ; eauto.
  Qed.

  Lemma contract_cpath (π : list Lab) p q
           (Hπ : CPath p q π)
           (Hdeq : forall x, x ∈ π -> deq_loop p x)
           (Hnin : forall x, x ∈ tl π -> ~ loop_contains x q) (* Header of q is not on π *)
    : exists ϕ, HPath p q ϕ /\ ϕ ⊆ π.
  Proof.
    revert dependent q. revert dependent π.
    specialize (well_founded_ind (R:=(@StrictPrefix' Lab)) (@StrictPrefix_well_founded Lab)
                                 (fun π : list Lab => (forall x, x ∈ π -> deq_loop p x) ->
                                                   forall q, CPath p q π ->
                                                        (forall x, x ∈ tl π -> ~ loop_contains x q) ->
                                                        exists ϕ, HPath p q ϕ /\ ϕ ⊆ π))
      as WFind.
    eapply WFind.
    intros π IH Hdeq q Hπ Hnin. clear WFind.
    inv Hπ.
    - exists [q]. unfold incl. split; eauto; econstructor.
    - specialize (edge_Edge H0) as Hedge.
      rename H into Hπ. rename q into c. rename π0 into π.
      assert (Hprefix : StrictPrefix' π (c :: π)) by (repeat econstructor).
      simpl in Hnin.
      inv Hedge.
      + edestruct IH as [ϕ [Hϕ Hincl]]; try eauto.
        * intros. intro. eapply Hnin. simpl. eapply in_tl_in. eassumption.
          eauto using basic_edge_loop_contains. 
        * exists (c :: ϕ). split; [| eauto using incl_app ].
          econstructor; [ eassumption |].
          left. split; [ eassumption |].
          intro.  eapply (Hnin b). eauto using path_contains_front.
          eauto using loop_contains_self, basic_edge_loop_contains. 
      + edestruct IH as [ϕ [Hϕ Hincl]]; try eauto. 
        * intros. intro. eapply Hnin. simpl. eapply in_tl_in. eassumption.
          eauto using back_edge_loop_contains.
        * exists (c :: ϕ). split; [| eauto using incl_app ].
          econstructor; [ eassumption |].
          left. split; eauto using back_edge_src_no_loop_head.
      + edestruct IH as [ϕ [Hϕ Hincl]]; try eauto. clear IH.
        * intros. intro. eapply Hnin; try eauto using in_tl_in.
          eapply deq_loop_entry in H. unfold deq_loop in H. eauto.
        * decide (loop_head b).
          -- exfalso. apply (Hnin b).
             ++ simpl. eapply path_contains_front; eassumption.
             ++ eauto using deq_loop_entry, deq_loop_head_loop_contains.
          -- exists (c :: ϕ). split; try eauto using incl_app.
             econstructor; [ eassumption |]. left. eauto.
      + destruct H as [h Hexit]. 
        decide (h ∈ π) as [ Hhin | Hhnin ].
        * specialize (in_path_ex_prefix_not_in Hπ Hhin) as Hfirst.
          destruct Hfirst as [ϕ [Hpre Hninϕ]].
          destruct ϕ as [ | e ϕ ].
          -- assert (Heq : p = h) by (eauto using prefix_singleton).
             subst p. exists [c; h]. split.
             ++ econstructor; [ econstructor |]. right. exists b. eassumption.
             ++ unfold incl. intros. inversion H.
                ** subst. eauto.
                ** inversion H1. subst. eauto. inversion H2.
          -- assert (Hedge : e --> h) by (eauto using prefix_edge_exists).

             assert (Hback : back_edge e h). {
               eapply edge_Edge in Hedge.
               inv Hedge.
               - exfalso. eapply basic_edge_no_loop2. eapply H.
                 eapply loop_contains_loop_head. eapply Hexit.
               - assumption.
               - enough (deq_loop p e).
                 + exfalso. eapply deq_loop_entry_not_deq_loop.
                   2: eapply H. eassumption.
                   1: eauto using deq_loop_trans, deq_loop_exited'.
                 + eauto using in_prefix_in.
               - destruct H as [h' H]. eapply no_exit_head in H.
                 exfalso. apply H. unfold loop_contains in Hexit. unfold loop_head. firstorder.
             }

             assert (Hnin2 : forall x, x ∈ (e :: ϕ) -> ~ loop_contains x e). {
               intros. intro. eapply Hnin. eapply in_prefix_in.
               2: eapply Hpre.
               1: eapply in_cons. eassumption.
               specialize (back_edge_innermost Hback) as Hinner1.
               decide (deq_loop x e).
               - exfalso. enough (Hinner2 : innermost_loop x e).
                 + specialize (innermost_unique Hinner1 Hinner2) as Heq. subst. firstorder.
                 + unfold innermost_loop. eauto.
               - enough (x <> h).
                 + eapply exit_edge_in_loop; try eassumption. eauto using back_edge_loop_contains.
                 + intro. subst. firstorder.
             }

            edestruct (@IH (e :: ϕ)) as [ϕ' [Hϕ' Hincl']].
             ++ econstructor. eapply PreStep. eassumption.
             ++ intros. eapply Hdeq. eapply in_cons. eauto using in_prefix_in.
             ++ eapply prefix_cons in Hpre. eapply path_prefix_path; try eassumption.
                admit. (* requires decidable edges; not sure how to bring this here. *)
             ++ eauto.
             ++ exists (c :: h :: ϕ'). split.
                ** econstructor. econstructor. eapply Hϕ'.
                   --- left. split; [ eauto |].
                       decide (loop_head e); [| eassumption ]. exfalso.
                       eapply (Hnin2 e); eauto using loop_contains_self.
                   --- right. exists b. eassumption.
        * edestruct (IH π) as [ϕ [Hϕ Hincl]].
          -- econstructor. econstructor.
          -- eauto.
          -- eassumption.
          -- intros. intro. eapply Hnin. simpl. eapply in_tl_in. eassumption.
             edestruct (deq_loop_exit_or Hexit); try eassumption. 
             subst. exfalso. eauto using in_tl_in. 
          -- exists (c :: ϕ). split; [| eauto using incl_app ].
             econstructor; [ eassumption |]. left. split; [ assumption |]. intro.
             enough (h = b).
             ++ subst b. eauto using path_contains_front.
             ++ assert (Heq : eq_loop h b) by (eauto using eq_loop_exiting).
                assert (Hinner : innermost_loop h b) by (eauto using exit_edge_innermost).
                eapply loop_contains_self in H.
                destruct Hinner as [Hinner _].
                eauto using head_unique.
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
