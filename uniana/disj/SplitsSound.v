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
        (Hnnil : r1 <> [] \/ r2 <> [])
        (Hloop : eq_loop q1 q2)
    : exists r1' r2', edge__P s u1 /\  edge__P s u2
                 /\ HPath u1 e1 (e1 :: r1') /\ HPath u2 e2 (e2 :: r2')
                 /\ Disjoint r1' r2' /\ (r1' <> [] \/ r2' <> []).
  Proof.
  Admitted.

  Lemma two_edge_exit_cases (q1 q2 p : Lab)
        (Hedge1 : q1 --> p)
        (Hedge2 : q2 --> p)
    : (exists h, exit_edge h q1 p /\ exit_edge h q2 p)
      \/ (forall h, ~ exit_edge h q1 p) /\ (forall h, ~ exit_edge h q2 p).
  Proof.
  Admitted.

  Lemma expand_hpath (π : list Lab) q p
        (Hπ : HPath q p π)
    : exists ϕ, CPath q p ϕ /\ π ⊆ ϕ.
  Admitted.

  Lemma contract_cpath (π : list Lab) q p
           (Hπ : CPath q p π)
           (Hdeq : deq_loop p q)
           (Hnin : forall x, x ∈ tl π -> ~ innermost_loop x q)
    : exists ϕ, HPath q p ϕ /\ ϕ ⊆ π.
  Admitted.

  Ltac spot_path := admit.

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
    Lemma hd_map_fst_snd (A B : Type) (a : A) (b : B) (l : list (A * B))
      : hd (a,b) l = (hd a (map fst l), hd b (map snd l)).
    Proof.
      destruct l;cbn;eauto using surjective_pairing.
    Qed.
    Lemma edge_path_hd_edge (L : Type) (ed : L -> L -> Prop) x y z π
          (Hedge : ed z x)
          (Hpath : Path ed x y (y :: π))
      : ed (hd z π) y.
    Admitted.
    eapply edge_path_hd_edge in Hin0 as Hqp1;eauto.
    eapply edge_path_hd_edge in Hin2 as Hqp2;eauto.
    rewrite hd_map_fst_snd in Hqp1, Hqp2.
    specialize (@two_edge_exit_cases (hd s (map fst r1)) (hd s (map fst r2)) p) as Hcase.
    exploit Hcase.
    1,2: eapply edge_path_hd_edge;eauto with tcfg; spot_path.
    destruct Hcase.
    - destructH.
      eapply inhom_loop_exits in Hin2 as Hinhom.
      4: eapply Hin0.
      all: eauto.
      2,3: rewrite hd_map_fst_snd; eapply pair_equal_spec;split;eauto.
      2,3,4: admit. (* using exit_edge we can show tail of tag is i & and same loop *)
      destructH.
      eapply splits_spec.
      exists (p :: r1'), (p :: r2'), u1, u2.
      split_conj;eauto.
    - admit.

  Admitted.

End splits_sound.
