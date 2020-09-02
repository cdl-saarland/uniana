Require Export Tagged Disjoint.


Ltac path_simpl2' H :=
  let Q:= fresh "Q" in
  lazymatch type of H with
  | Path ?e ?x ?y (?z :: ?π) =>
    replace y with z in *; [ | symmetry;eapply path_front;eauto ];
                              match type of H with
                              | Path _ _ _ (?w :: [])
                                => fold ([] ++ [w]) in H;
                                  path_simpl' H;
                                  unfold app in H
                              | Path _ _ _ (?w :: ?z :: [])
                                => fold ([w] ++ [z]) in H;
                                  path_simpl' H;
                                  unfold app in H
                              | _ => idtac
                              end
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


Section disj.
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
      Dloop : eq_loop q1 q2
    }.

  Class TeqPaths (u1 u2 q1 q2 : Lab)
        (l1 l2 j1 j2 : Tag)
        (r1 r2 : list (Lab * Tag)) :=
    {
      Tpath1 : TPath (u1,l1) (q1,j1) ((q1,j1) :: r1);
      Tpath2 : TPath (u2,l2) (q2,j2) ((q2,j2) :: r2);
      Tdisj : Disjoint ((q1,j1) :: r1) ((q2,j2) :: r2);
      Tloop : eq_loop q1 q2;
      Ttl_eq : tl j1 = tl j2;
      Tlj_eq1 : l1 = j1 \/ l1 = 0 :: j1;
      Tlj_eq2 : l2 = j1 \/ l2 = 0 :: j1 \/ loop_contains u2 q1
    }.

  Context `(D : DiamondPaths).

  Lemma s_deq_q
    : deq_loop s q1.
  Proof.
  Admitted.

  Lemma r1_incl_head_q : forall x, x ∈ map fst r1 -> deq_loop x q1.
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
  Admitted.

  Lemma u2_deq_q
        (Hnnil : r2 <> [])
    : deq_loop u2 q1.
  Proof.
  Admitted.

  Lemma no_back : forall x : Lab, x ∈ (q1 :: map fst r1) -> ~ loop_contains x q1.
  Admitted.

  Lemma no_back2
        (Htageq : j1 = j2)
    : forall x : Lab, x ∈ (q2 :: map fst r2) -> ~ loop_contains x q1.
  Admitted.

  Section disj_eqdep.
    Hypothesis (Hdeq : deq_loop q1 s).

    Lemma tl_eq
      : tl j1 = tl j2.
    Admitted.

    Lemma lj_eq1
      : l1 = j1 \/ l1 = 0 :: j1.
    Admitted.

    Lemma lj_eq2
      : l2 = j1 \/ l2 = 0 :: j1 \/ loop_contains u2 q1.
    Admitted.


  End disj_eqdep.

End disj.

Lemma DiamondPaths_sym `(C : redCFG) s u1 u2 p1 p2 q1 q2 k i l1 l2 j1 j2 r1 r2
      (D : DiamondPaths s u1 u2 p1 p2 q1 q2 k i l1 l2 j1 j2 r1 r2)
  : DiamondPaths s u2 u1 p2 p1 q2 q1 k i l2 l1 j2 j1 r2 r1.
Proof.
  destruct D.
  econstructor;eauto.
  - eapply Disjoint_sym;eauto.
  - symmetry. eauto.
Qed.
