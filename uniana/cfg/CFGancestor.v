Require Export CFGinnermost ListExtra.

Section cfg.
  Context `{C : redCFG}.
  
  Notation "p '-a>b' q" := (a_edge p q) (at level 55).
  Notation "p '-a>' q" := (p -a>b q = true) (at level 55).
  Notation "p '-->b' q" := (edge p q) (at level 55).
  Notation "p '-->' q" := (p -->b q = true) (at level 55, right associativity).

  (** * Definitions **)

  Definition ancestor a p q :=
    loop_contains a p /\ loop_contains a q \/ a = root .

  Definition near_ancestor  a p q := (* we cannot allow root for the other ancestor *)
    ancestor a p q /\ forall a', loop_contains a' p /\ loop_contains a' q -> loop_contains a' a.

  Definition outermost_loop h p := loop_contains h p /\ forall h', loop_contains h' p -> loop_contains h h'.
  
  Definition ex_outermost_loop p
    := finType_sig_or_never (DecPred (fun h => outermost_loop h p)).

  Definition get_outermost_loop p : option Lab
    := match ex_outermost_loop p with
       | inleft (exist _ h H) => Some h
       | inright _ => None
       end.

  Definition strict_incl (A : Type) (l l' : list A)
    := l ⊆ l' /\ exists a, a ∈ l' /\ a ∉ l.

  Infix "⊂" := strict_incl (at level 55).

  (** * Facts about outermost_loops **)

  Lemma loop_contains_outermost h p
        (Hl : loop_contains h p)
    : exists h', outermost_loop h' p.
  Proof.
    remember (elem Lab).
    specialize (@elementIn Lab) as Hin.
    rewrite <-Heql in Hin.
    clear Heql.
    unfold outermost_loop.
    enough (forall l', l' ⊆ l
                  -> exists h' : Lab, loop_contains h' p /\ (forall h'0 : Lab, h'0 ∈ l'
                                                                   -> loop_contains h'0 p
                                                                   -> loop_contains h' h'0)).
    {
      specialize (H l).
      exploit H.
      destructH. eexists; eauto.
    }
    induction l';intros.
    - exists h. split;eauto. intros. cbn in H0. contradiction.
    - exploit IHl'.
      + eapply incl_cons;eauto.
      + destructH. decide (loop_contains a h').
        * exists a. split;[eapply loop_contains_trans;eauto|].
          intros. destruct H0.
          -- subst. eauto using loop_contains_self, loop_contains_loop_head.
          -- exploit IHl'1. eapply loop_contains_trans;eauto.
        * exists h'. split;[auto|]. intros.
          destruct H0;[subst|eapply IHl'1;eauto].
          eapply loop_contains_either in IHl'0;eauto.
          destruct IHl'0; [contradiction|auto].
  Qed.

  Lemma get_outermost_loop_spec p
    : match get_outermost_loop p with
      | Some h => outermost_loop h p
      | None => forall h, loop_contains h p -> False
      end.
  Proof.
    unfold get_outermost_loop.
    destruct (ex_outermost_loop p).
    - destruct s. cbn in *. auto.
    - cbn in *. intros. eapply loop_contains_outermost in H. destructH.
      eapply n;eauto.
  Qed.                  

  (*
  Lemma LPath_loop_contains  h h' p π
        (Hpath : LPath h p π)
        (Hin : h' ∈ tl π)
    : loop_contains h p.
  Proof.
    revert dependent p. revert dependent h'.
    induction π;intros;inversion Hpath;subst;cbn in *;[contradiction|].
    destruct π;inversion H3;subst;cbn in *;[destruct Hin;[subst|contradiction]|].
    - decide (innermost_loop_strict h' a);cbn in *;[|congruence]. unfold innermost_loop_strict in i. destructH;auto.
    - destruct Hin.
      + admit.
      + eapply IHπ;auto. inversion Hpath; subst; eauto.
        admit.
   *)

  (** * Existence of ancestors, near_ancestors **)
  
  Lemma ex_LPath p
    : exists h, (forall h', loop_contains h' p -> loop_contains h h') /\ exists π, LPath h p π.
  Proof.
    remember (get_outermost_loop p) as oh.
    specialize (get_outermost_loop_spec p) as Hspec.
    destruct (get_outermost_loop p).
    - unfold outermost_loop in Hspec. destructH.
      exists e. split;eauto. eapply loop_LPath;eauto.
    - exists p. split; [intros h' Hh'; eapply Hspec in Hh';contradiction|].
      eexists. econstructor.
  Qed.

  Definition ex_near_ancestor_opt p q
    := finType_sig_or_never (DecPred (fun a => near_ancestor a p q)).

  (*
  Lemma near_ancestor_same  h p q a
        (Hloop : innermost_loop h p)
        (Hanc1 : near_ancestor a h q)
    : near_ancestor a p q.*)

  (* show:
   * ancestors are exactly LPath p ∩ LPath q ∪ {root}
   * if x ∈ LPath p ∩ LPath q -> lpath to x is prefix of both lpaths
   * thus the nearest ancestor is the last such x
   *)

  Lemma ex_near_ancestor p q
    : exists a, near_ancestor a p q.
  Proof.

    (****)
    remember (elem Lab).
    specialize (@elementIn Lab) as Hin.
    rewrite <-Heql in Hin.
    clear Heql.
    unfold near_ancestor.
    enough (forall l', l' ⊆ l
                  -> exists a : Lab, ancestor a p q /\ (forall a' : Lab, a' ∈ l'
                                                             -> loop_contains a' p /\ loop_contains a' q
                                                             -> loop_contains a' a)).
    {
      specialize (H l).
      exploit H.
      destructH. eexists; eauto.
    }
    induction l';intros.
    - exists root. split;[right;auto|].
      intros;cbn in *;contradiction.
    - exploit IHl';[eapply incl_cons;eauto|].
      destructH.
      decide (loop_contains a p /\ loop_contains a q).
      + destructH. decide (loop_contains a0 a).
        * exists a. split;[left;auto|].
          intros. destruct H0;[subst;eauto using loop_contains_self, loop_contains_loop_head|].
          specialize (IHl'1 a'). exploit IHl'1.
          eapply loop_contains_trans;eauto.
        * destruct IHl'0.
          -- exists a0. split;[left;auto|].
             intros. 
             destruct H1.
             ++ subst. eapply loop_contains_either in a2;[|destruct H0 as [H0 _];apply H0].
                destruct a2;[|eauto].
                contradict n. eauto.
             ++ eapply IHl'1;eauto.
          -- subst a0. exists a. split;[left;auto|].
             intros. destruct H0;[subst;eauto using loop_contains_self, loop_contains_loop_head|].
             specialize (IHl'1 a'). exploit IHl'1.
             eapply root_loop_root in IHl'1. subst.
             destructH. eapply loop_contains_either in H2. 2: apply a2.
             destruct H2;[|auto]. eapply root_loop_root in H1. subst.
             eauto using loop_contains_loop_head, loop_contains_self.
      + simpl_dec' n.
        destruct n.
        1,2 : exists a0; split;[auto|];
                  intros; destruct H1;[subst;destruct H2;contradiction|eapply IHl'1;eauto].
  Qed.

  (** * Dominance **)
  
  Lemma ancestor_dom1 a p q
    : ancestor a p q -> Dom edge__P root a p.
  Proof.
    intros.
    destruct H.
    - destruct H.
      eapply dom_loop;eauto.
    - subst. eapply dominant_root.
  Qed.

  Lemma ancestor_sym a p q
    : ancestor a p q -> ancestor a q p.
  Proof.
    unfold ancestor;firstorder 0.
  Qed.
  
  Lemma ancestor_dom2 a p q
    : ancestor a p q -> Dom edge__P root a q.
  Proof.
    eauto using ancestor_dom1, ancestor_sym.
  Qed.

End cfg.
