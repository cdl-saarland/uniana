Require Export EEdge.

Section cfg.
  Context `(C : redCFG).

  Lemma loop_head_acyclic_entry p h
        (Hloop : loop_head h)
        (Hedge : a_edge__P p h)
    : entry_edge p h.
  Proof.
    copy Hedge Hedge'.
    eapply a_edge_incl in Hedge.
    destruct (edge_Edge Hedge).
    all:auto;exfalso.
    - eapply basic_edge_no_loop2;eauto.
    - destruct b. contradiction.
    - destruct e. eapply no_exit_head;eauto.
  Qed.

  Lemma loop_cutting q p t
        (Hpath : CPath q p t)
        (Hnoh : forall h, loop_contains h q -> h ∉ t)
    : exists t', Path a_edge__P q p t'.
  Proof.
    revert p Hpath Hnoh.
    specialize (well_founded_ind (R:=(@StrictPrefix' Lab)) (@StrictPrefix_well_founded Lab)
                                 (fun t => forall p : Lab,
                                      CPath q p t
                                      -> (forall h : Lab, loop_contains h q -> h ∉ t)
                                      -> exists t' : list Lab, Path a_edge__P q p t'))
      as WFind.
    eapply WFind.
    intros;clear WFind.
    inv_path H0.
    - eexists;econstructor.
    - specialize (H π) as Hπ.
      exploit' Hπ.
      { econstructor. econstructor. }
      specialize (Hπ x0).
      exploit Hπ.
      { intros. intro N. eapply H1;eauto. }
      destructH.
      destruct (edge_Edge H3).
      + exists (p :: t'). destruct b. econstructor;eauto.
      + eapply loop_contains_ledge in b. eapply dom_loop_contains in b;cycle 1.
        * intro N. eapply H1;eauto.
        * eapply dom_dom_acyclic in b. eapply b in Hπ as Hb.
          eapply path_to_elem in Hb;eauto. destructH. eexists;eauto.
      + exists (p :: t').
        eapply entry_edge_acyclic in e. econstructor;eauto.
      + exists (p :: t').
        eapply exit_edge_acyclic in e. econstructor;eauto.
  Qed.

  Lemma member_reachs_innermost_latch_acyclic h q
        (Hloop : innermost_loop h q)
    : exists p, p ↪ h /\ q -a>* p.
  Proof.
    destruct Hloop. destruct H. destructH.
    exists x. split;auto.
    decide (h = q).
    { subst q. eapply loop_reachs_member. eapply loop_contains_ledge;eauto. }
    eapply loop_cutting in H3;eauto.
    intros.
    destr_r' π;subst.
    - inv H3.
    - path_simpl' H3.
      rewrite rev_rcons in H4. cbn in H4. rewrite <-in_rev in H4.
      assert (h ∉ (l ++ [q])) as Hnin.
      {
        contradict H4.
        eapply In_rcons in H4.
        destruct H4;[contradiction|auto].
      }
      contradict Hnin.
      decide (h0 = h). { subst;eauto. }
                       eapply path_from_elem in Hnin;eauto.
      destructH.
      eapply postfix_incl;eauto.
      eapply dom_loop_contains;eauto.
      + eapply loop_contains_ledge;eauto.
      + intro N. eapply H0 in H. contradict n0. eapply loop_contains_Antisymmetric;eauto.
  Qed.
End cfg.
