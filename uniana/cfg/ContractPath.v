Require Export HeadRewire PPexhead.
Require Import Lia.

Section cfg.
  Context `{C : redCFG}.

  Infix "-->" := edge__P.


  Lemma contract_cpath (π : list Lab) p q
        (Hπ : CPath p q π)
        (Hdeq : forall x, x ∈ π -> deq_loop x q)
        (Hnin : forall x, x ∈ tl π -> ~ loop_contains x q) (* Header of q is not on π *)
    : exists ϕ, HPath p q ϕ /\ ϕ ⊆ π.
  Proof.
    revert dependent q. revert dependent π.
    specialize (well_founded_ind (R:=(@StrictPrefix' Lab)) (@StrictPrefix_well_founded Lab)
                                 (fun π : list Lab => forall q, CPath p q π ->
                                                        (forall x, x ∈ π -> deq_loop x q) ->
                                                        (forall x, x ∈ tl π -> ~ loop_contains x q) ->
                                                        exists ϕ, HPath p q ϕ /\ ϕ ⊆ π))
      as WFind.
    eapply WFind.
    intros π IH q Hπ Hdeq Hnin. clear WFind.
    inv Hπ.
    - exists [q]. unfold incl. split; eauto; econstructor.
    - specialize (edge_Edge H0) as Hedge.
      rename H into Hπ. rename q into c. rename π0 into π.
      assert (Hprefix : StrictPrefix' π (c :: π)) by (repeat econstructor).
      simpl in Hnin.
      inv Hedge.
      + edestruct IH as [ϕ [Hϕ Hincl]]; try eauto.
        * unfold deq_loop in *. eauto using basic_edge_loop_contains.
        * intros. intro. eapply Hnin. simpl. eapply in_tl_in. eassumption.
          eauto using basic_edge_loop_contains.
        * exists (c :: ϕ). split; [| eauto using incl_app ].
          econstructor; [ eassumption |].
          left. split; [ eassumption |].
          intro.  eapply (Hnin b). eauto using path_contains_front.
          eauto using loop_contains_self, basic_edge_loop_contains.
      + edestruct IH as [ϕ [Hϕ Hincl]]; try eauto.
        * unfold deq_loop in *. eauto using back_edge_loop_contains.
        * intros. intro. eapply Hnin. simpl. eapply in_tl_in. eassumption.
          eauto using back_edge_loop_contains.
        * exists (c :: ϕ). split; [| eauto using incl_app ].
          econstructor; [ eassumption |].
          left. split; eauto using back_edge_src_no_loop_head.
      + unfold entry_edge in H. destruct H as [Hhead [H _]].
        exfalso. apply H. unfold deq_loop in Hdeq.
        eauto using loop_contains_self, in_cons, path_contains_front.
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
          -- assert (Hedge : e --> h).
             { eapply prefix_edge_exists. 2:eauto. eauto. }
             assert (Hedge' : entry_edge e h \/ back_edge e h). {
               eapply edge_Edge in Hedge.
               inv Hedge; try eauto.
               - exfalso. eapply basic_edge_no_loop2. eapply H.
                 eapply loop_contains_loop_head. eapply Hexit.
               - destruct H as [h' H]. eapply no_exit_head in H.
                 exfalso. apply H. unfold loop_contains in Hexit. unfold loop_head. firstorder.
             }
             destruct Hedge' as [Hent | Hback].
             ++ edestruct (@IH (e :: ϕ)) as [ϕ' [Hϕ' Hincl']].
                ** econstructor. eapply PreStep. eassumption.
                ** eapply prefix_cons in Hpre. eapply path_prefix_path'; try eassumption.
                ** intros. eapply eq_loop2.
                   --- eauto using enter_exit_same.
                   --- eapply Hdeq. eauto using in_prefix_in.
                ** simpl. intros. intro. eapply Hnin. eapply in_prefix_in. eapply H.
                   eauto using prefix_cons. eapply eq_loop2. eauto using enter_exit_same.
                   eapply deq_loop_refl. eassumption.
                ** exists (c :: h :: ϕ'). split.
                   --- econstructor. econstructor. eapply Hϕ'.
                       +++ left. split; [ eauto |].
                           intro. eapply (Hnin e).
                           *** eauto using prefix_cons, in_prefix_in.
                           *** eauto using deq_loop_head_loop_contains, eq_loop2, enter_exit_same.
                       +++ right. exists b. eassumption.
                   --- intros x Hx.
                       destruct Hx.
                       +++ subst. left;auto.
                       +++ destruct H.
                           *** subst. right;auto.
                           *** right. eapply prefix_incl;eauto.
             ++ assert (Hnin2 : forall x, x ∈ (e :: ϕ) -> ~ loop_contains x e). {
                  intros. intro. eapply Hnin. eapply in_prefix_in.
                  2: eapply Hpre.
                  1: eapply in_cons. eassumption.
                  specialize (back_edge_innermost Hback) as Hinner1.
                  - enough (x <> h).
                    + eapply (exit_edge_in_loop Hexit); try eassumption.
                      eauto using back_edge_loop_contains, eq_loop2.
                    + intro. subst. contradiction.
                }
                edestruct (@IH (e :: ϕ)) as [ϕ' [Hϕ' Hincl']].
                ** econstructor. eapply PreStep. eassumption.
                ** eapply prefix_cons in Hpre. eapply path_prefix_path'; try eassumption.
                ** eauto using exit_edge_innermost, back_edge_innermost,
                   path_no_loop_head_deq, prefix_cons, path_prefix_path' .
                ** eauto.
                ** exists (c :: h :: ϕ'). split.
                   --- econstructor. econstructor. eapply Hϕ'.
                       +++ left. split; [ eauto |].
                           decide (loop_head e); [| eassumption ]. exfalso.
                           eapply (Hnin2 e); eauto using loop_contains_self.
                       +++ right. exists b. eassumption.
                   --- intros x Hx.
                       destruct Hx.
                       +++ subst. left;auto.
                       +++ destruct H.
                           *** subst. right; auto.
                           *** right. eapply prefix_incl; eauto.
        * edestruct (IH π) as [ϕ [Hϕ Hincl]].
          -- econstructor. econstructor.
          -- eauto.
          -- eauto using exit_edge_innermost, back_edge_innermost, path_no_loop_head_deq.
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
  Qed.

  Lemma contract_cpath' (π : list Lab) q p
        (Hπ : CPath p q π)
        (Hdeq : deq_loop p q)
        (Hnin : forall x, x ∈ tl π -> ~ loop_contains x q)
    : exists ϕ, HPath p q ϕ /\ ϕ ⊆ π.
  Proof.
    eapply contract_cpath;eauto.
    unfold deq_loop. intros x Hxin h Hhcont.
    decide (loop_contains h x) as [Htmp | Hxcont]; [ assumption |].
    exfalso.
    destruct π as [|l π']; [ contradiction |].
    replace l with q in * by (eauto using path_front).
    simpl in Hnin.
    inversion Hπ; subst. {
      inv Hxin. contradiction. inv H.
    }
    rename H3 into Hedge. rename H0 into Hπ'.
    destruct Hxin as [Htmp | Hxin]. {
      subst. contradiction.
    }
    decide (loop_contains q q) as [Hhead | Hnhead ].
    - (* if q is a loop header, we cannot use Hnin to create a contradiction because it
         is only applicable to tl π. We essentially need to show that there is a header
         that contains q and lies on π' that contains all nodes on π'.
         We get that header using p_p_ex_head. Then, the fact that this header
         contains all other loops is in contradiction with Hnin. *)
      edestruct loop_reachs_member as [ρ Hρ].
      eapply (deq_loop_head_loop_contains Hdeq).
      eauto using loop_contains_loop_head.
      remember ((q :: π') ++ tl ρ) as σ.
      assert (Hσ : CPath q q σ). {
        rewrite Heqσ.
        eapply path_app'.
        - eapply subgraph_path'; eauto using a_edge_incl.
        - eassumption.
      }
      edestruct (p_p_ex_head Hσ) as [ho [Hin Hcont]]. {
        rewrite Heqσ. simpl.
        induction π'; try contradiction.
        simpl. lia.
      }
      assert (Hne : q <> ho). {
        intro. subst ho.
        eapply Hxcont.
        eapply loop_contains_trans.
        eapply Hhcont. eapply Hcont.
        rewrite Heqσ.
        eauto using in_or_app.
      }
      assert (Hoinπ' : ho ∈ π'). {
        (* Show that ho is on the π' part of σ.
           Essentially by constructing an acyclic path from ho to ho. *)
        assert (Hinσ := Hin).
        rewrite Heqσ in Hin. simpl in Hin.
        destruct Hin.
        - exfalso. eauto.
        - eapply in_app_or in H.
          destruct H;[ eassumption |].
          exfalso.
          edestruct loop_reachs_member as [τ Hτ]. {
            eapply Hcont. rewrite Heqσ. simpl. left. reflexivity.
          }
          eapply in_tl_in in H.
          edestruct (path_to_elem Hρ H) as [ω [Hω _]].
          eapply (path_path_acyclic Hτ Hω); eauto.
      }
      eapply (Hnin _ Hoinπ').
      eapply Hcont.
      rewrite Heqσ. eauto.
    - (* the other case is simple. The path needs to go through the loop header h
         to reach p. This header contradicts Hnin. *)
      eapply path_from_elem in Hπ'; try eauto.
      destruct Hπ' as [ϕ [Hϕ Hpost]].
      eapply (Hnin h); try eassumption.
      eapply in_postfix_in; try eassumption.
      eapply (dom_loop_contains).
      2: eapply Hxcont.
      2: eapply Hϕ.
      eapply (preds_in_same_loop Hhcont). {
        intro. subst. eauto.
      }
      eassumption.
  Qed.
End cfg.
