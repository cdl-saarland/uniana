Require Import Coq.Classes.EquivDec.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.Decidable.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Utils.
Require Import Lists.ListSet.
Require Import List.
Require Import Nat. 

Require Util Graph Evaluation Unchanged Disjoint UniquePI.

Module Uniana.
  Import Util Evaluation.Evaluation Disjoint.Disjoint Unchanged.Unchanged UniquePI.UniquePI.
  
  Parameter init_uni : Var -> Prop.

  Definition UniState := Var -> bool.
         
  Parameter abs_uni_eff : UniState -> UniState.

  Definition uni_state_concr (uni : UniState) : State -> State -> Prop :=
    fun s => fun s' => forall x, uni x = true -> s x = s' x.

  Parameter local_uni_corr : forall uni p i q j s s' qs qs', 
      uni_state_concr uni s s' ->
      eff (p, i, s) = Some (q, j, qs) ->
      eff (p, i, s') = Some (q, j, qs') ->
      uni_state_concr (abs_uni_eff uni) qs qs'.

  Definition uni_concr (u : Uni) : Hyper :=
    fun ts => forall t t', ts t -> ts t' ->
                   forall x p i s s', In (p, i, s) (`t) ->
                                 In (p, i, s') (`t') ->
                                 u p x = true -> s x = s' x.
  
  Definition uni_trans (uni : Uni) (upi : Upi) (unch : Unch) : Uni :=
    fun p
    => if p == root then uni root
      else fun x => ((join_andb (map (fun spl => match spl with
                                             (s, x) => uni s x && upi_trans upi uni s p
                                           end)
                                  (splits p)))
                    && (join_andb (map (fun q => abs_uni_eff (uni q) x) (preds p)))
                    && (join_andb (map (fun q => upi_trans upi uni q p) (preds p)))
                 )
                 || join_orb (map (fun q => (q <>b p) && uni q x && upi_trans upi uni q p)
                                 (unch_trans unch p x)).

  Lemma uni_trans_root_inv :
    forall uni hom unch x, uni_trans uni hom unch root x = uni root x.
  Proof.
    intros.
    unfold uni_trans.
    destruct (equiv_dec root root).
    reflexivity.
    exfalso. apply c. reflexivity.
  Qed.

  Lemma uni_correct :
    forall uni upi unch ts,
        sem_hyper (red_prod (red_prod (uni_concr uni) (upi_concr upi)) (lift (unch_concr unch))) ts ->
        uni_concr (uni_trans uni upi unch) ts.
  Proof.
    intros uni upi unch ts Hred.
    unfold sem_hyper in Hred.
    destruct Hred as [ts' [Hconcr Hstep]].
    unfold uni_concr.
    intros t t' Hsem Hsem' x p i s s' HIn HIn' Htrans.

    assert (upi_concr (upi_trans upi uni) ts) as HCupi. {
      apply upi_correct. 
      destruct Hconcr as [[_ Hhom] _].
      exists ts'; auto.
    }

    assert (unch_concr (unch_trans unch) t) as HCunch. {
      destruct Hconcr as [[_ _] Hunch].
      unfold lift in *; subst.
      apply unch_correct. assumption.
    } 
    
    assert (unch_concr (unch_trans unch) t') as HCunch'. {
      destruct Hconcr as [[_ _] Hunch].
      unfold lift in *; subst.
      apply unch_correct. assumption.
    }

    destruct Hconcr as [[HCuni HCupi'] _].

    subst.
    unfold uni_trans in Htrans. 
    assert (X := Hsem). destruct X as [t1 [k1 [Hts1 Hteq1]]].
    (*destruct X as [l [ltr [lstep [Hts Hlstep]]]]; subst.*)
    assert (X := Hsem'). destruct X as [t2 [k2 [Hts2 Hteq2]]].
    (*destruct X as [l' [ltr' [lstep' [Hts' Hlstep']]]]; subst.*)
    destruct (p == root); [ subst | ].
    - rewrite e in *; clear e. 
      (*destruct t as [t tr]. destruct t; cbn in HIn; inversion HIn.*)
      eapply HCuni; [eapply Hts1|apply Hts2| | | apply Htrans].
      + specialize (root_prefix t1) as [s0 rp]. apply root_start_tag in HIn as rst. subst i.
        eapply prefix_cons_in in rp as rp'.
        assert (Prefix (`t1) (`t)) as pre_t.
        { rewrite Hteq1. cbn. econstructor. econstructor. }
        eapply prefix_trans with (l2:=`t1) (l3:=`t) in rp; eauto.
        apply prefix_cons_in in rp. eapply tag_inj in HIn; [| apply rp]. subst s0. eauto.
      + specialize (root_prefix t2) as [s0 rp]. apply root_start_tag in HIn as rst. subst i.
        eapply prefix_cons_in in rp as rp'.
        assert (Prefix (`t2) (`t')) as pre_t.
        { rewrite Hteq2. cbn. econstructor. econstructor. }
        eapply prefix_trans with (l2:=`t2) (l3:=`t') in rp; eauto.
        apply prefix_cons_in in rp. eapply tag_inj in HIn'; [| apply rp]. subst s0. eauto.
    - conv_bool.
      destruct Htrans as [Htrans | Hunch].
      (* The uni/hom case *)
      + destruct Htrans as [[Hsplit Hpred] Hupi].
        rewrite Hteq1 in HIn. rewrite Hteq2 in HIn'.
        eapply in_pred_exists in HIn; try eassumption; [|setoid_rewrite <-Hteq1; exact (proj2_sig t)].
        eapply in_pred_exists in HIn'; try eassumption;[|setoid_rewrite <-Hteq2; exact (proj2_sig t')].
        destruct HIn as [q [j [r [HIn Hstep]]]].
        destruct HIn' as [q' [j' [r' [HIn' Hstep']]]].
        assert (List.In q (preds p)) as Hqpred by (eauto using step_conf_implies_edge).
        cut (q' = q); intros; subst.
        * cut (j' = j); intros; subst.
          -- eapply (local_uni_corr (uni q) q j p i r r' s s'); try eassumption.
             ** unfold uni_state_concr. intros.
                unfold uni_concr in HCuni .
                eapply (HCuni _ _ Hts1 Hts2 x0 q j); eassumption.
             ** eapply join_andb_true_iff in Hpred; try eassumption.
          -- (* unique preceding instances *)
            eapply join_andb_true_iff in Hupi; try eassumption.
            assert (p =/= q) by (symmetry; eauto using step_conf_implies_edge, no_self_loops).
            symmetry.
            eapply HCupi; [ eapply Hsem | eapply Hsem' | eassumption | | ].
            1: rewrite Hteq1. 2: rewrite Hteq2.
            all: cbn; rewrite nlcons_to_list; eapply precedes_step; eauto.
            all: rewrite <-nlcons_necons.
            ++ setoid_rewrite <-Hteq1. destruct t; cbn; eauto.
            ++ setoid_rewrite <-Hteq2. destruct t'; cbn; eauto.
        * (* disjoint paths! *) admit. (*
          destruct (q == q') as [ Heq | Hneq ]; [ eauto | exfalso ].
          assert (List.In q' (preds p)) as Hqpred' by (eauto using step_conf_implies_edge).
          unfold upi_concr in HCupi.
          eapply (join_andb_true_iff _ _ Hupi) in Hqpred'.
          eapply (join_andb_true_iff _ _ Hupi) in Hqpred.
          symmetry in Hneq.
          eapply disjoint with (q := q) (step := lstep) in Hneq; eauto.
          ++ destruct Hneq as [br [y [yb [Hwit Hspl]]]].
             destruct Hwit as [m [u' [u [Hney [Hinbr' [Hinbr _]]]]]].
             eapply join_andb_true_iff in Hsplit; try eapply Hspl. simpl in Hsplit. conv_bool.
             destruct Hsplit as [Hsplit _].
             apply Hney.
             cut (u' y = u y); intros. rewrite H. reflexivity.
             eapply HCuni; [ exact Hts' | exact Hts | | | ]; eauto.
          ++ intros.
             eapply HCupi; eauto.
             eapply (join_andb_true_iff _ _ Hsplit) in H.
             conv_bool. destruct H as [_ H]. eassumption. *)
        (* The unch case *)
      + rename Hunch into H.
        eapply join_orb_true_iff in H.
        destruct H as [u H].
        conv_bool.
        destruct H as [Hunch [[Hneq' Huni] Hupi]].
        specialize (HCunch p i s u x HIn Hunch).
        specialize (HCunch' p i s' u x HIn' Hunch).
        destruct HCunch as [j [r [Hprec Heq]]]; try eassumption.
        destruct HCunch' as [j' [r' [Hprec' Heq']]]; try eassumption.
        rewrite <- Heq. rewrite <- Heq'.
        cut (j' = j); intros.
        * subst j'. admit. (*eauto using precedes_step_inv.  *)
        * symmetry. eapply (HCupi _ _ Hsem Hsem'); eauto. 
  Qed.


End Uniana.
      