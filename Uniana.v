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

Require Util Graph Evaluation Unchanged Disjoint UniquePI LoopSplits Splits.

Module Uniana.
  Import Util Evaluation.Evaluation Disjoint.Disjoint Unchanged.Unchanged.
  Import UniquePI.UniquePI Splits.Splits LoopSplits.LoopSplits.
  
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
      else fun x => ((join_andb (map (fun spl
                                   => match spl with
                                       (s, x) => uni s x
                                     end)
                                  (splits p ++ loop_splits p)))
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
  
  Lemma branch_eff_eq br s1 s2 x i k k':
    is_branch br x
    -> s1 x = s2 x
    -> eff (br,i,s1) = Some k
    -> eff (br,i,s2) = Some k'
    -> fst k = fst k'.
  Proof.
    intros Hbr Heq Heff1 Heff2. unfold is_branch in Hbr. specialize (branch_spec br) as Hb.
    destruct Hbr as [tt [ff [xb Hbr]]].
    rewrite Hbr in Hb.
    destruct k as [[q j] r]. destruct k' as [[q' j'] r'].
    cbn.
    enough (q = q' /\ j = j') as [qeq jeq].
    {subst q j. reflexivity. }
    destruct Hb as [_ Hb]. apply Hb in Heff1 as Heff1'; apply Hb in Heff2 as Heff2'.
    cbn in Heff1',Heff2'. rewrite Heq in Heff1'. rewrite <-Heff2' in Heff1'. split;[assumption|].
    destruct Heff1'. clear Heff2'.
    eapply ivec_det; eauto.
  Qed.
        
  Lemma splits_is_branch br x p :
    In (br,x) (splits p) -> is_branch br x.
  Proof.
    intro HSsplit.
    eapply splits_spec in HSsplit. unfold DisjointBranch in HSsplit. firstorder.
  Qed.

  Lemma loop_splits_is_branch :
    forall (br : Lab) (x : Var) (p : Lab), In (br, x) (loop_splits p) -> is_branch br x.
  Proof.
    intros. eapply loop_splits_spec in H. firstorder.
  Qed.
  
  Ltac eff_some_k :=
    lazymatch goal with
    | [Htr : Tr ?tq,
             Hpost : Postfix (?l :r: ?K) (ne_to_list ?tq)
       |- exists k, eff ?K = Some k]                      
      => eapply postfix_incl in Hpost as Hpost_incl;
        eapply Tr_EPath in Htr as Htr';
        [destruct Htr' as [s0 Htr']|subst tq;simpl_nl;reflexivity];
        xeapply path_postfix_path Hpost; eauto;
        eapply front_eff_ex_succ;[eapply Htr| | |];
        eauto; [|subst tq; simpl_nl;eauto];
        eapply Hpost_incl,In_rcons; tauto
    end.
  
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
        * (* disjoint paths! *)
          destruct (q == q') as [ Heq | Hneq ]; [ eauto | exfalso ].
          assert (In q' (preds p)) as Hqpred' by (eauto using step_conf_implies_edge).
          
          pose (tq1 := nlcons (q,j,r)     (prefix_nincl (q,j,r) (`t1))).
          pose (tq2 := nlcons (q',j',r') (prefix_nincl (q',j',r') (`t2))).
          assert (Tr tq1) as Htr1. {
            eapply prefix_trace. subst tq1. rewrite <-nlcons_to_list.
            eapply prefix_nincl_prefix.
            eauto. destruct t1; eauto.
          }
          assert (Tr tq2) as Htr2. {
            eapply prefix_trace. subst tq2. rewrite <-nlcons_to_list.
            eapply prefix_nincl_prefix.
            eauto. destruct t2;eauto.
          }
          assert (exists (si : Lab * Tag),
                        last_common (ne_map fst tq1) (ne_map fst tq2) si) as [[S' I'] LC_lt].
          {
            eapply ne_last_common. repeat rewrite ne_back_map.
            eapply ne_back_trace in Htr1 as [s1 Htr1].
            eapply ne_back_trace in Htr2 as [s2 Htr2].
            setoid_rewrite Htr1. setoid_rewrite Htr2. cbn;eauto.
         } 
          (**)
          decide' (i == I'). (* if the tag is the same there is a splitpoint *)
          -- apply id in LC_lt as LC_lt'.
             destruct LC_lt as [l1' [l2' [Hpost1 [Hpost2 [Hdisj [Hnin1 Hnin2]]]]]].
             eapply last_common_splits in LC_lt'; eauto.
             destruct LC_lt' as [x' HSsplit].
             ++ eapply join_andb_true_iff in Hsplit; eauto; [|apply in_or_app;left;eauto].
                cbn in Hsplit. conv_bool. 
                apply postfix_ex_unmapped_postfix' in Hpost1 as [l01 [s1' [Hpost1 Hposteq1]]].
                apply postfix_ex_unmapped_postfix' in Hpost2 as [l02 [s2' [Hpost2 Hposteq2]]].
                2,3: econstructor; apply zero.
                eapply HCuni in Hsplit. all: cycle 1.
                ** exact Hts1.
                ** exact Hts2.
                ** eapply prefix_incl;eauto. eapply prefix_trans.
                   --- eapply prefix_nincl_prefix. eapply postfix_incl.
                       eapply Hpost1. eapply In_rcons;eauto.
                   --- subst tq1. rewrite <-nlcons_to_list. eapply prefix_nincl_prefix; eauto.
                   --- left. reflexivity.
                ** eapply prefix_incl;eauto. eapply prefix_trans.
                   --- eapply prefix_nincl_prefix. eapply postfix_incl.
                       eapply Hpost2. eapply In_rcons;eauto.
                   --- subst tq2. rewrite <-nlcons_to_list. eapply prefix_nincl_prefix; eauto.
                   --- left. reflexivity.
                ** eapply splits_is_branch in HSsplit as HSbranch.
                   assert (exists k, eff (S', i, s1') = Some k) as [k Hk] by eff_some_k.
                   assert (exists k', eff (S', i, s2') = Some k') as [k' Hk'] by eff_some_k.
                   eapply branch_eff_eq in Hsplit; eauto.
                   subst l1' l2'.
                   eapply not_same_step_disj_post with (q:=q); eauto.
                   rewrite Hk, Hk'. cbn. 
                   unfold option_fst. rewrite Hsplit. reflexivity.
          -- apply id in LC_lt as LC_lt'.
             eapply lc_loop_split with (i:=i) in LC_lt; cycle 1; eauto.
             ++ subst tq1.
                rewrite ne_map_nlcons. cbn. reflexivity.
             ++ subst tq2;rewrite ne_map_nlcons; cbn; reflexivity.
             ++ eapply Tr_EPath in Htr1 as [s0 Htr1]. eapply EPath_TPath in Htr1.
                cbn in Htr1. econstructor; eauto. cbn. split; [apply Hqpred|].
                eapply eff_eff_tag; eauto.                
                subst tq1. simpl_nl. reflexivity.
             ++ eapply Tr_EPath in Htr2 as [s0 Htr2]. eapply EPath_TPath in Htr2.
                cbn in Htr2. econstructor; eauto. cbn. split; [apply Hqpred'|eauto].
                eapply eff_eff_tag; eauto.
                subst tq2. simpl_nl. reflexivity.
             ++ destruct LC_lt as [X' HSsplit'].
                destruct LC_lt' as [l1' [l2' [Hpost1 [Hpost2 [Hdisj [Hnin1 Hnin2]]]]]].
                eapply join_andb_true_iff in Hsplit; [|apply in_or_app;right; eauto]. cbn in Hsplit.
                conv_bool.                 
                eapply postfix_ex_unmapped_postfix' in Hpost1 as [l01 [s1' [Hpost1 Hposteq1]]].
                apply postfix_ex_unmapped_postfix' in Hpost2 as [l02 [s2' [Hpost2 Hposteq2]]].
                2-5: eauto using zero, start_tag.
                eapply HCuni in Hsplit. all: cycle 1.
                ** exact Hts1.
                ** exact Hts2.
                ** eapply prefix_incl;eauto. eapply prefix_trans with (l2:=tq1).
                   --- eapply prefix_nincl_prefix. eapply postfix_incl.
                       eapply Hpost1. eapply In_rcons;eauto.
                   --- subst tq1. rewrite <-nlcons_to_list. eapply prefix_nincl_prefix; eauto.
                   --- left. reflexivity.
                ** eapply prefix_incl;eauto. eapply prefix_trans with (l2:=tq2).
                   --- eapply prefix_nincl_prefix. eapply postfix_incl.
                       eapply Hpost2. eapply In_rcons;eauto.
                   --- subst tq2. rewrite <-nlcons_to_list. eapply prefix_nincl_prefix; eauto.
                   --- left. reflexivity.
                ** eapply loop_splits_is_branch in HSsplit' as HSbranch.
                   assert (exists k, eff (S', I', s1') = Some k) as [k Hk] by eff_some_k.
                   (* because Tr ((p,i,s) ... (S',I',s')) *)
                   assert (exists k', eff (S', I', s2') = Some k') as [k' Hk'] by eff_some_k.
                   eapply branch_eff_eq in Hsplit; eauto.
                   subst l1' l2'.
                   eapply not_same_step_disj_post with (q:=q); eauto. 
                   rewrite Hk,Hk'. cbn. rewrite Hsplit. reflexivity.
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
        * subst j'. eapply HCuni. eapply Hts1. eapply Hts2. 3: eauto.
          all: eapply precedes_step_inv.
          -- rewrite <-nlcons_to_list. setoid_rewrite Hteq1 in Hprec. apply Hprec.
          -- rewrite <-nlcons_necons, <-Hteq1. destruct t; eauto.
          -- cbn. eauto.
          -- rewrite <-nlcons_to_list. setoid_rewrite Hteq2 in Hprec'. apply Hprec'.
          -- rewrite <-nlcons_necons, <-Hteq2. destruct t'; eauto.
          -- cbn;eauto.
        * symmetry. eapply (HCupi _ _ Hsem Hsem'); eauto.
          Unshelve. all: exact (root,start_tag,zero).
  Qed.


End Uniana.
      