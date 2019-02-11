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

Require Util Graph Evaluation Unchanged Disjoint.

Module Uniana.
  Import Util Evaluation.Evaluation Disjoint.Disjoint Unchanged.Unchanged.

  Section uniana.

    Context `(C : redCFG).
    
  Parameter branch: Lab -> option Var.

  Definition is_branch br x := branch br = Some x.

  Parameter val_true : Val -> bool.

  Parameter branch_spec :
    forall p, match branch p with
         | Some x => exists q q' s r r', q <> q'
                                   /\ if val_true (s x)
                                     then eff' (p,s) = Some (q, r)
                                     else eff' (p,s) = Some (q',r')                                
         | None => forall q q', p --> q -> p --> q' -> q = q'
         end.

  Parameter root_no_pred' : forall p, p --> root -> False.
    
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

  Definition Uni := Lab -> Var -> bool.

  Definition uni_concr (u : Uni) : Hyper :=
    fun ts => forall t t', ts t -> ts t' ->
                   forall x p i s s', In (p, i, s) (`t) ->
                                 In (p, i, s') (`t') ->
                                 u p x = true -> s x = s' x.

  Definition uni_branch (uni : Uni) :=
    (fun spq : Lab * Lab * Lab
     => let s := fst (fst spq) in
       match (branch s) with
       | Some x => uni s x
       | None => false
       end
    ).  
  
  Definition uni_trans (uni : Uni) (unch : Unch) : Uni :=
    fun p
    => if p == root then uni root
      else fun x => (join_andb (map (uni_branch uni) (splits p)))
                 (* the predecessor is only included in split set if p is an exit *)
                   && (join_andb (map (fun q => abs_uni_eff (uni q) x) (preds p)))
                 || join_orb (map (fun q => (q <>b p)
                                          && uni q x
                                          && join_andb (map (uni_branch uni) (rel_splits p q)))
                                 (unch_trans unch p x)).

  Lemma uni_trans_root_inv :
    forall uni unch x, uni_trans uni unch root x = uni root x.
  Proof.
    intros.
    unfold uni_trans.
    destruct (equiv_dec root root).
    reflexivity.
    exfalso. apply c. reflexivity.
  Qed.
  
  (*  
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
   *)
        
  (*
  Lemma splits_is_branch br x p :
    In (br,x) (splits p) -> is_branch br x.
  Proof.
    intro HSsplit.
    eapply splits_spec in HSsplit. unfold DisjointBranch in HSsplit. firstorder.
  Qed.
   *)

  (*
  Lemma loop_splits_is_branch :
    forall (br : Lab) (x : Var) (p s : Lab), In (br, x) (loop_splits p s) -> is_branch br x.
  Proof.
    intros. eapply loop_splits_spec in H. firstorder.
  Qed.
   *)

  (*
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
   *)
  
  (*
  Lemma is_split_loop_split p0 p q1 q2 br i0 i j1 j2 k l1 l2
    (Hpath1 : TPath (p0,i0) (p,i) ((p, i) :<: (q1, j1) :< l1))
    (Hpath2 : TPath (p0,i0) (p,i) ((p, i) :<: (q2, j2) :< l2))
    (Hneq : q2 =/= q1)
    (LC_lt : last_common ((q1, j1) :< l1) ((q2, j2) :< l2) (br, k)) :
    (exists x, (br,x) ∈ splits p) \/ exists s x x', (s,x) ∈ splits p /\ (br,x') ∈ preceding_loop_splits p s.
  Admitted.
   *)
  Definition sub_traces (ts ts' : Traces) : Prop := forall t, ts t -> exists t', ts' t' /\ Prefix (`t) (`t').

  Lemma uni_concr_sub_traces ts ts' uni
        (Hsub : sub_traces ts ts')
        (Huni : uni_concr uni ts')
    : uni_concr uni ts.
  Proof.
    unfold uni_concr in *. unfold sub_traces in Hsub.
    intros. specialize (Hsub t H) as Hsub1. specialize (Hsub t' H0) as Hsub2. destructH. destructH.
    eapply (Huni t'1 t'0); eauto.
    - eapply in_prefix_in;eauto.
    - eapply in_prefix_in;eauto.
  Qed.    
  
  Lemma uni_same_tag p q i j1 j2 s1 s2 r1 r2 (t1 t2 : trace) uni ts l1 l2
        (Htr1 : Tr ((p,i,s1) :<: (q,j1,r1) :< l1))
        (Htr2 : Tr ((p,i,s2) :<: (q,j2,r2) :< l2))
        (Hpre1 : Prefix ((q,j1,r1) :: l1) (`t1))
        (Hpre2 : Prefix ((q,j2,r2) :: l2) (`t2))
        (Hsplit : (join_andb (map (uni_branch uni) (splits p))) = true)
        (HCuni : uni_concr uni ts)
        (Hsem1 : ts t1)
        (Hsem2 : ts t2)
    : j2 = j1.
  Proof.
    (* use tag_eq_loop_exit *)
  Admitted.

  Lemma unch_same_tag p u j1 j2 r1 r2 ts l1 l2 (t1 t2 : trace) x uni unch
        (Hunibr : join_andb (map (uni_branch uni) (rel_splits p u)) = true)
        (Hunch : u ∈ unch_trans unch p x)
        (Hpre1 : Prefix l1 (`t1))
        (Hpre2 : Prefix l2 (`t2))
        (Hprec1 : Precedes l1 (u, j1, r1))
        (Hprec2 : Precedes l2 (u, j2, r2))
        (HCuni : uni_concr uni ts)
        (Hts1 : ts t1)
        (Hts2 : ts t2)
    : j1 = j2.
  Admitted.

  Lemma uni_same_lab p q1 q2 i j1 j2 s1 s2 r1 r2 (t1 t2 : trace) uni ts l1 l2
        (Htr1 : Tr ((p,i,s1) :<: (q1,j1,r1) :< l1))
        (Htr2 : Tr ((p,i,s2) :<: (q2,j2,r2) :< l2))
        (Hpre1 : Prefix ((q1,j1,r1) :: l1) (`t1))
        (Hpre2 : Prefix ((q2,j2,r2) :: l2) (`t2))
        (Hsplit : (join_andb (map (uni_branch uni) (splits p))) = true)
        (HCuni : uni_concr uni ts)
        (Hsem1 : ts t1)
        (Hsem2 : ts t2)
    : q2 = q1.
  Proof.  
  assert (exists (si : Lab * Tag),
             last_common (ne_map fst ((q1,j1,r1) :< l1))
                         (ne_map fst ((q2,j2,r2) :< l2)) si) as [[br k] LC_lt].
  {
    eapply ne_last_common. repeat rewrite ne_back_map.
    eapply ne_back_trace in Htr1 as [s1' Htr1]. cbn in Htr1.
    eapply ne_back_trace in Htr2 as [s2' Htr2]. cbn in Htr2.
    setoid_rewrite Htr1. setoid_rewrite Htr2. cbn;eauto.
  }
  simpl_nl' LC_lt; cbn in LC_lt.
  destruct (q2 == q1) as [ Heq | Hneq ]; [ eauto | exfalso ].
  symmetry in Hneq.
  eapply lc_join_split in LC_lt as LC_join;eauto.
  Unshelve. all:cycle 3. exact p. exact i.
  - unfold last_common in LC_lt. destructH' LC_lt.
    destruct l1',l2';cbn in *.
    + (* q1 = br = q2 --> contradiction *) admit.
    + (* since (br,k) = (q1,j1) & uniform, we have that (p,i) succeeds (br,k) thus
         (p,i) ∈ l2, thus double occurence of the same instance in t2 --> contradiction *) admit.
    + (* since (br,k) = (q2,j2) & uniform, we have that (p,i) succeeds (br,k) thus
         (p,i) ∈ l1, thus double occurence of the same instance in t1 --> contradiction *) admit. 
    + (* successor of br is the same because of uniformity and in l1' & l2', 
         thus l1' & l2' are not disjoint --> contradiction *) admit.
  - eapply Tr_EPath in Htr1; cbn;eauto. destruct Htr1 as [s01 Htr1]. eapply EPath_TPath in Htr1.
    cbn in *. unfold TPath'. simpl_nl' Htr1. cbn in *. (* follows from Htr1 *) admit.
  - (* follows from Htr2, if LC_join is adapted *) admit.
  Admitted.   
  
  Lemma uni_correct :
    forall uni unch ts,
      sem_hyper (red_prod (uni_concr uni) (lift (unch_concr unch))) ts ->
      uni_concr (uni_trans uni unch) ts.
  Proof.
    intros uni unch ts Hred.
    unfold sem_hyper in Hred.
    destruct Hred as [ts' [Hconcr Hstep]].
    unfold uni_concr.
    intros t t' Hsem Hsem' x p i s s' HIn HIn' Htrans.

(*    assert (upi_concr (upi_trans upi uni) ts) as HCupi. {
      apply upi_correct. 
      destruct Hconcr as [[_ Hhom] _].
      exists ts'; auto.
    }*)

    assert (unch_concr (unch_trans unch) t) as HCunch. {
      destruct Hconcr as [_ Hunch].
      unfold lift in *; subst.
      apply unch_correct; [eapply root_no_pred'|]. assumption.
    } 
    
    assert (unch_concr (unch_trans unch) t') as HCunch'. {
      destruct Hconcr as [ _ Hunch].
      unfold lift in *; subst.
      apply unch_correct; [eapply root_no_pred'|]. assumption.
    }

    destruct Hconcr as [HCuni  _].

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
        eapply prefix_trans with (l2:=`t1) (l3:=`t) in rp; eauto. 2:eapply root_no_pred'.
        apply prefix_cons_in in rp. eapply tag_inj in HIn; [| eapply root_no_pred'| apply rp].
        subst s0. eauto.
      + specialize (root_prefix t2) as [s0 rp]. apply root_start_tag in HIn as rst. subst i.
        eapply prefix_cons_in in rp as rp'.
        assert (Prefix (`t2) (`t')) as pre_t.
        { rewrite Hteq2. cbn. econstructor. econstructor. }
        eapply prefix_trans with (l2:=`t2) (l3:=`t') in rp; eauto.
        apply prefix_cons_in in rp. eapply tag_inj in HIn'; [|eapply root_no_pred'| apply rp].
        subst s0. eauto. eapply root_no_pred'.
    - conv_bool.
      destruct Htrans as [[Htrans Hpred] | Hunch].
      (* The uni/hom case *)
      + rewrite Hteq1 in HIn. rewrite Hteq2 in HIn'.
        eapply in_pred_exists in HIn; try eassumption; [|setoid_rewrite <-Hteq1; exact (proj2_sig t)].
        eapply in_pred_exists in HIn'; try eassumption;[|setoid_rewrite <-Hteq2; exact (proj2_sig t')].
        destruct HIn as [q [j [r [HIn Hstep]]]].
        destruct HIn' as [q' [j' [r' [HIn' Hstep']]]].
        assert (q ∈ (preds p)) as Hqpred
            by (eapply in_preds;eauto using step_conf_implies_edge,root_no_pred').

        eapply prefix_in_list in HIn as Hpre1. destruct Hpre1 as [l1 Hpre1].
        eapply prefix_in_list in HIn' as Hpre2. destruct Hpre2 as  [l2 Hpre2].
        
        rewrite nlcons_to_list in Hpre1.
        eapply prefix_trace in Hpre1 as Htr1 ; [|eapply root_no_pred'|destruct t1; eauto].

        rewrite nlcons_to_list in Hpre2.
        eapply prefix_trace in Hpre2 as Htr2; [|eapply root_no_pred'|destruct t2;eauto].
        simpl_nl' Hpre1. simpl_nl' Hpre2.
        cut (q' = q); intros; subst.
        * cut (j' = j); intros; subst.
          -- eapply (local_uni_corr (uni q) q j p i r r' s s'); try eassumption.
             ** unfold uni_state_concr. intros.
                unfold uni_concr in HCuni .
                eapply (HCuni _ _ Hts1 Hts2 x0 q j); eassumption.
             ** eapply join_andb_true_iff in Hpred; try eassumption.
          -- eapply uni_same_tag;eauto.
             1,2: econstructor;eauto;simpl_nl;eauto.
        * clear HCunch HCunch'.
          eapply uni_same_lab with (t1:=t1) (t2:=t2); eauto.
          1,2: econstructor;eauto;simpl_nl;eauto.
      (* The unch case *)
      + rename Hunch into H.
        eapply join_orb_true_iff in H.
        destruct H as [u H].
        conv_bool.
        destruct H as [Hunch [[Hneq' Huni] Hunibr]].
        specialize (HCunch p i s u x HIn Hunch).
        specialize (HCunch' p i s' u x HIn' Hunch).
        destruct HCunch as [j [r [Hprec Heq]]]; try eassumption.
        destruct HCunch' as [j' [r' [Hprec' Heq']]]; try eassumption.
        rewrite <- Heq. rewrite <- Heq'.
        cut (j = j'); intros.
        * subst j'. eapply HCuni. eapply Hts1. eapply Hts2. 3: eauto.
          all: eapply precedes_step_inv.
          -- rewrite <-nlcons_to_list. setoid_rewrite Hteq1 in Hprec. apply Hprec.
          -- rewrite <-nlcons_necons, <-Hteq1. destruct t; eauto.
          -- cbn. eauto.
          -- rewrite <-nlcons_to_list. setoid_rewrite Hteq2 in Hprec'. apply Hprec'.
          -- rewrite <-nlcons_necons, <-Hteq2. destruct t'; eauto.
          -- cbn;eauto.
        * unfold Precedes' in Hprec,Hprec'. destructH' Hprec. destructH' Hprec'.
          rewrite nlcons_to_list in Hprec0.
          eapply prefix_trace in Hprec0 as Htr1 ; [|eapply root_no_pred'|destruct t; eauto].
          rewrite nlcons_to_list in Hprec'0.
          eapply prefix_trace in Hprec'0 as Htr2; [|eapply root_no_pred'|destruct t';eauto].
          rewrite Hteq1 in Hprec0. simpl_nl' Hprec0. eapply prefix_cons_cons in Hprec0.
          rewrite Hteq2 in Hprec'0. simpl_nl' Hprec'0. eapply prefix_cons_cons in Hprec'0.
          eapply unch_same_tag with (l1:=l') ;eauto;[inversion Hprec1|inversion Hprec'1].
          all:subst;eauto;congruence.
  Qed.
  End uniana.

End Uniana.
