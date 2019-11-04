Require Export CFGdef CFGTac.


Section cfg.
  Context `{C : redCFG}.

  Notation "p '-a>b' q" := (a_edge p q) (at level 55).
  Notation "p '-a>' q" := (p -a>b q = true) (at level 55).
  Notation "p '-->b' q" := (edge p q) (at level 55).
  Notation "p '-->' q" := (p -->b q = true) (at level 55, right associativity).

  (** about loops **)
  
  Lemma loop_contains_loop_head (qh q : Lab)
    : loop_contains qh q -> loop_head qh.
  Proof.
    intro Q. unfold loop_head, loop_contains in *. destruct Q as [p [_ [Q _]]].
    eexists; eauto.
  Qed.

  Lemma loop_contains_self h : loop_head h -> loop_contains h h.
  Proof.
    intros Hl. unfold loop_contains.
    - unfold loop_head in Hl. destruct Hl. 
      eapply loop_head_dom in H as Hdom.
      eapply back_edge_incl in H as Hreach. specialize (a_reachability x) as Hreach'.
      destructH.
      eapply subgraph_path' in Hreach' as Hreach'';eauto using a_edge_incl.
      eapply Hdom in Hreach''. eapply path_from_elem in Hreach''; eauto.
      destructH; eauto.
      eapply path_NoDup' in Hreach''0;eauto. 
      destructH. exists x, π0. firstorder;eauto.
      + eapply subgraph_path';eauto using a_edge_incl.
      + eapply NoDup_rev in Hreach''3. eapply path_back in Hreach''2.
        remember (rev π0) as l.
        destruct l;cbn in *;eauto.
        specialize (ne_list_nlrcons π0) as Heql'. destructH. subst π0. cbn in *. simpl_nl' Heql.
        rewrite rev_rcons in Heql. inversion Heql;subst e l.
        simpl_nl' Hreach''2. subst. inversion Hreach''3;subst. auto.
  Qed.

  (** about dominance and more about loops **)

  Lemma dom_loop h
    : forall q: Lab, loop_contains h q -> Dom edge root h q.
  Proof.
    intros q Hq. unfold loop_contains,CPath in *. intros π Hπ.
    destructH. 
    eapply nin_tl_iff in Hq3;eauto.
    erewrite path_back in Hq3;eauto.
    eapply path_app in Hq2; eauto.
    eapply loop_head_dom in Hq2;eauto. eapply in_nl_conc in Hq2.
    destruct Hq3;[|subst h;eapply path_front in Hπ; subst q; destruct π;cbn;eauto].
    destruct Hq2;[contradiction|]. clear - H0. destruct π; cbn in *; eauto.
  Qed.
  
  Lemma dom_dom_acyclic r p q
    : Dom edge r p q -> Dom a_edge r p q.
  Proof.
    intros. unfold Dom in *. intros. apply H. eapply subgraph_path'; eauto using a_edge_incl.
  Qed.

  Instance loop_contains_Antisymmetric : Antisymmetric Lab eq loop_contains.
  Proof.
    unfold Antisymmetric.
    intros.
    specialize (a_reachability x) as Hx.
    specialize (a_reachability y) as Hy.
    destructH. destructH.
    eapply dom_loop in H. eapply dom_loop in H0.
    eapply dom_dom_acyclic in H. eapply dom_dom_acyclic in H0.
    eapply H in Hy as Hy'. eapply H0 in Hx as Hx'.
    eapply path_from_elem in Hy;eauto.
    eapply path_from_elem in Hx;eauto.
    do 2 destructH.
    eapply path_path_acyclic';eauto using a_edge_acyclic.
  Qed.

  Lemma loop_contains_ledge_path
        (p qh : Lab)
        (Hledge : p ↪ qh)
        (q : Lab)
        (π : ne_list Lab)
        (Hpath : Path edge q p π)
        (Hnin : qh ∉ tl (rev π))
        (x : Lab)
        (Hin : x ∈ π)
    : loop_contains qh x.
  Proof.
    unfold loop_contains.
    exists p. specialize (@path_from_elem _ edge _ q p x) as Hx. exploit Hx. destructH.
    exists ϕ. repeat (split;eauto). contradict Hnin. clear - Hx1 Hnin.
    induction Hx1; cbn in *;[auto|]. rewrite rev_rcons. cbn. eapply IHHx1 in Hnin.
    eapply tl_incl;auto.
  Qed.
  
  Lemma loop_contains_trans h h' p
        (Hloop : loop_contains h h')
        (Hloop' : loop_contains h' p)
    : loop_contains h p.
  Proof.
    copy Hloop Hloop_save.
    unfold loop_contains in Hloop,Hloop'.
    decide (h = h');[subst;eauto|].
    destructH' Hloop'. destructH' Hloop.
    exists p1. specialize (@path_app _ edge (h' :<: π) π0 p h' p1) as Hϕ.
    exploit Hϕ.
    - econstructor;eauto. eapply minus_subgraph. eauto.
    - eexists;split;eauto;split;eauto. intro N.
      specialize (ne_list_nlrcons π) as Hπ. destructH. rewrite Hπ in N. cbn in N. simpl_nl' N.
      rewrite <-nlconc_to_list in N. unfold rcons in N. rewrite app_assoc in N.
      rewrite rev_unit in N. cbn in N. eapply in_rev in N.
      eapply in_app_iff in N. destruct N.
      + eapply Hloop3. rewrite in_rev in H. clear - H n Hloop2. remember (rev π0) as l.
        destruct l; eauto. cbn. destruct H;subst;eauto. eapply path_back in Hloop2.
        specialize (ne_list_nlrcons π0) as Hπ0. destructH. rewrite Hπ0 in Heql.
        simpl_nl' Heql. rewrite rev_rcons in Heql. inversion Heql;subst. simpl_nl' n. contradiction.
      + assert (h ∈ π).
        { rewrite Hπ. simpl_nl. eapply In_rcons. right. auto. }
        eapply loop_contains_ledge_path in H0;eauto.
        eapply loop_contains_Antisymmetric in Hloop_save. exploit Hloop_save. contradiction.
  Qed.
  
  Lemma loop_reachs_member (h q : Lab)
    : loop_contains h q -> h -a>* q.
  Proof.
    intros Hloop. cbn.
    specialize (a_reachability q) as Hπ. destructH.
    eapply dom_loop in Hloop. eapply dom_dom_acyclic in Hloop.
    eapply Hloop in Hπ as Hin.
    eapply path_from_elem in Hπ;eauto. destructH.
    eexists;eauto.
  Qed.

  (*
  Lemma edge_head_same_loop (* unused *)p h h'
        (Hedge : edge p h = true)
        (Hhead : loop_head h)
        (Hloop : loop_contains h' p)
    : loop_contains h' h.
  Proof.
    eapply no_exit_head in Hhead;[contradiction|].
   *)
  
  Lemma root_loop_root h
    : loop_contains h root -> h = root.
  Proof.
    intros H.
    eapply dom_loop in H.
    assert (Path edge root root (ne_single root)) as Hpath;[econstructor|].
    eapply H in Hpath. destruct Hpath;[subst;auto|contradiction].
  Qed.
  
  Lemma loop_contains_either h1 h2 p
        (Hloo : loop_contains h1 p)
        (Hlop : loop_contains h2 p)
    : loop_contains h1 h2 \/ loop_contains h2 h1.
  Proof.
    specialize (a_reachability p) as Hr. destructH.
    eapply dom_loop in Hloo as Hdom1. eapply dom_dom_acyclic in Hdom1. eapply Hdom1 in Hr as Hr1. 
    eapply dom_loop in Hlop as Hdom2. eapply dom_dom_acyclic in Hdom2. eapply Hdom2 in Hr as Hr2.
    eapply path_from_elem in Hr1;eauto.
    eapply path_from_elem in Hr2;eauto.
    do 2 destructH.
    decide (h1 = p);[subst;right;auto|].
    decide (h2 = p);[subst;left ;auto|].
    decide (h1 = h2);[subst;left;eauto using loop_contains_self,loop_contains_loop_head|].
    eapply postfix_order_destruct in Hr4;eauto.
    destruct Hr4.
    - left. unfold loop_contains in *. do 2 destructH.
      exists p1. eapply path_app in Hloo2 as Happ;eauto. exists (π1 :+ tl ϕ).
      repeat (split;eauto). 2:eauto using subgraph_path',a_edge_incl.
      enough (h1 ∉ tl ϕ).
      + contradict Hloo3. eapply tl_incl in Hloo3. eapply in_rev in Hloo3.
        eapply in_nl_conc in Hloo3. destruct Hloo3;[|contradiction].
        destr_r π1. simpl_nl. rewrite rev_rcons. cbn. rewrite <-in_rev.
        simpl_nl' H1. eapply In_rcons in H1. destruct H1;[|auto]. subst a.
        clear - Hloo2 n.
        exfalso. contradict n. revert dependent p1.
        induction l;cbn in *;intros;inversion Hloo2;subst;auto.
        eapply IHl;eauto.
      + eapply path_back in Hr2 as Hr2'.
        eapply path_back in Hr0 as Hr0'.
        destr_r ϕ0. cbn in Hr2'. simpl_nl' Hr2'. subst a.
        destr_r ϕ. cbn in Hr0'. simpl_nl' Hr0'. subst a.
        simpl_nl' H. simpl_nl.
        eapply acyclic_path_NoDup in Hr2. simpl_nl' Hr2. eapply NoDup_rev in Hr2.
        inversion H;subst.
        * eapply rev_rev_eq in H2;repeat rewrite rev_rcons in H2. inversion H2;subst. contradiction.
        * eapply rev_rev_eq in H0;repeat rewrite rev_rcons in H0. inversion H0;subst.
          eapply rev_rev_eq in H4. subst l'.
          intro N. eapply tl_incl in N. eapply postfix_incl in N;[|eauto].
          rewrite rev_rcons in Hr2. inversion Hr2;subst. eapply in_rev in N; contradiction.
    - right. unfold loop_contains in *. do 2 destructH.
      exists p0. eapply path_app in Hlop2 as Happ;eauto. 2: clear Hr0;eauto using subgraph_path',a_edge_incl.
      exists (π0 :+ tl ϕ0).
      repeat (split;eauto). 
      enough (h2 ∉ tl ϕ0).
      + contradict Hlop3. eapply tl_incl in Hlop3. eapply in_rev in Hlop3.
        eapply in_nl_conc in Hlop3. destruct Hlop3;[|contradiction].
        destr_r π0. simpl_nl. rewrite rev_rcons. cbn. rewrite <-in_rev.
        simpl_nl' H1. eapply In_rcons in H1. destruct H1;[|auto]. subst a.
        clear - Hlop2 n0.
        exfalso. contradict n0. revert dependent p0.
        induction l;cbn in *;intros;inversion Hlop2;subst;auto.
        eapply IHl;eauto.
      + eapply path_back in Hr2 as Hr2'.
        eapply path_back in Hr0 as Hr0'.
        destr_r ϕ0. cbn in Hr2'. simpl_nl' Hr2'. subst a.
        destr_r ϕ. cbn in Hr0'. simpl_nl' Hr0'. subst a.
        simpl_nl' H. simpl_nl.
        eapply acyclic_path_NoDup in Hr0. simpl_nl' Hr0. eapply NoDup_rev in Hr0.
        inversion H;subst.
        * eapply rev_rev_eq in H2;repeat rewrite rev_rcons in H2. inversion H2;subst. contradiction.
        * eapply rev_rev_eq in H0;repeat rewrite rev_rcons in H0. inversion H0;subst.
          eapply rev_rev_eq in H4. subst l'.
          intro N. eapply tl_incl in N. eapply postfix_incl in N;[|eauto].
          rewrite rev_rcons in Hr0. inversion Hr0;subst. eapply in_rev in N; contradiction.
  Qed.
  
  Lemma dom_path (* unused *)p q
    : Dom edge root p q -> p -->* q.
  Proof.
    intros Hdom.
    specialize reachability as [π Hπ]. specialize (Hdom π Hπ).
    eapply path_from_elem in Hπ; eauto using Lab_dec. firstorder.
  Qed.

  Lemma loop_contains_not_dom (* unused *)h q 
    : loop_contains h q -> h <> q -> exists p, p ↪ h /\ ~ Dom edge q h p.
  Proof.
    intros Hloop Hneq. unfold loop_contains in Hloop. destructH.
    unfold Dom; eexists; firstorder; eauto.
    intros H0.
    eapply nin_tl_iff in Hloop3;eauto. erewrite path_back in Hloop3;eauto.
    destruct Hloop3;[|subst q;contradiction]. apply H,H0. eauto.
  Qed.
  
  Lemma not_and_iff (A B : Prop) : decidable A -> (~ (A /\ B) <-> ~ A \/ ~ B).
  Proof.
    firstorder.
  Qed.

  Lemma in_tl_in {A : Type} (a : A) (l : list A) : a ∈ tl l -> a ∈ l.
  Proof.
    destruct l; cbn in *; eauto.
  Qed.
  
  Lemma dom_loop_contains h p q
    : loop_contains h q -> ~ loop_contains h p -> Dom edge p h q.
  Proof.
    intros Hloop Hnloop.
    decide (p = q); [subst;contradiction|].
    unfold loop_contains in Hloop. destructH.
    eapply nin_tl_iff in Hloop3;eauto; erewrite path_back in Hloop3;eauto.
    destruct Hloop3 as [Hloop3|Hloop3];[|subst q;eapply dominant_self]. rename π into π1.
    intros π Hπ.
(*    assert (p ∈ all_lab) as H0 by (eapply path_in_alllab1;eauto).*)
    specialize reachability as Hϕ.
    unfold loop_contains in Hnloop.
    rewrite DM_not_exists in Hnloop. setoid_rewrite DM_not_exists in Hnloop.
    eapply path_app in Hloop2;eauto.
    specialize (Hnloop p0 (π1 :+ tl π)).
    setoid_rewrite not_and_iff in Hnloop; [setoid_rewrite not_and_iff in Hnloop|].
    - destruct Hnloop as [Hnloop|Hnloop]; [contradiction|destruct Hnloop].
      + contradiction.
      + clear - Hloop3 H.
        eapply not_not in H.
        * eapply in_tl_in in H. eapply in_rev in H. eapply in_nl_conc in H. destruct H;[contradiction|].
          eapply in_tl_in;eauto.
        * eapply In_dec;eauto.
    - edestruct path_dec;eauto; firstorder.
    - edestruct (back_edge_dec p0 h); firstorder.
      Unshelve. all:eauto. (*TODO: remove *)
  Qed.
    Lemma loop_contains_path (* unused *)h q π
    : CPath h q π -> loop_contains h q -> NoDup π -> forall p, p ∈ π -> loop_contains h p.
  Proof.
    intros Hπ Hin Hnd p Hp. 
    decide (p = h) as [Hph|Hph].
    - rewrite Hph. eapply loop_contains_self. eapply loop_contains_loop_head; eauto.
    - destruct (loop_contains_dec h p) as [N|N]; [eauto|exfalso].
      eapply path_from_elem in Hp; eauto. destructH.
      eapply dom_loop_contains in N; eauto; cycle 1.
      eapply postfix_incl in Hp1 as Hp1'; eauto.
      dependent induction Hp1.
      + simpl_nl' x. subst ϕ. 
        eapply Hph. eapply path_back in Hp0; eapply path_back in Hπ. rewrite <-Hp0. eauto.
      + clear IHHp1. unfold Dom in N.
        eapply postfix_incl in Hp1. eapply Hp1 in N; eauto.
        rewrite rcons_nl_rcons in x. eapply ne_to_list_inj in x. rewrite <-x in Hnd.
        eapply f_equal with (f:=@ne_back Lab) in x. simpl_nl' x. eapply path_back in Hπ. rewrite Hπ in x.
        subst a.
        eapply NoDup_nin_rcons; eauto. rewrite rcons_nl_rcons. assumption.
  Qed.

  Lemma loop_contains_splinter h1 h2 p π
        (Hloop1 : loop_contains h1 h2)
        (Hloop2 : loop_contains h2 p)
        (Hpath : Path edge root p π)
    : h2 ≻* h1 | π.
  Proof.
    eapply dom_loop in Hloop2. eapply Hloop2 in Hpath as Hin.
    eapply path_to_elem in Hin;eauto. destructH.
    eapply splinter_prefix;eauto.
    inversion Hin0;subst h2 a.
    - eapply dom_loop in Hloop1. eapply Hloop1 in Hin0. rewrite <-H1 in Hin0. inversion Hin0;subst;[|contradiction].
      econstructor. econstructor. econstructor. econstructor.
    - cbn in *. econstructor. eapply dom_loop in Hloop1. eapply Hloop1 in Hin0. rewrite <-H3 in Hin0.
      eapply splinter_single. cbn in *; eauto.
  Qed.

  (** * preds **)

  Definition preds `{redCFG Lab edge} p : list Lab := filter (decPred_bool (fun q => edge q p)) (elem Lab). 

  Lemma preds_in_same_loop h p q
        (Hl : loop_contains h p)
        (Hneq : h <> p)
        (Hedge : q --> p)
    : loop_contains h q.
  Proof.
    unfold loop_contains in Hl.
    destructH.
    eapply path_rcons in Hl2 as Hl2';eauto.
    exists p0, (π :>: q). repeat (split;eauto).
    simpl_nl. rewrite rev_rcons. cbn. eapply nin_tl_iff in Hl3;auto.
    destruct Hl3 as [Hl3|Hl3];[contradict Hl3;eapply in_rev;auto|eapply path_back in Hl2;subst;auto].
  Qed.

  (** * other facts **)

  Lemma exit_a_edge h p q
        (Hexit : exit_edge h p q)
    : a_edge p q = true.
  Proof.
    destruct (a_edge p q) eqn:E;[auto|exfalso].
    eapply no_exit_head;eauto.
    unfold exit_edge in Hexit. destructH.
    exists p. unfold back_edge, back_edge_b. unfold_edge_op. split; auto.
    rewrite negb_true_iff; auto.
  Qed.
  
  Lemma acyclic_path_stays_in_loop (h p q : Lab) π
        (Hpath : Path a_edge p q π)
        (Hp : loop_contains h p)
        (Hq : loop_contains h q)
    : forall x, x ∈ π -> loop_contains h x.
  Proof.
    enough (h ∉ tl (rev π)) as Hnin.
    - intros.
      eapply subgraph_path' in Hpath;eauto.
      eapply (path_from_elem) in Hpath as Hϕ;eauto. destructH.
      unfold loop_contains in Hq.
      destructH.
      exists p0, (π0 :+ tl ϕ); split_conj; auto.
      + eapply path_app;eauto.
      + destruct ϕ;cbn;[auto|].
        assert (e = q) by (clear - Hϕ0; inversion Hϕ0; subst; eauto);subst.
        rewrite <-nlconc_neconc.
        rewrite <-neconc_app. rewrite rev_app_distr.
        replace (tl (rev ϕ ++ rev π0)) with ((tl (rev ϕ)) ++ rev π0).
        * intro N. eapply in_app_or in N.
          destruct N.
          -- apply Hnin. clear - Hϕ1 H0. destruct (ne_list_nlrcons π). destructH. subst. simpl_nl' Hϕ1. simpl_nl.
             rewrite rev_rcons. cbn.
             eapply postfix_rev_prefix in Hϕ1. rewrite rev_rcons in Hϕ1.
             destruct (ne_list_nlrcons ϕ). destructH;subst. simpl_nl' Hϕ1.
             rewrite nl_cons_lr_shift in Hϕ1. simpl_nl' Hϕ1. rewrite rev_rcons in Hϕ1.
             simpl_nl' H0. rewrite rev_rcons in H0. cbn in H0.
             eapply prefix_cons_cons in Hϕ1.
             eapply prefix_incl in Hϕ1. eapply in_rev in H0. 
             specialize (Hϕ1 h). eapply Hϕ1.
             rewrite <-in_rev. right;auto.
          -- eapply nin_tl_iff in Hq3;auto. destruct Hq3 as [Hq3|Hq3]; [eapply Hq3;eapply in_rev;auto|].
             eapply path_back in Hq2. rewrite Hq2 in Hq3. subst h.
             eapply Hnin. clear - Hϕ1.
             destruct (ne_list_nlrcons π). destructH. rewrite H. simpl_nl. rewrite rev_rcons. cbn.
             rewrite H in Hϕ1. simpl_nl' Hϕ1.
             destruct l';[exfalso|];inversion Hϕ1; subst; cbn in *; try congruence'.
             destruct l'; cbn in *. inversion H2. 1,2: destruct l'; cbn in *; congruence.
             ++ eapply in_or_app. right;firstorder.
             ++ eapply postfix_hd_eq in Hϕ1. subst. eapply in_or_app. firstorder.
        * clear. destruct (ne_list_nlrcons ϕ). destructH. rewrite H. simpl_nl. rewrite rev_rcons. cbn. reflexivity.
    - intro N.
      specialize (a_reachability p) as [ϕ Hϕ].
      eapply dom_loop in Hp.
      eapply dom_dom_acyclic in Hp.
      eapply Hp in Hϕ as Hin.
      eapply path_app in Hpath as Hpath';eauto.
      eapply acyclic_path_NoDup in Hpath' as Hnd. rewrite <-nlconc_to_list in Hnd.
      enough (π ++ tl ϕ = rev (tl (rev π)) ++ ϕ).
      + rewrite H in Hnd.
        eapply NoDup_app;eauto.
        rewrite <-in_rev. auto.
      + clear - Hpath Hϕ.
        destruct (ne_list_nlrcons π). destructH. subst.
        simpl_nl. rewrite rev_rcons. cbn. rewrite rev_involutive.
        eapply path_back in Hpath. simpl_nl' Hpath. subst x.
        destruct ϕ;cbn in *;simpl_nl.
        * inversion Hϕ; subst. rewrite app_nil_r. reflexivity.
        * inversion Hϕ; subst. unfold rcons. rewrite <-app_assoc. cbn. reflexivity.
  Qed.

  Lemma acyclic_parallel_exit_path h p q π
        (Hπ : Path a_edge h q π)
        (Hexit : exit_edge h p q)
    : forall x, x ∈ tl π -> loop_contains h x.
  Proof.
    destruct π;cbn in *;[contradiction|].
    assert (e = q) by (inversion Hπ;cbn in *;subst;auto);subst.
    inversion Hπ;subst.
    intros.
    eapply acyclic_path_stays_in_loop;eauto.
    - eapply loop_contains_self;unfold exit_edge in Hexit; destructH ;eauto using loop_contains_loop_head.
    - eapply exit_pred_loop;eauto.
      eapply a_edge_incl;eauto.
  Qed.

  Lemma loop_contains_ledge qh ql
    : ql ↪ qh -> loop_contains qh ql.
  Proof.
    intros. exists ql, (ne_single ql). split_conj;[auto|constructor|cbn]. exact (fun x => x).
  Qed.
  
  Lemma exit_edge_pred_exiting h p q
        (Hexit : exit_edge h p q)
        (p' : Lab)
        (Hedge : edge p' q = true)
    : exit_edge h p' q.
  Proof.
    copy Hexit Hexit'.
    unfold exit_edge; unfold exit_edge in Hexit. destructH.
    split_conj;eauto.
    eapply exit_pred_loop;eauto.
  Qed.
  
  Lemma root_no_acyclic_pred p
    : a_edge p root <> true.
  Proof.
    specialize (a_reachability p) as [π Hπ].
    intro. eapply a_edge_acyclic;eauto.
  Qed.
  
  Lemma exit_edge_acyclic h qe e
        (Hexit : exit_edge h qe e)
    : a_edge qe e = true.
  Proof.
    copy Hexit Hexit'.
    unfold exit_edge in Hexit.
    destructH.
    destruct (a_edge qe e) eqn:E;[auto|exfalso].
    eapply no_exit_head;eauto.
    eexists; unfold back_edge,back_edge_b; unfold_edge_op.
    split;eauto. eapply negb_true_iff. auto.
  Qed.

  Lemma exit_edge_unique_diff_head h qe e
        (Hexit : exit_edge h qe e)
        h'
        (Hloop : loop_contains h' h)
        (Hnloop : ~ loop_contains h' e)
    : h' = h.
  Proof.
    specialize (a_reachability e) as [π Hπ].
    inversion Hπ;subst e a.
    - exfalso. subst π.
      eapply exit_edge_acyclic in Hexit. exfalso. eapply root_no_acyclic_pred;eauto.
    - eapply a_edge_incl in H0. eapply exit_pred_loop in H0 as H2;eauto.
      eapply single_exit with (p:=b) (q:=c).
      + split;[|split];eauto.
        eapply loop_contains_trans;eauto.
      + split;[|split];eauto.
        contradict Hnloop. eapply loop_contains_trans;eauto.
  Qed.
  
  Lemma exit_edge_in_loop (* unused *) (h1 h2 p2 e2 : Lab)
        (Hexit' : exit_edge h2 p2 e2)
        (Hloop : loop_contains h1 h2)
        (Hneq : h1 <> h2)
    : loop_contains h1 e2.
    decide (loop_contains h1 e2);[auto|].
    copy Hexit' Hexit''.
    unfold exit_edge in Hexit'. destructH.
    assert (exit_edge h1 p2 e2).
    {
      unfold exit_edge. split_conj;cycle 1.
      + eauto.
      + eauto.
      + eauto using loop_contains_trans.
    }
    eapply single_exit in Hexit'';eauto. contradiction.
  Qed.
  
  Lemma entry_through_header h p q
        (Hnin : ~ loop_contains h p)
        (Hin : loop_contains h q)
        (Hedge : p --> q)
    : q = h.
  Proof.
    specialize (a_reachability p) as Hreach. destructH.
    eapply path_front in Hreach as Hfront.
    eapply subgraph_path' in Hreach as Hreach'. 2: eapply a_edge_incl.
    eapply PathCons in Hreach';eauto.
    eapply dom_loop in Hreach' as Hdom;eauto.
    cbn in Hdom. decide (q = h);destruct Hdom;auto;try contradiction.
    exfalso.
    contradict Hnin.
    unfold loop_contains in *. destructH.
    eapply path_rcons in Hedge;eauto.
    exists p0. eexists. split_conj;eauto.
    simpl_nl. eapply nin_tl_iff in Hin3;eauto.
    destruct Hin3.
    - simpl_nl. rewrite rev_rcons. cbn. rewrite <-in_rev. auto.
    - eapply path_back in Hin2. rewrite Hin2 in H0. symmetry in H0. contradiction.
  Qed.

End cfg.
