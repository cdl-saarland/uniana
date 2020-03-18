Require Export CFGdef CFGTac.


Section cfg.
  Context `{C : redCFG}.

  Notation "p '-a>b' q" := (a_edge p q) (at level 55).
  Notation "p '-a>' q" := (p -a>b q = true) (at level 55).
  Notation "p '-->b' q" := (edge p q) (at level 55).
  Notation "p '-->' q" := (p -->b q = true) (at level 55, right associativity).

  (** * Basic loop facts **)
  
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
      + eapply NoDup_rev in Hreach''3. 
        remember (rev π0) as l.
        destruct l;cbn in *;eauto.
        assert (π0 = rev l ++ [e]).
        { rewrite rev_rev_eq. rewrite rev_rcons. rewrite rev_involutive. eauto. }
        rewrite H1 in Hreach''2. eapply path_back in Hreach''2. subst.
        inversion Hreach''3. subst. assumption.
  Qed.

  (** ** Facts about dominance and loops **)

  Lemma dom_loop h
    : forall q: Lab, loop_contains h q -> Dom edge__P root h q.
  Proof.
    intros q Hq. unfold loop_contains,CPath in *. intros π Hπ.
    destructH. 
    eapply nin_tl_iff in Hq3;eauto.
    destruct Hq3.
    - eapply path_app' in Hq2. 2: eapply Hπ.
      eapply loop_head_dom in Hq2. 2:eauto. eapply in_app_or in Hq2.
      destruct Hq2;[contradiction|]. eapply tl_incl;auto.
    - eapply path_contains_front in Hπ. enough (h = q);[subst;eauto|].
      destr_r' π0;cbn in *;subst.
      + inversion Hq2.
      + rewrite rev_rcons in H. cbn in H. inversion H. subst. path_simpl'  Hq2. reflexivity.
  Qed.
  
  Lemma dom_dom_acyclic r p q
    : Dom edge__P r p q -> Dom a_edge__P r p q.
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
        (π : list Lab)
        (Hpath : Path edge__P q p π)
        (Hnin : qh ∉ tl (rev π))
        (x : Lab)
        (Hin : x ∈ π)
    : loop_contains qh x.
  Proof.
    unfold loop_contains.
    exists p. specialize (@path_from_elem _ edge__P _ q p x) as Hx. exploit Hx. destructH.
    exists ϕ. repeat (split;eauto). contradict Hnin. clear - Hx1 Hnin.
    induction Hx1; cbn in *;[auto|]. rewrite rev_rcons. cbn. eapply IHHx1 in Hnin.
    eapply tl_incl;auto.
  Qed.

  (** ** Transitivity of loop_contains **)
  
  Lemma loop_contains_trans h h' p
        (Hloop : loop_contains h h')
        (Hloop' : loop_contains h' p)
    : loop_contains h p.
  Proof.
    copy Hloop Hloop_save.
    unfold loop_contains in Hloop,Hloop'.
    decide (h = h');[subst;eauto|].
    destructH' Hloop'. destructH' Hloop.
    exists p1. specialize (path_app Hloop'2 (back_edge_incl Hloop'0) Hloop2) as Hϕ.
    exists (π0 ++ π);split;eauto;split;eauto. intro N.    
    cbn in *. rewrite rev_app_distr in N.
    destr_r' π;subst;cbn in *. 1: inversion Hloop'2.
    rewrite rev_rcons in N. cbn in N.
    eapply in_app_or in N. destruct N.
    - eapply loop_contains_ledge_path in Hloop'3. 2,3: eauto.
      + eapply loop_contains_Antisymmetric in Hloop_save. eapply Hloop_save in Hloop'3. contradiction.
      + eapply In_rcons. right. eapply in_rev. auto.
    - destr_r' π0;subst;cbn in *;[contradiction|].
      rewrite rev_rcons in H. destruct H;subst.
      + path_simpl' Hloop2. contradiction.
      + rewrite rev_rcons in Hloop3. cbn in Hloop3. contradiction.
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
  Lemma edge_head_same_loop p h h'
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
    assert (Path edge__P root root [root]) as Hpath;[econstructor|].
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
      exists p1. eapply path_app' in Hloo2 as Happ;eauto. exists (π1 ++ tl ϕ).
      repeat (split;eauto). 2:eauto using subgraph_path',a_edge_incl.
      enough (h1 ∉ tl ϕ).
      + contradict Hloo3. eapply tl_incl in Hloo3. eapply in_rev in Hloo3.
        eapply in_app_or in Hloo3. destruct Hloo3;[|contradiction].
        destr_r' π1;subst;[contradiction|]. rewrite rev_rcons. cbn. rewrite <-in_rev.
        eapply In_rcons in H1. destruct H1;[|auto]. subst x.
        clear - Hloo2 n.
        exfalso. contradict n. revert dependent p1.
        induction l;cbn in *;intros;inversion Hloo2;subst;auto.
        * inversion H3.
        * congruence'.
        * eapply IHl;eauto.
      + destr_r' ϕ0;subst. 1: inversion Hr2. 
        destr_r' ϕ;subst. 1: inversion Hr0.
        eapply path_back in Hr2 as Hr2'.
        eapply path_back in Hr0 as Hr0'. subst x x0.
        eapply acyclic_path_NoDup in Hr2. eapply NoDup_rev in Hr2.
        inversion H;subst.
        * eapply rev_rev_eq in H2;repeat rewrite rev_rcons in H2. inversion H2;subst. contradiction.
        * eapply rev_rev_eq in H0;repeat rewrite rev_rcons in H0. inversion H0;subst.
          eapply rev_rev_eq in H4. subst l'.
          intro N. eapply tl_incl in N. eapply postfix_incl in N;[|eauto].
          rewrite rev_rcons in Hr2. inversion Hr2;subst. eapply in_rev in N; contradiction.
    - right. unfold loop_contains in *. do 2 destructH.
      exists p0. eapply path_app' in Hlop2 as Happ;eauto. 2: clear Hr0;eauto using subgraph_path',a_edge_incl.
      exists (π0 ++ tl ϕ0).
      repeat (split;eauto). 
      enough (h2 ∉ tl ϕ0).
      + contradict Hlop3. eapply tl_incl in Hlop3. eapply in_rev in Hlop3.
        eapply in_app_or in Hlop3. destruct Hlop3;[|contradiction].
        destr_r' π0;subst. 1: inversion Hlop2. rewrite rev_rcons. cbn. rewrite <-in_rev.
        eapply In_rcons in H1. destruct H1;[|auto]. subst x.
        clear - Hlop2 n0.
        exfalso. contradict n0. revert dependent p0.
        induction l;cbn in *;intros;inversion Hlop2;subst;auto.
        * inversion H3.
        * congruence'.        
        * eapply IHl;eauto.
      + destr_r' ϕ0;subst. 1:inversion Hr2.
        destr_r' ϕ;subst. 1: inversion Hr0.
        eapply path_back in Hr2 as Hr2'.
        eapply path_back in Hr0 as Hr0'. subst x x0.
        eapply acyclic_path_NoDup in Hr0. eapply NoDup_rev in Hr0.
        inversion H;subst.
        * eapply rev_rev_eq in H2;repeat rewrite rev_rcons in H2. inversion H2;subst. contradiction.
        * eapply rev_rev_eq in H0;repeat rewrite rev_rcons in H0. inversion H0;subst.
          eapply rev_rev_eq in H4. subst l'.
          intro N. eapply tl_incl in N. eapply postfix_incl in N;[|eauto].
          rewrite rev_rcons in Hr0. inversion Hr0;subst. eapply in_rev in N; contradiction.
  Qed.
  
  Lemma dom_path p q
    : Dom edge__P root p q -> p -->* q.
  Proof.
    intros Hdom.
    specialize reachability as [π Hπ]. specialize (Hdom π Hπ).
    eapply path_from_elem in Hπ; eauto using Lab_dec. firstorder.
  Qed.

  Lemma back_edge_no_a_edge p q
    : p ↪ q -> ~ a_edge__P p q.
  Proof.
    intros Hbedge Haedge.
    specialize (a_reachability p) as Hreach.
    destructH.
    eapply loop_head_dom in Hbedge.
    eapply dom_dom_acyclic in Hbedge.
    specialize (Hbedge _ Hreach).
    eapply PathCons in Haedge;eauto.
    eapply acyclic_path_NoDup in Haedge.
    inversion Haedge. subst.
    contradiction.
  Qed.

  Lemma loop_contains_not_dom h q 
    : loop_contains h q -> h <> q -> exists p, p ↪ h /\ ~ Dom edge__P q h p.
  Proof.
    intros Hloop Hneq. unfold loop_contains in Hloop. destructH.
    unfold Dom; eexists; firstorder; eauto.
    - apply back_edge_incl;eauto.
    - eapply back_edge_no_a_edge. auto.
    - eapply nin_tl_iff in Hloop3;eauto. destruct Hloop3.
      + eauto.
      + contradict Hneq. destr_r' π;subst. 1:inversion Hloop2.
        rewrite rev_rcons in H. cbn in *. inversion H. subst. path_simpl' Hloop2. reflexivity.
  Qed.
  
  Lemma not_and_iff (A B : Prop) : decidable A -> (~ (A /\ B) <-> ~ A \/ ~ B).
  Proof.
    firstorder.
  Qed.

  Lemma in_tl_in {A : Type} (a : A) (l : list A) : a ∈ tl l -> a ∈ l.
  Proof.
    destruct l; cbn in *; eauto.
  Qed.

  (* FIXME: move *)
  Lemma hd_rev_tl_rev_cons (A : Type) (l : list A) (a : A)
    : hd a (rev (tl (rev (a :: l)))) = a.
  Proof.
    clear.
    rewrite rev_cons. destr_r' l;subst;cbn;auto.
    rewrite rev_rcons. cbn.  rewrite rev_rcons. cbn. auto.
  Qed.

  (** * Path and Dominance facts **)

  Lemma path_front'
    : forall (*(L : Type) (edge : L -> L -> bool)*) (p q r : Lab) (π : list Lab),
      Path edge__P p q π -> q = hd r π.
  Proof.
    intros.
    destruct π.
    - inversion H.
    - cbn. eapply path_front;eauto.
  Qed.
  
  Lemma path_back'
    : forall (*(L : Type) (edge : L -> L -> bool)*) (p q r : Lab) (π : list Lab),
      Path edge__P p q π -> p = hd r (rev π).
  Proof.
    intros.
    destr_r' π;subst.
    - cbn in *. inversion H.
    - rewrite rev_rcons. cbn. eapply path_back;eauto.
  Qed.
  
  Lemma app_tl_switch (A : Type) (a b : A) (π ϕ : list A)
        (Heq : hd a (rev π) = hd b ϕ)
        (Hπ : π <> nil)
        (Hϕ : ϕ <> nil)
    : π ++ tl ϕ = (rev (tl (rev π))) ++ ϕ.
  Proof.
    destr_r' π;[congruence|].
    destruct ϕ;[congruence|].
    clear Hπ Hϕ. subst π. rewrite rev_rcons in Heq. cbn in Heq. subst.
    rewrite rev_rcons. cbn. rewrite rev_involutive.
    rewrite <-app_assoc. reflexivity.
  Qed.
  
  Lemma dom_loop_contains h p q
    : loop_contains h q -> ~ loop_contains h p -> Dom edge__P p h q.
  Proof.
    intros Hloop Hnloop π Hπ.
    copy Hloop Hloop'. copy Hnloop Hnloop'.
    unfold loop_contains in Hnloop. do 3 simpl_dec' Hnloop.
    assert (forall x ϕ, x ↪ h -> Path edge__P p x ϕ -> h ∈ tl (rev ϕ)) as Q.
    { clear - Hnloop.
      intros. specialize (Hnloop x ϕ). firstorder.
      decide (h ∈ tl (rev ϕ));[auto|contradiction].
    }
    clear Hnloop. 
    unfold loop_contains in Hloop. destructH.
    eapply path_app' in Hloop2 as Happ;eauto.
    erewrite app_tl_switch in Happ.
    2: { eapply path_back' in Hloop2. eapply path_front' in Hπ. rewrite <-Hπ. rewrite <-Hloop2. auto. }
    2: intro;subst;inversion Hloop2.
    2: intro;subst;inversion Hπ. 
    specialize (Q _ _ Hloop0 Happ).
    destr_r' π;subst;[inversion Hπ|subst].
    rewrite app_assoc in Q. rewrite rev_rcons in Q. cbn in Q.
    eapply in_rev in Q. eapply in_app_or in Q. destruct Q as [Q|Q];[eapply in_rev in Q;contradiction|].
    eapply In_rcons;auto.
    Unshelve. all:auto.
  Qed.
  
  Lemma loop_contains_path h q π
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
      + eapply Hph. eapply path_back_eq;eauto. 
      + clear IHHp1. unfold Dom in N.
        eapply postfix_incl in Hp1. eapply Hp1 in N; eauto.
        unfold CPath in Hπ. path_simpl' Hπ.
        eapply NoDup_nin_rcons in Hnd. contradiction.
  Qed.

  Lemma loop_contains_splinter h1 h2 p π
        (Hloop1 : loop_contains h1 h2)
        (Hloop2 : loop_contains h2 p)
        (Hpath : Path edge__P root p π)
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

  (** * Predecessors **)

  Definition preds `{redCFG Lab edge} p : list Lab
    := filter (decPred_bool (fun q => edge q p)) (elem Lab).


  Lemma preds_in_same_loop h p q
        (Hl : loop_contains h p)
        (Hneq : h <> p)
        (Hedge : q --> p)
    : loop_contains h q.
  Proof.
    unfold loop_contains in Hl.
    destructH.
    specialize (path_rcons (r:=q) Hl2) as Hl2'. exploit Hl2'.
    exists p0, (π ++ [q]). repeat (split;eauto).
    rewrite rev_rcons. cbn. eapply nin_tl_iff in Hl3;auto.
    destruct Hl3 as [Hl3|Hl3];[contradict Hl3;eapply in_rev;auto|].
    destr_r' π;subst;[inversion Hl2|]. rewrite rev_rcons in *. cbn in Hl3. path_simpl' Hl2.
    inversion Hl3. contradiction.
  Qed.

  (** * Facts about acyclic paths and exits **)

  Lemma exit_a_edge h p q
        (Hexit : exit_edge h p q)
    : a_edge p q = true.
  Proof.
    destruct (a_edge p q) eqn:E;[auto|exfalso].
    eapply no_exit_head;eauto.
    unfold exit_edge in Hexit. destructH.
    exists p. unfold back_edge. unfold_edge_op. split; auto.
    unfold a_edge__P,is_true2,is_true.
    intro N. congruence.
  Qed.
  
  Lemma acyclic_path_stays_in_loop (h p q : Lab) π
        (Hpath : Path a_edge__P p q π)
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
      exists p0, (π0 ++ tl ϕ); split_conj; auto.
      + eapply path_app';eauto.
      + destr_r' π;subst. 1: inversion Hpath.
        rename l into π.
        destr_r' π0;subst. 1: inversion Hq2.
        rename l into π0.
        destr_r' ϕ;subst. 1: inversion Hϕ0.
        rename l into ϕ.
        rewrite rev_app_distr. 
        rewrite rev_rcons in *.
        cbn in *. rewrite <-in_rev in Hq3,Hnin.
        path_simpl' Hpath. path_simpl' Hq2. path_simpl' Hϕ0.
        destruct ϕ;cbn;[rewrite <-in_rev;auto|].
        rewrite rev_rcons. cbn.
        intro N. eapply in_app_or in N. destruct N as [N|[N|N]].
        * eapply postfix_rcons_rcons in Hϕ1. eapply postfix_incl in Hϕ1.
          eapply Hnin. eapply Hϕ1. right. rewrite in_rev. auto.
        * cbn in Hϕ0. path_simpl' Hϕ0. subst.
          eapply postfix_rcons_rcons in Hϕ1.
          eapply Hnin. eapply postfix_incl;eauto.
        * rewrite <-in_rev in N. contradiction.
    - intro N.
      specialize (a_reachability p) as [ϕ Hϕ].
      eapply dom_loop in Hp.
      eapply dom_dom_acyclic in Hp.
      eapply Hp in Hϕ as Hin.
      eapply path_app' in Hpath as Hpath';eauto.
      eapply acyclic_path_NoDup in Hpath' as Hnd. 
      enough (π ++ tl ϕ = rev (tl (rev π)) ++ ϕ).
      + rewrite H in Hnd.
        eapply NoDup_app;eauto.
        rewrite <-in_rev. auto.
      + clear - Hpath Hϕ.
        destr_r' π;subst. 1: inversion Hpath. rewrite rev_rcons. cbn.
        rewrite rev_involutive.
        eapply path_back in Hpath. subst x.
        destruct ϕ;cbn in *.
        * inversion Hϕ; subst. 
        * inversion Hϕ; subst;auto. rewrite <-app_assoc. cbn. reflexivity.
          rewrite <-app_cons_assoc. auto.
  Qed.
  
  Lemma acyclic_parallel_exit_path h p q π
        (Hπ : Path a_edge__P h q π)
        (Hexit : exit_edge h p q)
    : forall x, x ∈ tl π -> loop_contains h x.
  Proof.
    destruct π;cbn in *;[contradiction|].
    assert (e = q) by (inversion Hπ;cbn in *;subst;auto);subst.
    inversion Hπ;subst. 1: intros;contradiction.
    intros.
    eapply acyclic_path_stays_in_loop;eauto.
    - eapply loop_contains_self;unfold exit_edge in Hexit; destructH ;
        eauto using loop_contains_loop_head.
    - eapply exit_pred_loop;eauto.
      eapply a_edge_incl;eauto.
  Qed.

  Lemma loop_contains_ledge qh ql
    : ql ↪ qh -> loop_contains qh ql.
  Proof.
    intros. exists ql, ([ql]). split_conj;[auto|constructor|cbn]. exact (fun x => x).
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
    eexists; unfold back_edge; unfold_edge_op.
    split;eauto.
    intro. congruence.
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
  
  Lemma exit_edge_in_loop  (h1 h2 p2 e2 : Lab)
        (Hexit' : exit_edge h2 p2 e2)
        (Hloop : loop_contains h1 h2)
        (Hneq : h1 <> h2)
    : loop_contains h1 e2.
  Proof.
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
    eapply dom_loop_contains in Hin as Hin';eauto.
    assert (Path edge__P p q (q :: [p])) as Hpath.
    1: econstructor;eauto;econstructor.
    eapply Hin' in Hpath. destruct Hpath;auto.
    inversion H;[|contradiction]. subst.
    exfalso.
    apply Hnin. eapply loop_contains_self. eauto using loop_contains_loop_head.
  Qed.
  
End cfg.
