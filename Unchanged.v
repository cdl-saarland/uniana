
Require Import Coq.Program.Utils.
Require Import Lists.ListSet.
Require Import List.

Require Util Evaluation.

Module Unchanged.
  Import Evaluation.Evaluation Util.
  Open Scope prg.

  Definition Unch := Lab -> Var -> set Lab.

  Definition unch_concr (unch : Unch) : Traces :=
    fun t => forall to i s u x, In (to, i, s) (`t) ->
                              set_In u (unch to x) ->
                              exists j r, Precedes' (`t) (u, j, r) (to, i, s) /\
                                     r x = s x.
                           
  Definition unch_join_ptw (d d' : set Lab) := set_inter Lab_dec' d d'. 

  Definition unch_join (u u' : Unch) : Unch :=
    fun l x => unch_join_ptw (u l x) (u' l x).

  Definition unch_trans_local (unch : Unch) (q p : Lab) (x : Var) : set Lab :=
    set_add Lab_dec' p (if is_def x q p then empty_set Lab else unch q x).

  Definition unch_trans_ptw (unch : Unch) l x : set Lab :=
    if Lab_dec' l root then set_add Lab_dec' root (empty_set Lab) else
    let f := fun q acc => set_inter Lab_dec' q acc in
    let t := fun q => unch_trans_local unch q l x in
    fold_right f all_lab (map t (preds l)).
      
  Definition unch_trans (unch : Unch) : Unch :=
    fun l x => unch_trans_ptw unch l x.

  Lemma unch_trans_root : forall unch x, unch_trans unch root x = set_add Lab_dec' root (empty_set Lab).
  Proof.
    intros.
    cut (preds root = nil); intros.
    + unfold unch_trans, unch_trans_ptw. 
      destruct (Lab_dec' root root); firstorder.
    + cut (forall q, ~ List.In q (preds root)); intros; eauto using list_emp_in, root_no_pred. 
  Qed.

  Inductive Front (u : Unch) : Var -> Lab -> Prop :=
    | FrontDef : forall x p, is_def_lab x p -> Front u x p
    | FrontIter : forall x l l' r r' p, l <> r ->
                                   Front u x l ->
                                   Front u x r ->
                                   l' --> p ->
                                   r' --> p ->
                                   set_In l (u l' x) ->
                                   set_In r (u r' x) ->
                                   ~ set_In l (u r' x) ->
                                   ~ set_In r (u l' x) ->
                                   Front u x p.
  
  Lemma unch_trans_lem u to x unch :
    set_In u (unch_trans unch to x) ->
    u = to \/ (forall q, List.In q (preds to) -> (is_def x q to = false /\ set_In u (unch q x))).
  Proof.
    intros.
    unfold unch_trans, unch_trans_ptw, unch_join_ptw, unch_trans_local in H.
    induction (preds to); simpl in *.
    - right. intros. inject H0.
    - destruct (Lab_dec' to root).
      + simpl in H. destruct H; [ subst | firstorder ]. eauto.
      + eapply set_inter_elim in H.
        destruct H as [Hin Hother].
        eapply IHl in Hother. clear IHl.
        inject Hother; [ eauto |].
        destruct (Lab_dec' u to); subst; eauto.
        right.
        intros.
        inject H0; [ subst | eauto].
        destruct (is_def x q to).
        * simpl in Hin. firstorder.
        * eauto using set_add_elim2.
  Qed.

(*  Lemma in_exists_pred p i s k t :
    forall tr step, proj2_sig tr = Step (`t) k (proj2_sig t) step -> In (p, i, s) tr  ->
    p <> root ->
    exists q j r, In (q, j, r) t /\ eff (q, j, r) = Some (p, i, s).
  Proof.
    intros k' step H Hneq.
    dependent induction t; inv_tr H.
    - exists root, start_tag, s0. split; [ constructor | eauto ].
    - inv_tr H4. firstorder.
    - destruct k as [[q j] r]. exists q, j, r.
      split; [ constructor | eauto ].
    - eapply IHt in H4; eauto. destruct H4 as [q [j [r [Hin Hstep]]]].
      exists q, j, r. split; [ constructor |]; eauto.
  Qed.*)


  Lemma unch_correct :
    forall unch t,
      sem_trace (unch_concr unch) t -> unch_concr (unch_trans unch) t.
  Proof.
    intros unch t Hred.
    unfold sem_trace in Hred.
    destruct Hred as [t' [k' [Hred H]]].
    unfold unch_concr in *.
    intros to i s u x.
    intros Hin Hunch.
    destruct (Lab_dec' to root); subst.
    - unfold unch_trans, unch_trans_ptw in Hunch. destruct (Lab_dec' root root); [ | firstorder ].
      simpl in Hunch. destruct Hunch; [ | firstorder ]. subst.      
      exists i, s. split; eauto. exists nil. split; [|econstructor].
      apply root_start_tag in Hin as rst. subst i.
      assert (rp := root_prefix t). destruct rp as [s' rp].
      apply prefix_cons_in in rp as rp'. eapply tag_inj in rp'; [|apply Hin].
      subst s'. assumption.
    - assert (Hpred := Hin).
      rewrite H in Hpred.
      eapply in_exists_pred in Hpred; try eassumption.
      + destruct Hpred as [q [j [r [Hpredin Hpred]]]].
        assert (Hedge: q --> to) by (eauto using step_conf_implies_edge).
        eapply unch_trans_lem in Hunch; try eassumption.
        destruct (Lab_dec' to u) as [ | Hneq ]; subst.
        * exists i, s. split; [ | reflexivity ]. eauto using precedes_self.
        * destruct Hunch; [ firstorder |].
          eapply H0 in Hedge. destruct Hedge as [Hndef Huin].
          edestruct Hred as [j' [r' [Hprec Heq]]]; eauto.
          exists j', r'. rewrite Heq.
          split; [|eauto using no_def_untouched]. rewrite H. eapply precedes_succ; eauto.        
      + clear - H. destruct t; cbn in H; inversion t; subst x.
        * congruence.
        * inversion H2. subst; eauto.
  Qed.
  


  

  (*
  Lemma unch_dom (u : Unch) x l l' :
    set_In l (u l' x) -> forall q, is_def_lab x q -> forall (π : Path q l'), PathIn l π.
  Proof.
  Admitted.

  Lemma unch_path_exist (u : Unch) x l l' r :
    set_In l (u l' x) -> ~ set_In r (u l' x) -> exists (π : Path l l'), ~ PathIn r π.
  Proof.
  Admitted.
    
  Lemma front_and_join (u : Unch) x p :
    Front u x p <-> is_def_lab x p \/ exists d d' q q' (π : Path d q) (π' : Path d' q'), is_def_lab x d /\
                                                                                 is_def_lab x d' /\
                                                                                 q --> p /\ q' --> p /\
                                                                                 DisjPaths π π'.
  Proof.
    split; intros.
    - induction H; [ left; assumption | right ].
      eapply unch_path_exist in H6; try eassumption.
      eapply unch_path_exist in H7; try eassumption.
      destruct H6 as [π Hπ], H7 as [π' Hπ'].
      specialize (unch_dom _ _ _ _ H4). intro Hdom.
      specialize (unch_dom _ _ _ _ H5). intro Hdom'.
      assert (Hdom := unch_dom _ _ _ _).
      assert (DisjPaths π π'). {
        unfold DisjPaths.
        intros q.
        split; intros.
        - 

      destruct IHFront1, IHFront2.
      + exists l, r, l', r', π, π'.
        do 4 (split; [ assumption |]).
        unfold DisjPaths.
        admit.
      + 

      assert  
      (*
      destruct IHFront1, IHFront2.
      + exists l, r, l', r'.
        eexists. eexists. 
        do 4 (split; [ assumption |]).
        admit.
      +
       *)
      admit.
    - admit.
                           
  *)

  (* Paths *)


  (*
  Section Disj.
    Variable unch : Unch.
    Variable s t f : Lab.
    Variable x xs : Var.
    Variable Hst : s --> t.
    Variable Hsf : s --> f.
    Variable Hbr : branch s = Some (t, f, x, xs).
    Variable Hfp : unch_lfp unch.

    Lemma unch_split_is_on_path dl to (p : Path f to) :
      unch to xs = Some dl ->
      PathIn dl p.
    Proof.
      intros Hunch.
      induction p.
      - rename p into f. simpl.
        assertl (Hbrspec := branch_spec_var s t f x xs Hbr).
        destruct Hbrspec as [Hl [Hr _]].
        destruct (unch_trans_res unch s f xs Hsf).
        + rewrite unch_lfp_trans_eq in H; try eassumption.
          rewrite Hunch in H. inject H. reflexivity.
        + destruct H as [_ [H _]].  rewrite H in *; firstorder.
      - rename from into f. rename p into q. simpl.
        destruct (unch_trans_res unch q to xs e).
        + rewrite unch_lfp_trans_eq in H; try eassumption.
          rewrite Hunch in H. inject H. left. reflexivity.
        + destruct H as [_ [_ [_ H]]].
          rewrite unch_lfp_trans_eq in H; try eassumption.
          rewrite H in Hunch. right. eauto.
    Qed.
    
    Lemma unch_split_exists {to} (p : Path f to) :
      exists dl, unch to xs = Some dl /\ PathIn dl p.
    Proof.
      induction p.
      - rename p into f. simpl.
        assert (Hbrspec := branch_spec_var s t f x xs Hbr).
        destruct Hbrspec as [Hl [Hr _]].
        destruct (unch_trans_res unch s f xs Hsf).
        + rewrite unch_lfp_trans_eq in H; try eassumption.
          exists f. split; [ eauto | reflexivity ].
        + destruct H as [_ [H _]]. rewrite H in *; firstorder.
      - rename from into f. rename p into q. simpl.
        destruct (unch_trans_res unch q to xs e).
        + rewrite unch_lfp_trans_eq in H; try eassumption.
          exists to. split; eauto. 
        + destruct H as [_ [_ [_ H]]].
          rewrite unch_lfp_trans_eq in H; try eassumption.
          destruct IHp as [dl [IHp Hin]]; try eassumption. rewrite IHp in H.
          exists dl. eauto. 
    Qed.

    Variable l r : Lab.

    Section PathsGiven.
      Variable a : Path t l.
      Variable b : Path f r.
  
      Lemma unch_disj_l :
        disjoint a b ->
        exists dl dr, unch l xs = Some dl /\ unch r xs = Some dr /\ dl =/= dr.
      Proof.
        intros Hdis.
        unfold disjoint in Hdis.
        destruct Hdis as [Hl Hr].
        induction a as [t | t].
        - destruct (branch_spec_var s t f x xs Hbr) as [Hdef _].
          destruct (unch_trans_res unch s t xs Hst); rewrite unch_lfp_trans_eq in H; try eassumption.
          + destruct (unch_split_exists b) as [dr [Hu Hp]].
            exists t, dr. repeat split; try eassumption.
            intro. eapply Hl. constructor. rewrite H0. assumption.
          + destruct H as [_ [H _]]. rewrite Hdef in H. firstorder.
        - rename p0 into b', p into l.
          destruct IHp; try eassumption.
          + intros. apply Hl. simpl. auto.
          + intros. apply Hr in H. contradict H. simpl. auto.
          + destruct H as [dr [Hul [Hur Hneq]]].
            destruct (unch_trans_res unch l to xs e); rewrite unch_lfp_trans_eq in H; try eassumption.
            * exists to, dr. repeat split; eauto. 
              intro. eapply (Hl to). simpl. left. reflexivity. eapply unch_split_is_on_path. auto.
              rewrite H0. eassumption.
            * destruct H as [_ [_ [_ H]]].
              rewrite H. eauto.
      Qed.

*)



End Unchanged.