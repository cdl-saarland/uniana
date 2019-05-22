
Require Import Coq.Program.Utils.
Require Import Lists.ListSet.
Require Import List.

Require Export Evaluation.

Open Scope prg.

Section unch.
  Context `{C : redCFG}.
  
  Notation "p --> q" := (edge p q = true) (at level 55,right associativity).
  
  Variable root_no_pred' : forall p, p --> root -> False.

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
      let t := fun q => unch_trans_local unch q l x in
      fold_right (set_inter Lab_dec') (elem Lab) (map t (preds l)).
  
  Definition unch_trans (unch : Unch) : Unch :=
    fun l x => unch_trans_ptw unch l x.
  
  Lemma in_preds p q : q ∈ preds p <-> q --> p.
  Proof.
    unfold preds; rewrite in_filter_iff; firstorder; cbn in *.
    - destruct (edge q p);eauto.
    - rewrite H;eauto.
  Qed.

  Lemma unch_trans_root : forall unch x, unch_trans unch root x = set_add Lab_dec' root (empty_set Lab).
  Proof.
    intros.
    cut (preds root = nil); intros.
    + unfold unch_trans, unch_trans_ptw. 
      destruct (Lab_dec' root root); firstorder.
    + cut (forall q, ~ List.In q (preds root)); intros; eauto using list_emp_in, root_no_pred'.
      rewrite in_preds. intros H. eapply root_no_pred'; eauto.
  Qed.

(*  Inductive Front (u : Unch) : Var -> Lab -> Prop :=
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
                                 Front u x p.*)
  
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
      apply prefix_cons_in in rp as rp'. eapply tag_inj with (s0:=s) in rp'. 
      subst s'. 1,2,3:assumption. 
    - assert (Hpred := Hin).
      rewrite H in Hpred.
      eapply in_exists_pred in Hpred; try eassumption.
      + destruct Hpred as [q [j [r [Hpredin Hpred]]]].
        assert (Hedge: q --> to) by (eauto using step_conf_implies_edge).
        eapply unch_trans_lem in Hunch; try eassumption.
        destruct (Lab_dec' to u) as [ | Hneq ]; subst.
        * exists i, s. split; [ | reflexivity ]. eauto using precedes_self.
        * destruct Hunch; [ firstorder |].
          setoid_rewrite in_preds in H0.
          eapply H0 in Hedge. destruct Hedge as [Hndef Huin].
          edestruct Hred as [j' [r' [Hprec Heq]]]; eauto.
          exists j', r'. rewrite Heq.
          split; [|eauto using no_def_untouched]. rewrite H. eapply precedes_succ; eauto.
          rewrite <-H. destruct t; eauto.
      + clear - H. destruct t; cbn in H; inversion t; subst x.
        * congruence.
        * inversion H2. subst; eauto.
  Qed.
End unch.
