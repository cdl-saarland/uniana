
Require Import Coq.Program.Utils.
Require Import Lists.ListSet.
Require Import List.
Require Import Coq.Classes.EquivDec.

Require Export Evaluation.

Open Scope prg.

Section unch.
  Context `{C : redCFG}.
  
  Notation "p --> q" := (edge p q = true) (at level 55,right associativity).
  
  Lemma root_no_pred' : forall p, p --> root -> False.
  Proof.
    eapply root_no_pred.
  Qed.

  Definition Unch := Lab -> Var -> set Lab.


  Definition unch_concr (unch : Unch) : Traces :=
    fun t => forall to i s u x, In (to, i, s) (`t) ->
                        set_In u (unch to x) ->
                        exists j r, Precedes' (`t) (u, j, r) (to, i, s) /\
                               r x = s x.
  
  Definition unch_join_ptw (d d' : set Lab) := set_inter Lab_dec' d d'. 

  Definition unch_join (* unused *)(u u' : Unch) : Unch :=
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

  Lemma unch_trans_root (* unused *): forall unch x, unch_trans unch root x = set_add Lab_dec' root (empty_set Lab).
  Proof.
    intros.
    cut (preds root = nil); intros.
    + unfold unch_trans, unch_trans_ptw. 
      destruct (Lab_dec' root root); firstorder.
    + cut (forall q, ~ List.In q (preds root)); intros; eauto using list_emp_in, root_no_pred'.
      rewrite in_preds. intros H. eapply root_no_pred'; eauto.
  Qed.
  
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
  
  Definition unch_concr' (unch : Unch) (l : list Conf) :=
    forall (to : Lab) (i : Tag) (s : State) (u : Lab) (x : Var),
      (to,i,s) ∈ l ->
      u ∈ unch to x ->
      exists (j : Tag) (r : State), Precedes' l (u,j,r) (to,i,s) /\ r x = s x.

  
  Lemma prefix_trans_NoDup (A : Type) `{EqDec A eq} (a : A) (l l1 l2 : list A)
        (Hpre1 : Prefix (a :: l1) l)
        (Hpre2 : Prefix l2 l)
        (Hnd : NoDup l)
        (Hin : a ∈ l2)
    : Prefix (a :: l1) l2.
  Proof.
    induction l;cbn.
    - eapply prefix_incl in Hin;eauto. cbn in Hin. contradiction.
    - inversion_clear Hnd;subst. decide' (a == a0).
      + inversion Hpre1;subst.
        * inversion Hpre2; subst; [econstructor|].
          eapply prefix_incl in Hin; eauto. congruence.
        * exfalso. eapply prefix_incl in H4. firstorder.          
      + eapply prefix_incl in Hin;eauto. destruct Hin;[congruence|].
        inversion Hpre1;subst;[congruence|].
        inversion Hpre2; subst.
        * econstructor;eauto.
        * eapply IHl;eauto.
  Qed.

  
  Lemma Tr_NoDup t
        (Htr : Tr t)
    : NoDup t.
  Proof.
    destruct (ne_front t) eqn:E. destruct c eqn:E'.
    eapply Tr_EPath in Htr. destructH.
    - eapply EPath_TPath in Htr. eapply tpath_NoDup in Htr. eapply NoDup_map_inv.
      rewrite to_list_ne_map. eauto.
    - rewrite E. reflexivity.
  Qed.


  Lemma precedes_prefix l' p q i j r s (t : ne_list Conf)
        (Hprec : Precedes' t (q,j,r) (p,i,s))
        (Hpre  : Prefix l' t)
        (Hin : (p,i,s) ∈ l')
        (Htr : Tr t)
    : Precedes' l' (q,j,r) (p,i,s).
  Proof.
    unfold Precedes' in *.
    destructH. exists l'0. split;eauto.
    eapply prefix_trans_NoDup;eauto.
    eapply Tr_NoDup;eauto.
  Qed.

  Lemma unch_concr'_pre unch t l
        (HCunch : unch_concr unch t)
        (Hpre : Prefix l (`t))
    : unch_concr' unch l.
  Proof.
    unfold unch_concr,unch_concr' in *; eauto.
    intros. specialize (HCunch to i s u x). exploit HCunch;[eapply prefix_incl;eauto|].
    destructH. eexists; eexists; split; [|eauto].
    eapply precedes_prefix;eauto. destruct t; cbn; eauto.
  Qed.
  
  Lemma unch_dom u p i s x unch l 
        (Hunch : u ∈ unch_trans unch p x)
        (HCunch : unch_concr' (unch_trans unch) l)
        (Htr : Tr ((p,i,s) :< l))
    : Dom edge root u p.
  Proof.
    unfold unch_trans,unch_trans_ptw in Hunch. unfold unch_trans_local in Hunch.
    (* FIXME: give intuition *)
    destruct (Lab_dec' p root).
    - cbn in *. destruct Hunch;[|contradiction]. (*subst. eapply dominant_self.
    - assert (exists L, forall r, r ∈ L
                        <-> forall q, q ∈ preds p
                               -> r ∈ set_add Lab_dec' p (if is_def x q p then empty_set Lab else unch q x)). *)
      admit.
  Admitted.

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
        destruct (Lab_dec to u) as [ | Hneq ]; subst.
        * exists i, s. split; [ | reflexivity ]. rewrite <-e. eapply precedes_self;eauto.
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
