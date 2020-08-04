
Require Import Coq.Program.Utils.
Require Import Coq.Logic.Eqdep_dec.
Require Import Lists.ListSet.
Require Import List.
Require Import Coq.Classes.EquivDec.

Require Export Evaluation.

Open Scope prg.

Section unch.
  Context `{C : redCFG}.

  Notation "p --> q" := (edge p q = true) (at level 55,right associativity).

  Definition Unch := Lab -> Var -> set Lab.


  Lemma Lab_dec' `{redCFG} : forall (l l' : Lab), { l = l' } + { l <> l'}.
  Proof.
    apply Lab_dec.
  Qed.


  (** * RD-Concretizer **)
  (** ** Definition **)

  Definition unch_concr (unch : Unch) : Traces :=
    fun t => forall to i s u x, In (to, i, s) (`t) ->
                        set_In u (unch to x) ->
                        exists j r, Precedes' (`t) (u, j, r) (to, i, s) /\
                               r x = s x.

  Definition unch_meet (u1 u2 : Unch) : Unch
    := fun (p : Lab) (x : Var) => set_union Lab_dec' (u1 p x) (u2 p x).

  Infix "⊓" := unch_meet (at level 70).

  (** * Meet-preserving **)

  Lemma unch_concr_meet_preserve (u1 u2 : Unch) (t : trace)
    : unch_concr (u1 ⊓ u2) t <-> unch_concr u1 t /\ unch_concr u2 t.
  Proof.
    split;intros H.
    - unfold unch_concr in *. split;intros.
      1,2: specialize (H to i s u x H0); exploit H;eauto.
      1,2: unfold unch_meet.
      + eapply set_union_intro1;eauto.
      + eapply set_union_intro2;eauto.
    - destruct H.
      unfold unch_concr in *.
      intros.
      eapply set_union_elim in H2. destruct H2.
      + eapply H;eauto.
      + eapply H0;eauto.
  Qed.

  (** * RD-transformer **)

  (** ** Definition **)

  Definition unch_join_ptw (d d' : set Lab) := set_inter Lab_dec' d d'.

  Definition unch_join (u u' : Unch) : Unch :=
    fun l x => unch_join_ptw (u l x) (u' l x).

  Definition unch_trans_local (unch : Unch) (q p : Lab) (x : Var) : set Lab :=
    set_add Lab_dec' p (if is_def x q p then empty_set Lab else unch q x).

  Definition unch_trans_ptw (unch : Unch) l x : set Lab :=
    match preds l with
    | nil => set_add Lab_dec' l (empty_set Lab) 
    | p :: ps => let t := fun q => unch_trans_local unch q l x in
               fold_right (set_inter Lab_dec') (elem Lab) (map t (p :: ps))
    end.
  (*
    if Lab_dec' l root then set_add Lab_dec' root (empty_set Lab) else
      let t := fun q => unch_trans_local unch q l x in
      fold_right (set_inter Lab_dec') (elem Lab) (map t (preds l)).
*)

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
      rewrite H. reflexivity.
    + cut (forall q, ~ List.In q (preds root)); intros; eauto using list_emp_in, root_no_pred.
      rewrite in_preds. intros H. eapply root_no_pred; eauto.
  Qed.

  (*
  Lemma unch_trans_root : forall unch x, unch_trans unch root x = set_add Lab_dec' root (empty_set Lab).
  Proof.
    intros.
    cut (preds root = nil); intros.
    + unfold unch_trans, unch_trans_ptw.
      destruct (Lab_dec' root root); firstorder.
    + cut (forall q, ~ List.In q (preds root)); intros; eauto using list_emp_in, root_no_pred.
      rewrite in_preds. intros H. eapply root_no_pred; eauto.
  Qed.
  *)

  Lemma unch_trans_lem u to x unch :
    set_In u (unch_trans unch to x) ->
    u = to \/ (forall q, List.In q (preds to) -> (is_def x q to = false /\ set_In u (unch q x))).
  Proof.
    intros.
    unfold unch_trans, unch_trans_ptw, unch_join_ptw, unch_trans_local in H.
    induction (preds to); simpl in *.
    - right. intros. inject H0.
    - eapply set_inter_elim in H.
      destruct H as [Hin Hother].
      destruct l.
      + simpl in Hother.
        destruct (is_def x a) eqn:Hdef; simpl in Hin.
        inject Hin; intuition.
        destruct (Lab_dec' u to); [ eauto | ].
        right. intros. 
        inject H.
        * split; eauto using set_add_elim2.
        * inject H0.
      + eapply IHl in Hother. clear IHl.
        inject Hother; [ eauto |].
        destruct (Lab_dec' u to); subst; eauto.
        right.
        intros.
        inject H0; [ subst | eauto].
        destruct (is_def x q to).
        * simpl in Hin. firstorder auto with *.
        * eauto using set_add_elim2.
  Qed.

  Definition unch_concr' (unch : Unch) (l : list Conf) :=
    forall (to : Lab) (i : Tag) (s : State) (u : Lab) (x : Var),
      (to,i,s) ∈ l ->
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
    destruct t;[inversion Htr|].
    destruct (c) eqn:E. destruct c0 eqn:E'.
    eapply Tr_EPath in Htr. destructH.
    - eapply EPath_TPath in Htr. eapply tpath_NoDup in Htr. eapply NoDup_map_inv. eauto.
    - cbn. reflexivity.
  Qed.


  Lemma precedes_prefix l' p q i j r s (t : list Conf)
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

  (** ** Dominance **)

  Definition path := { π : list Lab | exists e, Path edge__P root e π }.
  Definition Paths := path -> Prop.

  Definition unch_concr_dom (unch : Unch) (π : path) :=
    forall (to : Lab) (u : Lab) (x : Var),
      u ∈ unch to x ->
      to ∈ `π ->
      u ∈ `π.

  Definition sem_path (ps : Paths) : Paths :=
    fun π' => exists l π, ps π /\ `π' = (l :: `π).

  Lemma pred_in_path (π : path) (π' : path) l to
        (Hpath : `π = l :: `π')
        (Hin : to ∈ `π)
        (Hnoroot : to <> root)
    : exists pred, pred ∈ preds to /\ pred ∈ `π'.
  Proof.
    unfold path in π.
    destruct π as [ π [ e He ] ].
    simpl in *.
    eapply path_to_elem with (r := to) in He; try assumption.
    destruct He as [ϕ [Hp Hprefix]].
    clear Hin e.
    inversion Hp; subst.
    - firstorder eauto with *.
    - exists b. split.
      + unfold preds. rewrite in_filter_iff. split.
        * eauto.
        * simpl. rewrite H0. trivial.
      + eapply path_contains_front in H.
        dependent destruction Hprefix.
        * assumption.
        * eapply prefix_incl in Hprefix. eapply Hprefix. right. assumption.
  Qed.

  Lemma preds_root_nil
    : preds root = [].
  Proof.
    unfold preds.
    induction (elem Lab); simpl; [ reflexivity |].
    (* I'd love to do a destruct on (edge a root) but somehow, I can't *)
  Admitted.
      
  Lemma unch_correct_dom :
        forall unch π, sem_path (unch_concr_dom unch) π -> unch_concr_dom (unch_trans unch) π.
  Proof.
    intros.
    unfold sem_path in H.
    unfold unch_concr_dom.
    intros to u x Hunch Htoin.
    destruct H as [l [π' [Hconcr Heq]]].
    unfold unch_trans, unch_trans_ptw in Hunch.
    unfold unch_concr_dom in Hconcr.

    destruct (Lab_dec' to root). {
      subst to. rewrite preds_root_nil in Hunch. simpl in Hunch.
      inject Hunch; [ assumption | inject H ].
    }

    assert (Hpred : exists pred, pred ∈ preds to /\ pred ∈ `π'). {
      eapply pred_in_path; try eassumption.
    }
    
    destruct Hpred as [pred [Hpred Hpredin]].
    induction (preds to) as [ | p ps ]; simpl in Hunch.
    - contradiction Hpred.
    - eapply set_inter_elim in Hunch.
      destruct (Lab_dec' pred p).
      + subst. clear Hpred.
        destruct Hunch as [Hunch _]. clear IHps.
        unfold unch_trans_local in Hunch.
        unfold path in π'.
        eapply set_add_elim in Hunch.
        inversion_clear Hunch.
        * subst. eassumption.
        * destruct (is_def x p to); [ firstorder |].
          rewrite Heq. right. eauto.
      + destruct Hunch as [_ Hunch].
        inversion Hpred; [ subst; tauto |].
        destruct ps; [ inject H | eapply IHps; try eassumption ].
  Qed.

  Lemma unch_concr_dom_monotone unch2 unch1 
    (Hless : forall p x, unch2 p x ⊆ unch1 p x) 
    : forall π, unch_concr_dom unch1 π -> unch_concr_dom unch2 π.
  Proof.
    intros.
    unfold unch_concr_dom in *.
    intros to u x Hunch Hinto.
    unfold incl in Hless.
    eauto.
  Qed.

  (* 
  Lemma unch_trans_contains unch u p x :
    u ∈ unch_trans unch p x -> u = p \/ u ∈ unch 
*)
  Lemma forall_summary `{T : Type} (P Q : T -> Prop)
        : (forall a, P a) -> (forall a, Q a) -> (forall a, P a -> Q a).
  Proof.
    firstorder.
  Qed.

  Lemma path_begin_no_preds π p
        (Hπ : Path edge__P root p π)
    : preds (last π root) = [].
  Proof.
    dependent induction π.
    - simpl. eapply preds_root_nil.
    - enough (a = p).
      + subst. simpl.
        destruct π.
        * enough (Heq : forall a b, Path edge__P a b [b] -> a = b).
          -- apply Heq in Hπ. subst p. eapply preds_root_nil.
          -- intros. inversion H; [ reflexivity |].
             subst. inversion H1.
        * inversion Hπ. eapply IHπ. eapply H0.
      + symmetry. eapply path_front. eassumption.
  Qed.

  Lemma unch_trace_dom unch p x u
        (Hfix: forall p x, unch p x ⊆ unch_trans unch p x)
    : u ∈ unch p x -> Dom edge__P root u p.
  Proof.
    unfold Dom.
    intros Hunch π Hπ.
    specialize (path_begin_no_preds Hπ); intros Hpred.
    induction Hπ.
    - simpl in Hpred. eapply Hfix in Hunch.
      unfold unch_trans, unch_trans_ptw in Hunch.
      rewrite Hpred in Hunch. simpl in Hunch; inject Hunch; intuition.
    - subst. eapply Hfix in Hunch.
      unfold unch_trans, unch_trans_ptw in Hunch.
      assert (Hin : b ∈ preds c). {
        unfold preds.
        eapply in_filter_iff. simpl. rewrite H. intuition.
      }
      induction (preds c) as [| p ps]; [ inject Hin | ].
      simpl in Hunch. 
      eapply set_inter_elim in Hunch.
      destruct Hunch as [Hlocal Hother].
      unfold unch_trans_local in Hlocal.
      destruct Hin.
      * subst p.
        destruct (is_def x b c).
        -- simpl in Hlocal. inject Hlocal; intuition.
        -- eapply set_add_elim in Hlocal. inject Hlocal; [ intuition |].
           right. eapply IHHπ. assumption. simpl in Hpred.
           inversion Hπ; subst; assumption.
      * eapply IHps; try eassumption.
        destruct ps; [ contradiction | eassumption].
  Qed.

  (** ** Correctness **)

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
      simpl in Hunch. rewrite preds_root_nil in Hunch. destruct Hunch; [ subst | firstorder ]. 
      exists i, s. split; eauto. exists nil. split; [|econstructor].
      apply root_start_tag in Hin as rst. subst i.
      assert (rp := root_prefix t). destruct rp as [s' rp].
      apply prefix_cons_in in rp as rp'. eapply tag_inj with (s0:=s) in rp'.
      subst s'. 1,2:assumption.
    - assert (Hpred := Hin).
      rewrite H in Hpred.
      eapply in_exists_pred in Hpred; try eassumption.
      + destruct Hpred as [q [j [r [Hpredin Hpred]]]].
        assert (Hedge: q --> to) by (eauto using step_conf_implies_edge).
        eapply unch_trans_lem in Hunch; try eassumption.
        destruct (Lab_dec to u) as [ | Hneq ]; subst.
        * exists i, s. split; [ | reflexivity ]. rewrite <-e. eapply precedes_self;eauto.
        * destruct Hunch; [ firstorder eauto with * |].
          setoid_rewrite in_preds in H0.
          eapply H0 in Hedge. destruct Hedge as [Hndef Huin].
          edestruct Hred as [j' [r' [Hprec Heq]]]; eauto.
          exists j', r'. rewrite Heq.
          split; [|eauto using no_def_untouched]. rewrite H. eapply precedes_succ; eauto.
          rewrite <-H. destruct t; eauto.
      + clear - H. destruct t; cbn in H; inversion t; subst x.
        * destruct t' as [t' Ht]. destruct t';[inversion Ht|]. cbn in *.
          inversion t. subst. eauto.
        * inversion H2. subst; eauto.
  Qed.
End unch.
