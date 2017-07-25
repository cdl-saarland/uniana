Require Import Coq.Classes.EquivDec.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Eqdep_dec.
Require Import List.
Require Import Omega.

Section CFG.
  Variable N : nat.
  Variable Lab : Type.
  Variable Var : Type.
  Variable Val : Type.
  Variable init_uni : Var -> Prop.

  Definition IVec := (list nat).
  Definition State := Var -> Val.
  Definition States := State -> Prop.
  Definition Coord := prod Lab IVec.
  Definition Conf := prod Coord State.

  Definition UniState := Var -> Prop.

  Variable eff : Conf -> option Conf.
  Variable abs_uni_eff : UniState -> UniState.

  Definition uni_state_concr (uni : UniState) : State -> State -> Prop :=
    fun s => fun s' => forall x, uni x -> s x = s' x.

  Variable local_uni_corr : forall uni p i q j s s' qs qs', 
      uni_state_concr uni s s' ->
      eff (p, i, s) = Some (q, j, qs) ->
      eff (p, i, s') = Some (q, j, qs') ->
      uni_state_concr (abs_uni_eff uni) qs qs'.

  Variable has_edge : Lab -> Lab -> Prop.
  Variable root : Lab.
  Variable Lab_dec : forall (x y : Lab), {x = y} + {x <> y}.
  Program Instance lab_eq_eqdec : EqDec Lab eq := Lab_dec.

  Definition start_coord := (root, @nil nat) : Coord.

  Definition is_effect_on (p q : Lab) :=
    exists i i' s s', eff ((p, i), s) = Some ((q, i'), s').

  Variable root_no_pred : forall p, ~ has_edge p root.

  Variables edge_spec :
    forall p q, is_effect_on p q -> has_edge p q.

  (* TODO *)
  Axiom Conf_dec :
    forall k k' : Conf, {k = k'} + {k <> k'}.

  Inductive Tr : Conf -> Type :=
    | Init : forall s, Tr (start_coord, s)
    | Step : forall k k', Tr k' -> eff k' = Some k -> Tr k.

  Definition Traces := forall c, Tr c -> Prop.
  Definition Hyper := Traces -> Prop.

  (* This is the concrete transformer for sets of traces *)
  Definition sem_trace (ts : Traces) : Traces :=
    fun k' => fun tr' => exists k tr step, ts k tr /\ tr' = (Step k' k tr step).

  Definition Uni := Lab -> Var -> Prop.
  Definition Hom := Lab -> Prop.

  Definition sem_hyper (T : Hyper) : Hyper :=
    fun ts' => exists ts, T ts /\ ts' = sem_trace ts.

  (* 
  Definition traces (ts : Traces) : Prop :=
    forall t, ts t -> tr t.
    (* (forall s, ts ((start_coord, s) :: nil)) /\ forall t, ts t -> ts (step t). *)
  *)

  Inductive In (k : Conf) (tr : Tr k) : Conf -> Prop := 
    | In_At : In k tr k
    | In_Other : forall l k' tr' step, tr = (Step k k' tr' step) -> In k' tr' l -> In k tr l.

  Inductive Follows (k : Conf) (tr : Tr k) : Conf -> Conf -> Prop := 
  | Follows_At : forall pred pred_tr step,  tr = (Step k pred pred_tr step) ->
                                            Follows k tr k pred
  | Follows_Other : forall succ pred k' tr' step, tr = (Step k k' tr' step) ->
                                                    Follows k' tr' succ pred ->
                                                    Follows k tr succ pred.

  Inductive HasPrefix (k : Conf) (tr : Tr k) : forall l, Tr l -> Prop :=
  | Prefix_At : HasPrefix k tr k tr
  | Prefix_Step : forall l ltr l' ltr' step, tr = (Step k l ltr step) ->
                                             HasPrefix l ltr l' ltr' ->
                                             HasPrefix k tr l' ltr'.

  Lemma closed :
    forall ts k tr, sem_trace ts k tr -> exists k' tr' step, ts k' tr' /\ tr = (Step k k' tr' step).
  Proof.
    intros.
    unfold sem_trace in H.
    assumption.
  Qed.

  Definition prefix_closed : Hyper :=
    fun ts => (forall s, ts (start_coord, s) (Init s))
              \/ (forall k tk l tl step, ts k tk -> tk = (Step k l tl step) -> ts l tl).

  Definition uni_concr (u : Uni) : Hyper :=
    fun ts => forall t t' tr tr', ts t tr -> ts t' tr' ->
                                  forall x p i s s', In t tr ((p, i), s) ->
                                                     In t' tr' ((p, i), s') ->
                                                     u p x -> s x = s' x.


  Definition hom_concr (h : Hom) : Hyper :=
    fun ts =>
      forall t t'
             tr tr', ts t tr -> ts t' tr' ->
                     forall p, h p ->
                               forall q q' j j'
                                      k k' step step'
                                      i s s'
                                      s1 s2, Follows k (Step k t tr step)
                                                     ((p, i), s1) ((q, j), s) ->
                                             Follows k' (Step k' t' tr' step')
                                                     ((p, i), s2) ((q', j'), s')  ->
                                             q = q' /\ j = j'.

  Definition red_prod (h h' : Hyper) : Hyper :=
    fun ts => h ts /\ h' ts.
  
  Definition uni_trans (uni : Uni) (hom : Hom) : Uni :=
    fun p => if p == root then uni root
             else fun x => hom p /\ forall q, has_edge q p -> abs_uni_eff (uni q) x.
             

  Lemma uni_trans_root_inv :
    forall uni hom x, uni_trans uni hom root x = uni root x.
  Proof.
    intros.
    unfold uni_trans.
    simpl.
    destruct (equiv_dec root root).
    reflexivity.
    exfalso. apply c. reflexivity.
  Qed.

  Lemma root_no_eff :
    forall k s', eff k = Some (start_coord, s') -> False.
  Proof.
    intros.
    destruct k as [[p i] s].
    apply (root_no_pred p). apply edge_spec. unfold is_effect_on.
    exists i. exists nil. exists s. exists s'.
    assumption.
  Qed.

  Lemma in_start :
    forall p i s s' tr, In (start_coord, s') tr (p, i, s) -> (p, i) = start_coord.
  Proof.
    intros.
    unfold start_coord.
    remember (start_coord, s').
    inversion H; subst.
    + injection H0; intros; subst. reflexivity.
    + subst. exfalso. 
      destruct k'. destruct c.
      apply (root_no_pred l). apply edge_spec.
      unfold is_effect_on.
      exists i0. exists nil. exists s0. exists s'.
      assumption.
  Qed.

  Lemma start_no_tgt :
    forall i' s' k, eff k = Some (root, i', s') -> False.
  Proof.
    intros.
    destruct k as [[p i] s].
    apply (root_no_pred p).
    apply edge_spec.
    unfold is_effect_on.
    exists i. exists i'. exists s. exists s'.
    assumption.
  Qed.

  Lemma follows_exists :
    forall p i s h tr, In h tr (p, i, s) -> p <> root -> exists pred, Follows h tr (p, i, s) pred.
  Proof.
    intros.
    induction tr.
    + inversion H.
      - symmetry in H2. contradiction.
      - exfalso. eapply start_no_tgt. eassumption.
    + inversion H; subst.
      - exists k'. econstructor. reflexivity.
      - injection H1; intros; subst.
        apply inj_pair2_eq_dec in H3; subst.
        apply IHtr in H2.
        inversion_clear H2 as [pred H'].
        exists pred. econstructor; try eassumption.
        apply Conf_dec.
  Qed.

  Lemma follows_red :
    forall k tr succ pred, Follows k tr succ pred -> exists tr', (Follows succ tr' succ pred
                                                                  /\ HasPrefix k tr succ tr').
  Proof.
    intros.
    induction tr.
    + inversion H; exfalso; eapply start_no_tgt; eassumption.
    + inversion H; subst.
      - injection H0; intros; subst; clear H0.
        apply inj_pair2_eq_dec in H1; try (apply Conf_dec); subst. 
        exists (Step succ pred pred_tr e).
        split.
        * assumption.
        * constructor.
      - injection H0; intros; subst.
        apply inj_pair2_eq_dec in H2; try (apply Conf_dec); subst. 
        apply IHtr in H1. clear IHtr.
        destruct H1 as [tr [ Hfollow Hprefix ]].
        exists tr.
        split; try assumption.
        econstructor; try eassumption.
  Qed.

  Lemma follows_implies_step :
    forall k tr succ pred, Follows k tr succ pred -> eff pred = Some succ.
  Proof.
    intros.
    induction tr.
    - inversion H; exfalso; eapply start_no_tgt; eassumption.
    - inversion H; subst.
      * assumption.
      * injection H0; intros; subst; clear H0.
        apply inj_pair2_eq_dec in H2; try (apply Conf_dec); subst.
        auto.
  Qed.

  Lemma follows_implies_in2 :
    forall k' tr' k step succ pred, Follows k (Step k k' tr' step) succ pred -> In k' tr' pred.
  Proof.
    intro k'.
    intro tr'.
    induction tr'; intros.
    + inversion H; subst.
      - injection H0; intros; subst.
        apply inj_pair2_eq_dec in H1; try (apply Conf_dec); subst.
        constructor.
      - injection H0; intros; subst.
        apply inj_pair2_eq_dec in H2; try (apply Conf_dec); subst.
        inversion H1; subst; exfalso; eapply start_no_tgt; eassumption.
    + inversion H; subst.
      - injection H0; intros; subst.
        apply inj_pair2_eq_dec in H1; try (apply Conf_dec); subst.
        constructor.
      - injection H0; intros; subst.
        apply inj_pair2_eq_dec in H2; try (apply Conf_dec); subst.
        econstructor.
        econstructor.
        eapply IHtr'.
        apply H1.
  Qed.

  Lemma uni_correct :
    forall uni hom ts,
        sem_hyper (red_prod (uni_concr uni) (hom_concr hom)) ts ->
        uni_concr (uni_trans uni hom) ts.
  Proof.
    intros uni hom ts' Hred.
    unfold uni_concr.
    unfold sem_hyper in Hred.
    destruct Hred as [ts [Hconcr Hstep]]; subst.
    destruct Hconcr as [HCuni HChom].

    intros k k' tr tr' Hsem Hsem' x p i s s'.
    intros HIn HIn' Htrans.

    unfold uni_trans in Htrans. 
    destruct (equiv_dec p root).
    + rewrite e in *; clear e.
      destruct Hsem as [l [ltr [lstep [Hlin Hlstep]]]].
      destruct Hsem' as [l' [ltr' [lstep' [Hlin' Hlstep']]]].
      unfold uni_concr in HCuni.
      inversion HIn; subst.
      - exfalso. eapply start_no_tgt. eassumption.
      - inversion HIn'; subst.
        * exfalso. eapply start_no_tgt. eassumption.
        * injection H; intros; subst.
          apply inj_pair2_eq_dec in H3; try (apply Conf_dec); subst; clear H.
          injection H1; intros; subst.
          apply inj_pair2_eq_dec in H; try (apply Conf_dec); subst; clear H1.
          eapply (HCuni k'0 k'1 tr'0 tr'); try eassumption.
    + destruct Htrans as [Hhom Hpred]. 
      apply follows_exists in HIn; try eassumption.
      apply follows_exists in HIn'; try eassumption.
      destruct HIn as [[[q j] sq] Hflw].
      destruct HIn' as [[[q' j'] sq'] Hflw'].

      apply closed in Hsem.
      apply closed in Hsem'.
      destruct Hsem as [l [ltr [lstep [Hlin Hlstep]]]].
      destruct Hsem' as [l' [ltr' [lstep' [Hlin' Hlstep']]]].
      cut (q = q' /\ j = j'); intros.
      * inversion_clear H as [Hq Hj]; subst.
        rename j' into j.
        rename q' into q.
        eapply (local_uni_corr (uni q)).
        unfold uni_state_concr.
        - intros. 
          unfold uni_concr in HCuni.
          eapply HCuni.
          apply Hlin.
          apply Hlin'.
          eapply follows_implies_in2. apply Hflw.
          eapply follows_implies_in2. apply Hflw'.
          apply H.
        - eapply follows_implies_step; eassumption.
        - eapply follows_implies_step; eassumption.
        - apply Hpred.
          eapply edge_spec.
          unfold is_effect_on.
          exists j. exists i. exists sq. exists s. eapply follows_implies_step. apply Hflw.
      * clear HCuni. subst.
        unfold hom_concr in HChom.
        eapply (HChom l l' ltr ltr'); try eassumption.
Qed.