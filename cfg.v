Require Import Coq.Classes.EquivDec.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Eqdep_dec.
Require Import List.
Require Import Nat.
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

  Ltac inv_tr H := inversion H; subst; 
      repeat match goal with
      | [ H0: @existT Conf _ _ _ = @existT _ _ _ _  |- _ ] => apply inj_pair2_eq_dec in H0; try (apply Conf_dec); subst
      end.

  Fixpoint len (k : Conf) (t : Tr k) : nat.
    inversion t.
    - apply 0.
    - subst. apply (1 + len k' X).
    Defined.

  Inductive At : forall k, Tr k -> nat -> Conf -> Prop :=
  | AtInit : forall s, At (start_coord, s) (Init s) 0 (start_coord, s)
  | AtSuffix : forall k k' sk t n step, At k t n sk ->
                                        At k' (Step k' k t step) n sk
  | AtStep : forall k k' t step,  At k' (Step k' k t step) (1 + len k t) k'.
  
  Definition Traces := forall c, Tr c -> Prop.
  Definition Hyper := Traces -> Prop.

  (* This is the concrete transformer for sets of traces *)
  Definition sem_trace (ts : Traces) : Traces :=
    fun k' => fun tr' => exists k tr step, ts k tr /\ tr' = (Step k' k tr step).

  Definition Uni := Lab -> Var -> Prop.
  Definition Hom := Lab -> Prop.
  Definition Unch := Lab -> Var -> Lab.

  Definition sem_hyper (T : Hyper) : Hyper :=
    fun ts' => exists ts, T ts /\ ts' = sem_trace ts.

  (* 
  Definition traces (ts : Traces) : Prop :=
    forall t, ts t -> tr t.
    (* (forall s, ts ((start_coord, s) :: nil)) /\ forall t, ts t -> ts (step t). *)
  *)

  Inductive In : forall k, Tr k -> Conf -> Prop := (* (k : Conf) (tr : Tr k) : Conf -> Prop :=  *)
    | In_At : forall k tr, In k tr k
    | In_Other : forall l k k' tr' step, In k' tr' l -> In k (Step k k' tr' step) l.

  Inductive Follows : forall k, Tr k -> Conf -> Conf -> Prop := 
  | Follows_At : forall k pred pred_tr step, Follows k (Step k pred pred_tr step) k pred
  | Follows_Other : forall succ pred k k' tr' step, Follows k' tr' succ pred ->
                                                    Follows k (Step k k' tr' step) succ pred.

  Inductive HasPrefix : forall k, Tr k -> forall l, Tr l -> Prop :=
  | Prefix_At : forall k tr, HasPrefix k tr k tr
  | Prefix_Step : forall k l ltr l' ltr' step, HasPrefix l ltr l' ltr' ->
                                               HasPrefix k (Step k l ltr step) l' ltr'.

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

                                           
  (*
  
  Inductive UnchOpen (x : Var) (from to : Lab) : forall k', Tr k' -> Type :=
  | Open : forall k i s t step,
      UnchBetween from to k t ->
      UnchOpen from to (to, i, s) (Step (to, i, s) k t step)
  | Cont : forall k i p s t step,
      p <> from ->
      UnchOpen from to k t ->
      UnchOpen from to (p, i, s) (Step (p, i, s) k t step)
  with UnchBetween (x : Var) (from to : Lab) : forall k', Tr k' -> Type :=
       | Close : forall k i s t step,
           UnchOpen from to k t ->
           UnchBetween from to (from, i, s) (Step (from, i, s) k t step)
       | App : forall p i s k t step,
           UnchBetween from to k t ->
           p <> to ->
           UnchBetween from to (p, i, s) (Step (p, i, s) k t step)
       | Start : forall s, UnchBetween from to (start_coord, s) (Init s).
*)
  Definition Unch_Between (k : Conf) (t : Tr k) (s : State) (x : Var) (a b c : nat) :=
    forall q i s', a < b -> b <= c -> At k t b (q, i, s') -> s x = s' x.
  
  Definition Since (k k' : Conf) (t : Tr k) (t' : Tr k') (x : Var) (from to : Lab) := 
    forall i c c' s s', At k t c (to, i, s) -> 
                        At k' t' c' (to, i, s') ->
                        exists j r r' a a', At k t a (from, j, r) /\
                                            At k' t' a' (from, j, r') /\
                                            forall b b', Unch_Between k t s x a b c /\
                                                         Unch_Between k' t' s' x a' b' c'.
  
  Definition unch_concr (unch : Unch) : Hyper :=
    fun ts => forall k k' t t', ts k t -> ts k' t' -> 
                                forall to x from, unch to x = from -> Since k k' t t' x from to.

  Definition red_prod (h h' : Hyper) : Hyper :=
    fun ts => h ts /\ h' ts.
  
  Definition uni_trans (uni : Uni) (hom : Hom) (unch : Unch) : Uni :=
    fun p => if p == root then uni root
             else fun x => (hom p /\ forall q, has_edge q p -> abs_uni_eff (uni q) x)
                             \/ uni (unch p x) x.
             

  Lemma uni_trans_root_inv :
    forall uni hom unch x, uni_trans uni hom unch root x = uni root x.
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
    + injection H1; intros; subst. reflexivity.
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
    + inversion H. subst. contradiction.
    + inversion H; subst.
      * dependent inversion tr1; subst.
        - contradiction.
        - exists k'0. constructor.
      * apply inj_pair2_eq_dec in H4; subst; try (apply Conf_dec).
        apply IHtr in H5.
        inversion_clear H5 as [pred H'].
        exists pred. econstructor; try eassumption.
  Qed.

  Lemma follows_red :
    forall k tr succ pred, Follows k tr succ pred -> exists tr', (Follows succ tr' succ pred
                                                                  /\ HasPrefix k tr succ tr').
  Proof.
    intros.
    induction tr.
    + inversion H; exfalso; eapply start_no_tgt; eassumption.
    + inversion H; subst.
      - apply inj_pair2_eq_dec in H3; try (apply Conf_dec); subst. 
        exists (Step succ pred tr e).
        split.
        * assumption.
        * constructor.
      - apply inj_pair2_eq_dec in H3; try (apply Conf_dec); subst. 
        apply IHtr in H5. clear IHtr.
        destruct H5 as [tr' [ Hfollow Hprefix ]].
        exists tr'.
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
      * apply inj_pair2_eq_dec in H3; try (apply Conf_dec); subst.
        auto.
  Qed.

  Lemma follows_implies_in2 :
    forall k' tr' k step succ pred, Follows k (Step k k' tr' step) succ pred -> In k' tr' pred.
  Proof.
    intro k'.
    intro tr'.
    induction tr'; intros.
    + inv_tr H.
      - constructor.
      - inversion H5; subst; exfalso; eapply start_no_tgt; eassumption.
    + inv_tr H.
      - constructor.
      - econstructor.
        eapply IHtr'.
        eauto.
  Qed.

  Lemma in_implies_at :
    forall k k' t, In k t k' <-> exists a, At k t a k'.
  Proof.
    intros. split; intro.
    + induction t.
      - inversion H; subst.
        apply inj_pair2_eq_dec in H2; try (apply Conf_dec); subst.
        exists 0. econstructor.
      - inv_tr H.
        * dependent inversion tr0; subst.
          ** exists 0. econstructor.
          ** exists (1 + len k'1 t0).
             apply AtStep.
        * apply IHt in H4.
          destruct H4 as [a HAt].
          exists a.
          econstructor. assumption.
    + induction t; destruct H as [a H].
      - inversion H; subst. constructor.
      - inv_tr H.
        apply In_Other.
        * apply IHt. exists a. auto.
        * constructor.
  Qed.

  Lemma uni_correct :
    forall uni hom unch ts,
        sem_hyper (red_prod (red_prod (uni_concr uni) (hom_concr hom)) (unch_concr unch)) ts ->
        uni_concr (uni_trans uni hom unch) ts.
  Proof.
    intros uni hom unch ts' Hred.
    unfold uni_concr.
    unfold sem_hyper in Hred.
    destruct Hred as [ts [Hconcr Hstep]]; subst.
    destruct Hconcr as [[HCuni HChom] HCunch].

    intros k k' tr tr' Hsem Hsem' x p i s s'.
    intros HIn HIn' Htrans.

    unfold uni_trans in Htrans. 
    destruct (equiv_dec p root).
    + rewrite e in *; clear e.
      destruct Hsem as [l [ltr [lstep [Hlin Hlstep]]]].
      destruct Hsem' as [l' [ltr' [lstep' [Hlin' Hlstep']]]].
      unfold uni_concr in HCuni.
      inv_tr HIn.
      - exfalso. eapply start_no_tgt. eassumption.
      - inv_tr HIn'.
        * exfalso. eapply start_no_tgt. eassumption.
        * inv_tr H. eapply (HCuni l l' ltr ltr'); try eassumption.
    + destruct Htrans as [[Hhom Hpred] | Hunch].
      - apply follows_exists in HIn; try eassumption.
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
          unfold uni_state_concr in *.
          eapply (local_uni_corr (uni q)).
          ** intros. 
             unfold uni_concr in HCuni.
             eapply HCuni.
             apply Hlin.
             apply Hlin'.
             eapply follows_implies_in2. apply Hflw.
             eapply follows_implies_in2. apply Hflw'.
             apply H.
          ** eapply follows_implies_step; eassumption.
          ** eapply follows_implies_step; eassumption.
          ** apply Hpred.
             eapply edge_spec.
             unfold is_effect_on.
             exists j. exists i. exists sq. exists s. eapply follows_implies_step. apply Hflw.
        * clear HCuni. subst.
          unfold hom_concr in HChom.
          eapply (HChom l l' ltr ltr'); try eassumption.
      - clear HChom.
        destruct Hsem as [l [ltr [lstep [Hlin Hlstep]]]].
        destruct Hsem' as [l' [ltr' [lstep' [Hlin' Hlstep']]]].
        subst tr tr'.
        rename c into HProot.
        remember (unch p x) as q; symmetry in Heqq.
        rename Hunch into Huniq.

        apply in_implies_at in HIn.
        apply in_implies_at in HIn'.
        destruct HIn as [c HAt].
        destruct HIn' as [c' HAt'].

        unfold unch_concr in HCunch.
        specialize (HCunch l l' ltr ltr' Hlin Hlin' p x q Heqq).
        unfold Since in HCunch.
        specialize (HCunch i c c' s s').
        

        unfold uni_concr in HCuni.
        specialize (HCuni l l' ltr ltr' Hlin Hlin' x q).


        specialize (Hlin p x q Heqq).
        specialize (Hlin' p x q Heqq).
        unfold Between in *.


        


Qed.