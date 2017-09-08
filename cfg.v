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
  Definition UnchState := Var -> Lab.

  Variable eff : Conf -> option Conf.
  Variable abs_uni_eff : UniState -> UniState.
  Variable abs_unch_eff : UnchState -> UnchState.

  
  
  
  Definition uni_state_concr (uni : UniState) : State -> State -> Prop :=
    fun s => fun s' => forall x, uni x -> s x = s' x.

  Variable local_uni_corr : forall uni p i q j s s' qs qs', 
      uni_state_concr uni s s' ->
      eff (p, i, s) = Some (q, j, qs) ->
      eff (p, i, s') = Some (q, j, qs') ->
      uni_state_concr (abs_uni_eff uni) qs qs'.

  Variable has_edge : Lab -> Lab -> bool.
  Variable is_def : Var -> Lab -> Lab -> bool.
  Variable root : Lab.
  Variable Lab_dec : forall (x y : Lab), {x = y} + {x <> y}.
  Variable Val_dec : forall (x y : Val), {x = y} + {x <> y}.
  Program Instance lab_eq_eqdec : EqDec Lab eq := Lab_dec.
  Program Instance val_eq_eqdec : EqDec Val eq := Val_dec.

  Definition start_coord := (root, @nil nat) : Coord.

  Definition is_effect_on (p q : Lab) :=
    exists i i' s s', eff ((p, i), s) = Some ((q, i'), s').

  Variable root_no_pred : forall p, has_edge p root = false.

  Variables edge_spec :
    forall p q, is_effect_on p q -> has_edge p q = true.

  Variables def_spec :
    forall p q x, (exists i j s r, eff (p, i, s) = Some (q, j, r) /\ r x <> s x) -> is_def x p q = true.

  Lemma step_implies_edge :
    forall k k', eff k = Some k' -> exists p q i j s r, has_edge p q = true /\ k = (p, i, s) /\ k' = (q, j, r).
  Proof.
    intros.
    destruct k as [[p i] s].
    destruct k' as [[q j] r].
    exists p. exists q. exists i. exists j. exists s. exists r.
    split; auto.
    apply edge_spec.
    exists i. exists j. exists s. exists r.
    assumption.
  Qed.

  (* TODO *)
  Axiom Conf_dec :
    forall k k' : Conf, {k = k'} + {k <> k'}.

  Inductive Tr : Conf -> Type :=
    | Init : forall s, Tr (start_coord, s)
    | Step : forall k k', Tr k' -> eff k' = Some k -> Tr k.

  Ltac inv_tr H := inversion H; subst; 
                   repeat match goal with
                          | [ H0: @existT Conf _ _ _ = @existT _ _ _ _  |- _ ] => apply inj_pair2_eq_dec in H0;
                                                                                  try (apply Conf_dec); subst
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

  Definition dom (p q : Lab) :=
    forall k t b j r, At k t b (q, j, r) -> exists a i s, At k t a (p, i, s) /\ a <= b.

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

  Lemma in_root :
    forall p i s s' t, In (start_coord, s) t (p, i, s') -> (p, i, s) = (start_coord, s).
  Proof.
    intros.
  Admitted.

  Inductive Follows : forall k, Tr k -> Conf -> Conf -> Prop := 
  | Follows_At : forall k pred pred_tr step, Follows k (Step k pred pred_tr step) k pred
  | Follows_Other : forall succ pred k k' tr' step, Follows k' tr' succ pred ->
                                                    Follows k (Step k k' tr' step) succ pred.

  Inductive Leads : forall k, Tr k -> Conf -> Conf -> Prop :=
  | Leads_At : forall k t lead follow step, In k t lead ->
                                            Leads follow (Step follow k t step) lead follow
  | Leads_Cont : forall k k' t lead follow step, Leads k t lead follow ->
                                                 Leads k' (Step k' k t step) lead follow.

  Inductive HasPrefix : forall k, Tr k -> forall l, Tr l -> Prop :=
  | Prefix_At : forall k tr, HasPrefix k tr k tr
  | Prefix_Step : forall k l ltr l' ltr' step, HasPrefix l ltr l' ltr' ->
                                               HasPrefix k (Step k l ltr step) l' ltr'.

  Definition prefix_closed : Hyper :=
    fun ts => (forall s, ts (start_coord, s) (Init s))
              \/ (forall k tk l tl step, ts k tk -> tk = (Step k l tl step) -> ts l tl).

  Definition all : Traces -> Prop :=
    fun ts => forall k t, ts k t -> forall k' step, ts k' (Step k' k t step).

  Lemma all_closed :
    forall ts, all ts -> all (sem_trace ts).
  Proof.
    unfold all in *.
    intros.
    unfold sem_trace.
    exists k. exists t. exists step. 
    split.
    - unfold sem_trace in H0.
      destruct H0 as [k0 [tr0 [step0 [Htr0 HStep0]]]]; subst.
      apply H.
      assumption.
    - reflexivity.
  Qed.    

  Lemma all_trace :
    forall ts k tr, all ts -> sem_trace ts k tr -> ts k tr.
  Proof.
    intros.
    destruct H0 as [k' [tr' [step' [Hts HStep]]]]; subst.
    auto.
  Qed.
  
  Definition uni_concr (u : Uni) : Hyper :=
    fun ts => all ts /\ forall t t' tr tr', ts t tr -> ts t' tr' ->
                                  forall x p i s s', In t tr ((p, i), s) ->
                                                     In t' tr' ((p, i), s') ->
                                                     u p x -> s x = s' x.

  (*
                                      s1 s2, Follows k (Step k t tr step)
                                                     ((p, i), s1) ((q, j), s) ->
                                             Follows k' (Step k' t' tr' step')
                                                     ((p, i), s2) ((q', j'), s')  ->
  *)

  Definition hom_concr (h : Hom) : Hyper :=
    fun ts =>  all ts /\
      forall t t'
             tr tr', ts t tr -> ts t' tr' ->
                     forall p, h p ->
                               forall q q' j j'
                                      i s s'
                                      s1 s2, Follows t tr ((p, i), s1) ((q, j), s) ->
                                             Follows t' tr' ((p, i), s2) ((q', j'), s')  ->
                                             q = q' /\ j = j'.

  Definition Unch_Between (k : Conf) (t : Tr k) (s : State) (x : Var) (a b c : nat) :=
    forall q i s', a < b -> b <= c -> At k t b (q, i, s') -> s x = s' x.
  
  Definition Since (k k' : Conf) (t : Tr k) (t' : Tr k') (x : Var) (from to : Lab) := 
    forall i s s', In k t (to, i, s) -> 
                   In k' t' (to, i, s') ->
                   exists j r r' , In k t (from, j, r) /\
                                   In k' t' (from, j, r') /\
                                   s x = r x /\ s' x = r' x.

  (*
  Definition unch_concr2 (unch : Unch) : Traces :=
    fun k, fun t => forall to x from, unch to x = from ->
                                      forall i s, In k t (to, i, s) ->
                                                  exists j r, In k t (from 
*)
  
  Definition unch_concr (unch : Unch) : Traces :=
    fun k => fun t => forall x to i s, In k t (to, i, s) ->
                                       exists j r, In k t (unch to x, j, r) /\ s x = r x.

  Variable unch_trans_local : Unch -> Lab -> Lab -> Var -> Lab.
  Variable unch_trans_local_spec :
    forall q p x unch, if is_def x q p then unch_trans_local unch q p x = p
                       else unch_trans_local unch q p x = unch q x.

  Variable unch_trans : Unch -> Unch.
  Variable unch_trans_spec :
    forall unch p x r, unch_trans unch p x = r ->
                       (p =/= root /\ forall q, unch_trans_local unch q p x = r) \/ r = p.
    
  Definition uni_trans (uni : Uni) (hom : Hom) (unch : Unch) : Uni :=
    fun p => if p == root then uni root
             else fun x => (hom p /\ forall q, has_edge q p = true -> abs_uni_eff (uni q) x)
                             \/ uni (unch p x) x.
             

  Definition red_prod (h h' : Hyper) : Hyper :=
    fun ts => h ts /\ h' ts.

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

  Lemma start_no_tgt :
    forall i' s' k, eff k = Some (root, i', s') -> False.
  Proof.
    intros. 
    destruct k as [[p i] s].
    unfold start_coord in H.
    cut (is_effect_on p root); intros.
    apply edge_spec in H0.
    rewrite root_no_pred in H0.
    inversion H0.
    unfold is_effect_on.
    exists i. exists i'. exists s. exists s'.
    assumption.
  Qed.

  Lemma follows_exists_detail :
    forall p i s h tr, In h tr (p, i, s) -> p <> root ->
                       exists q j r, Follows h tr (p, i, s) (q, j, r).
  Proof.
    intros.
    induction tr.
    + inversion H. subst. contradiction.
    + inv_tr H.
      * dependent inversion tr1; subst.
        - contradiction.
        - destruct k'0 as [[q j] r]. exists q. exists j. exists r. constructor.
      * apply IHtr in H5.
        inversion_clear H5 as [q [j [r H']]].
        exists q. exists j. exists r. econstructor; try eassumption.
  Qed.

  Lemma follows_exists :
    forall p i s h tr, In h tr (p, i, s) -> p <> root ->
                       exists pred, Follows h tr (p, i, s) pred.
  Proof.
    intros.
    apply (follows_exists_detail p i s h tr H) in H0.
    destruct H0 as [q [j [r H0]]].
    exists (q, j, r). assumption.
  Qed.

  Lemma follows_red :
    forall k tr succ pred, Follows k tr succ pred -> exists tr', (Follows succ tr' succ pred
                                                                  /\ HasPrefix k tr succ tr').
  Proof.
    intros.
    induction tr.
    + inversion H; exfalso; eapply start_no_tgt; eassumption.
    + inv_tr H.
      - exists (Step succ pred tr e).
        split.
        * assumption.
        * constructor.
      - apply IHtr in H5. clear IHtr.
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
    - inv_tr H; auto.
  Qed.

  Lemma follows_implies_edge :
    forall k tr p q i j r s, Follows k tr (p, i, s) (q, j, r) -> has_edge q p = true.
  Proof.
    intros.
    apply follows_implies_step in H.
    apply step_implies_edge in H.
    repeat destruct H.
    destruct H0.
    injection H; intros; subst; clear H.
    injection H0; intros; subst; clear H0.
    reflexivity.
  Qed.

  Lemma follows_implies_in2 :
    forall k tr succ pred, Follows k tr succ pred -> In k tr pred.
  Proof.
    intros k tr.
    induction tr; intros; inv_tr H.
    - repeat constructor. 
    - econstructor. eapply IHtr. eauto.
  Qed.

  Lemma follows_implies_in2_step :
    forall k' k tr step succ pred, Follows k' (Step k' k tr step) succ pred -> In k tr pred.
  Proof.
    intros.
    inv_tr H.
    - constructor.
    - eapply follows_implies_in2; eauto.
  Qed.

  Lemma in_implies_at :
    forall k k' t, In k t k' -> exists a, At k t a k'.
  Proof.
    intros. 
    induction t.
    - inv_tr H. exists 0. econstructor.
    - inv_tr H.
      * dependent inversion tr0; subst.
        ** exists 0. econstructor.
        ** exists (1 + len k'1 t0).
           apply AtStep.
      * apply IHt in H4.
        destruct H4 as [a HAt].
        exists a.
        econstructor. assumption.
  Qed.

  Lemma at_implies_in :
    forall a k t k', At k t a k' -> In k t k'.
  Proof.
    intros.
    induction t.
    - inversion H; subst. constructor.
    - inv_tr H.
      apply In_Other.
      * apply IHt. assumption.
      * constructor.
  Qed.

  Lemma no_def_untouched :
    forall p q x, is_def x q p = false -> forall i j s r, eff (q, j, r) = Some (p, i, s) -> r x = s x.
  Proof.
    intros.
    specialize (def_spec q p x).
    cut (forall (a b : Prop), (a -> b) -> (~ b -> ~ a)); intros Hrev; [| eauto].
    apply Hrev in def_spec.
    - cut (forall x y : Val, ~ (x <> y) -> x = y).
      * intros.
        apply H1; clear H1.
        intro. apply def_spec.
        exists j; exists i; exists r; exists s; auto.
      * intros y z. destruct (equiv_dec y z); intros; auto.
        exfalso. apply H1. auto.
    - intro.
      rewrite H in H1.
      inversion H1.
  Qed.

  Lemma unch_correct :
    forall unch k t,
      sem_trace (unch_concr unch) k t -> unch_concr (unch_trans unch) k t.
  Proof.
    intros unch k t Hsem.
    destruct Hsem as [k' [t' [step [Hconcr Hstep]]]]; subst.
    unfold unch_concr.
    intros x to i s HIn.
    unfold unch_concr in Hconcr.
    assert (unch_trans unch to x = unch_trans unch to x) by reflexivity.
    assert (Hspec := unch_trans_spec unch to x (unch_trans unch to x) H).
    clear H.
    inversion Hspec.
    - assert (Hfollow := HIn).
      destruct H as [Hroot H].
      eapply follows_exists in Hfollow; [| eauto].
      destruct Hfollow as [[[q j] r] Hfollow].
      specialize (unch_trans_local_spec q to x unch).
      specialize (H q).
      remember (is_def x q to) as def.
      destruct def; rewrite unch_trans_local_spec in H.
      * rewrite <- H.
        exists i; exists s; split; eauto.
      * unfold unch_concr in Hconcr.
        assert (Hstep := Hfollow).
        apply follows_implies_in2_step in Hfollow.
        apply follows_implies_step in Hstep.
        rewrite <- H in *.
        specialize (Hconcr x q j r Hfollow).
        destruct Hconcr as [h [u [Hfromin Hfromeq]]].
        exists h; exists u.
        split; try (constructor; assumption).
        cut (s x = r x).
        ** intros Heq_qp.
           rewrite Heq_qp.
           assumption.
        ** symmetry in Heqdef.
           symmetry.
           eapply no_def_untouched; try eassumption.
    - exists i; exists s.
      rewrite H.
      auto.
  Qed.

  Definition lift (tr : Traces) : Hyper :=
    fun ts => ts = tr.

  Lemma uni_correct :
    forall uni hom unch t,
        sem_hyper (red_prod (red_prod (uni_concr uni) (hom_concr hom)) (lift (unch_concr unch))) t ->
        uni_concr (uni_trans uni hom unch) t.
  Proof.
    intros uni hom unch t Hred.
    unfold sem_hyper in Hred.
    destruct Hred as [ts [Hconcr Hstep]]; subst.
    destruct Hconcr as [[HCuni HChom] HCunch].

    split.
    unfold uni_concr in HCuni.
    destruct HCuni as [Hall _].
    eapply all_closed; auto.

    intros k k' tr tr' Hsem Hsem' x p i s s'.
    intros HIn HIn' Htrans.

    unfold uni_trans in Htrans. 
    destruct HCuni as [Hall HCuni].
    assert (ts k tr) as Hts by (eapply all_trace; eassumption).
    assert (ts k' tr') as Hts' by (eapply all_trace; eassumption).

    destruct (equiv_dec p root).
    + rewrite e in *; clear e.
      destruct Hsem as [l [ltr [lstep [Hlin Hlstep]]]].
      destruct Hsem' as [l' [ltr' [lstep' [Hlin' Hlstep']]]].
      (* unfold uni_concr in HCuni. *)
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
        cut (q = q' /\ j = j'); intros.
        * inversion_clear H as [Hq Hj]; subst j' q'.
          unfold uni_state_concr in *.
          eapply (local_uni_corr (uni q) q j p i sq sq' s s').
          ** intros.
             eapply (HCuni k k' tr tr' Hts Hts' x0 q j); try eapply follows_implies_in2; eassumption.
          ** eapply follows_implies_step; eassumption.
          ** eapply follows_implies_step; eassumption.
          ** apply Hpred.
             eapply edge_spec.
             unfold is_effect_on.
             exists j. exists i. exists sq. exists s. eapply follows_implies_step. apply Hflw.
        * clear HCuni. subst.
          destruct HChom as [_ HChom].
          eapply (HChom k k' tr tr'); try eassumption.
      - clear HChom.
        rename c into HProot.
        remember (unch p x) as q; symmetry in Heqq.
        rename Hunch into Huniq.
        unfold lift in HCunch; subst.
        unfold unch_concr in Hts.
        assert (Hconcr := Hts x p i s HIn).
        assert (Hconcr' := Hts' x p i s' HIn').
        destruct Hconcr as [j [r [Hin_from Heq]]].
        destruct Hconcr' as [j' [r' [Hin_from' Heq']]].
        cut (j = j'); intros.
        * subst j'.
          apply all_trace in Hsem; try eassumption.
          apply all_trace in Hsem'; try eassumption.
          rewrite Heq. rewrite Heq'.
          eapply (HCuni k k' tr tr' Hsem Hsem' x (unch p x) j r r' Hin_from Hin_from' Huniq).
        * admit.
Qed.