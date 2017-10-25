Require Import Coq.Classes.EquivDec.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Eqdep_dec.
Require Import List.
Require Import Nat.
Require Import Omega.
Require Import Ensembles.

Module CFG.
  Parameter N : nat.
  Parameter Lab : Type.
  Parameter Var : Type.
  Parameter Val : Type.
  Parameter init_uni : Var -> Prop.

  Definition IVec := (list nat).
  Definition State := Var -> Val.
  Definition States := State -> Prop.
  Definition Coord := prod Lab IVec.
  Definition Conf := prod Coord State.

  Definition UniState := Var -> Prop.
  Definition UnchState := Var -> Lab.

  Parameter eff : Conf -> option Conf.
  Parameter abs_uni_eff : UniState -> UniState.
  Parameter abs_unch_eff : UnchState -> UnchState.

  Definition uni_state_concr (uni : UniState) : State -> State -> Prop :=
    fun s => fun s' => forall x, uni x -> s x = s' x.

  Parameter local_uni_corr : forall uni p i q j s s' qs qs', 
      uni_state_concr uni s s' ->
      eff (p, i, s) = Some (q, j, qs) ->
      eff (p, i, s') = Some (q, j, qs') ->
      uni_state_concr (abs_uni_eff uni) qs qs'.

  Parameter has_edge : Lab -> Lab -> bool.
  Parameter is_def : Var -> Lab -> Lab -> bool.
  Parameter root : Lab.
  Parameter Lab_dec : forall (x y : Lab), {x = y} + {x <> y}.
  Parameter Val_dec : forall (x y : Val), {x = y} + {x <> y}.
  Parameter Conf_dec : forall (x y : Conf), {x = y} + {x <> y}.
  Program Instance lab_eq_eqdec : EqDec Lab eq := Lab_dec.
  Program Instance val_eq_eqdec : EqDec Val eq := Val_dec.
  Program Instance conf_eq_eqdec : EqDec Conf eq := Conf_dec.

  Definition start_ivec := @nil nat.

  Definition start_coord := (root, start_ivec) : Coord.

  Definition is_effect_on (p q : Lab) :=
    exists i i' s s', eff ((p, i), s) = Some ((q, i'), s').

  Parameter root_no_pred : forall p, has_edge p root = false.

  Parameter edge_spec :
    forall p q, is_effect_on p q -> has_edge p q = true.

  Parameter def_spec :
    forall p q x, (exists i j s r, eff (p, i, s) = Some (q, j, r) /\ r x <> s x) -> is_def x p q = true.

  Parameter nesting : Lab -> Lab -> Prop.
  Notation "a <<= b" := (nesting a b) (at level 70, right associativity).
  Parameter nesting_dec : forall x y : Lab, { x <<= y } + { ~ x <<= y }.
  Parameter nesting_root : forall l, root <<= l.

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
  Inductive Tr : Conf -> Type :=
    | Init : forall s, Tr (start_coord, s)
    | Step : forall k k', Tr k' -> eff k' = Some k -> Tr k.

  Ltac inv_tr H := inversion H; subst; 
                   repeat match goal with
                          | [ H0: @existT Conf _ _ _ = @existT _ _ _ _  |- _ ] => apply inj_pair2_eq_dec in H0;
                                                                                  try (apply Conf_dec); subst
                          end.

  Definition Traces := forall k, Tr k -> Prop.
  Definition Hyper := Traces -> Prop.

  (* This is the concrete transformer for sets of traces *)
  Definition sem_trace (ts : Traces) : Traces :=
    fun k' => fun tr' => exists k tr step, ts k tr /\ tr' = (Step k' k tr step).

  (* This is the hypertrace transformer.
     Essentially, it lifts the trace set transformers to set of trace sets *)
  Definition sem_hyper (T : Hyper) : Hyper :=
    fun ts' => exists ts, T ts /\ ts' = sem_trace ts.

  Definition Uni := Lab -> Var -> Prop.
  Definition Hom := Lab -> Prop.
  Definition Unch := { unch: Lab -> Var -> Lab | forall p x, unch p x <<= p }.

  Inductive In : forall k, Tr k -> Conf -> Prop := (* (k : Conf) (tr : Tr k) : Conf -> Prop :=  *)
    | In_At : forall k tr, In k tr k
    | In_Other : forall l k k' tr' step, In k' tr' l -> In k (Step k k' tr' step) l.

  Parameter ivec_fresh : forall p i s k t, Some (p, i, s) = eff k ->
                                           forall q j r, In k t (q, j, r) ->
                                                         j <> i.

  Inductive Follows : forall k, Tr k -> Conf -> Conf -> Prop := 
  | Follows_At : forall k pred pred_tr step, Follows k (Step k pred pred_tr step) k pred
  | Follows_Other : forall succ pred k k' tr' step, Follows k' tr' succ pred ->
                                                    Follows k (Step k k' tr' step) succ pred.

  Inductive Precedes : forall k, Tr k -> Conf -> Conf -> Prop :=
  | Prec_in : forall k t, Precedes k t k k
  | Prec_cont : forall k t q p i j r s step, Precedes k t (q, j, r) k -> 
                                             p <> q ->
                                             Precedes (p, i, s) (Step (p, i, s) k t step) (q, j, r) (p, i, s)
  | Prec_other : forall k' k t c c' step, Precedes k t c c' ->
                                          Precedes k' (Step k' k t step) c c'.

  Parameter ivec_nesting : forall k k' t t' p q j j' i i' r r' s s',
      Precedes k t (q, j, r) (p, i, s) ->
      Precedes k' t' (q, j', r') (p, i', s') ->
      q <<= p ->
      j' = j /\ r = r'.

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
    fun ts => all ts /\
              forall t t' tr tr', ts t tr -> ts t' tr' ->
                                  forall x p i s s', In t tr ((p, i), s) ->
                                                     In t' tr' ((p, i), s') ->
                                                     u p x -> s x = s' x.

  Definition hom_concr (h : Hom) : Hyper :=
    fun ts => all ts /\
              forall t t' tr tr', ts t tr -> ts t' tr' ->
                                  forall p, h p ->
                                            forall q q' j j'
                                                   i s s'
                                                   s1 s2, Follows t tr ((p, i), s1) ((q, j), s) ->
                                                          Follows t' tr' ((p, i), s2) ((q', j'), s')  ->
                                                          q = q' /\ j = j'.

  
  Definition unch_hyper_concr (unch : Unch) : Hyper :=
    fun ts => all ts /\
              forall k t to i s x, ts k t ->
                                   In k t (to, i, s) ->
                                   exists j r, Precedes k t (proj1_sig unch to x, j, r) (to, i, s) /\ r x = s x.
                                  
  (*
  Definition unch_hyper_concr (unch : Unch) : Hyper :=
    fun ts => all ts /\
              forall k t to i s x, In k t (to, i, s) ->
                                   exists j r, Precedes k t (unch to x, j, r) (to, i, s) /\ s x = r x /\
                                               forall k' t' s', In k' t' (to, i, s') -> exists r',
                                                   Precedes k' t' (unch to x, j, r') (to, i, s') /\
                                                   s' x = r' x.
   *)
  
  Definition unch_concr (unch : Unch) : Traces :=
    fun k => fun t => forall to i s x, In k t (to, i, s) ->
                                       exists j r, Precedes k t (proj1_sig unch to x, j, r) (to, i, s) /\ r x = s x.

  Definition unch_trans_local : Unch -> Lab -> Lab -> Var -> Lab.
    refine(fun unch => fun q => fun p => fun x => if is_def x q p then p else
                                                    if nesting_dec q p then proj1_sig unch q x else
                                                      p).
                                                             

  Variable unch_trans_local : Unch -> Lab -> Lab -> Var -> Lab.
  Variable unch_trans_local_spec :
    forall q p x unch, if is_def x q p then unch_trans_local unch q p x = p
                       else unch_trans_local unch q p x = proj1_sig unch q x.

  Variable unch_trans : Unch -> Unch.
  Variable unch_trans_spec :
    forall unch p x, (p =/= root /\ forall q, unch_trans_local unch q p x = proj1_sig (unch_trans unch) p x)
                     \/ proj1_sig (unch_trans unch) p x = p.
    
  Definition uni_trans (uni : Uni) (hom : Hom) (unch : Unch) : Uni :=
    fun p => if p == root then uni root
             else fun x => (hom p /\ forall q, has_edge q p = true -> abs_uni_eff (uni q) x)
                             \/ uni (proj1_sig unch p x) x.
             
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

  Lemma follows_implies_in :
    forall k t succ pred, Follows k t succ pred -> In k t succ.
  Proof.
    intros k t.
    induction t; intros; inv_tr H.
    - constructor.
    - econstructor. eauto.
  Qed.

  Lemma precedes_self :
    forall k t c, In k t c -> Precedes k t c c.
  Proof.
    intros.
    induction t.
    + inv_tr H.
      constructor.
    + destruct (equiv_dec c k).
      * rewrite e0 in *.
        constructor.
      * destruct c as [[q j] r].
        destruct k as [[p i] s].
        constructor.
        apply IHt.
        inv_tr H.
        - exfalso. apply c0. reflexivity.
        - assumption.
  Qed.

  Lemma precedes_implies_in : 
    forall k t c c', Precedes k t c c' -> In k t c.
  Proof.
    intros k t c.
    induction t; intros; inv_tr H; constructor; eauto.
   Qed.

  Lemma precedes_implies_in_to : 
    forall k t c c', Precedes k t c c' -> In k t c'.
  Proof.
    intros k t c.
    induction t; intros; inv_tr H; constructor; eauto.
   Qed.

  Definition lab_of (k : Conf) :=
    match k with
      ((p, i), s) => p
    end.

  Lemma precedes_follows :
    forall k t c d e,
      Precedes k t c d ->
      Follows k t e d ->
      lab_of c =/= lab_of e ->
      Precedes k t c e.
  Proof.
    intros k t.
    induction t; intros c d next Hprec Hflw Hlab.
    - inv_tr Hflw.
    - destruct (equiv_dec k next).
      * rewrite <- e0 in *; clear e0.
        inv_tr Hprec.
        + constructor.
        + constructor.
          assumption. assumption.
        + destruct c as [[cp ci] cs].
          destruct k as [[kp ki] ks].
          econstructor.
          ++ assert (k' === d) by admit.
             rewrite H.
             assumption.
          ++ auto.
      * inv_tr Hflw.
        + contradiction c0; reflexivity.
        + assert (k =/= d) by admit.
          eapply Prec_other.
          inv_tr Hprec; try (exfalso; apply H; reflexivity).
          eauto.
  Admitted.
  
  Lemma no_def_untouched :
    forall p q x, is_def x q p = false -> forall i j s r, eff (q, j, r) = Some (p, i, s) -> r x = s x.
  Proof.
    intros.
    specialize (def_spec q p x).
    cut (forall (a b : Prop), (a -> b) -> (~ b -> ~ a)); intros Hrev; [| eauto].
    assert (Hds := def_spec).
    eapply Hrev in Hds.
    - cut (forall x y : Val, ~ (x <> y) -> x = y).
      * intros.
        apply H1; clear H1.
        intro. apply Hds.
        exists j; exists i; exists r; exists s; eauto.
      * intros y z. destruct (equiv_dec y z); intros; auto.
        exfalso. apply H1. auto.
    - intro.
      rewrite H in H1.
      inversion H1.
  Qed.

  Lemma precedes_self_same :
    forall k t p i s j r, Precedes k t (p, j, r) (p, i, s) -> j = i /\ r = s.
  Proof.
    induction t; intros; inv_tr H.
    + auto.
    + auto.
    + exfalso; auto.
    + eapply IHt; eapply H5.
  Qed.

  Lemma precedes_no_root :
    forall k t c p i s, Precedes k t c (p, i, s) -> lab_of c <> root -> p <> root.
  Proof.
  Admitted.

  (*
  Lemma unch_prec_correct :
    forall unch t,
      sem_hyper (unch_prec_concr unch) t -> unch_prec_concr (unch_trans unch) t.
  Proof.
    intros unch t Hred.
    unfold sem_hyper in Hred.
    destruct Hred as [ts [Hconcr Hstep]]; subst.
    unfold unch_prec_concr in *.
    intros k k' t t' j j' r r' s s' i to x Hsem Hsem' Hprec Hprec'.

    assert (Htrans := unch_trans_spec unch to x).
    destruct Htrans as [[Hroot Htrans] | Htrans].
    + assert (Hin := Hprec). apply precedes_implies_in_to in Hin.
      assert (Hin' := Hprec'). apply precedes_implies_in_to in Hin'.
      apply follows_exists_detail in Hin.
      apply follows_exists_detail in Hin'.

      destruct Hin as [q [h [u Hflw]]].
      destruct Hin' as [q' [h' [u' Hflw']]].
      assert (Htrans' := Htrans q').
      specialize (Htrans q).
      rewrite <- Htrans' in Htrans.
      assert (Hpred := unch_trans_local_spec q to x unch).
      assert (Hpred' := unch_trans_local_spec q' to x unch).

      destruct (is_def x q to), (is_def x q' to).
    - rewrite Hpred' in Htrans'.
      rewrite <- Htrans' in *.
      apply precedes_self_same in Hprec. destruct Hprec as [Hprec _].
      apply precedes_self_same in Hprec'. destruct Hprec' as [Hprec' _].
      rewrite Hprec. rewrite Hprec'. reflexivity.
    - rewrite <- Htrans in Htrans'.
      rewrite Hpred in Htrans'.
      rewrite <- Htrans' in *.
      apply precedes_self_same in Hprec. destruct Hprec as [Hprec _].
      apply precedes_self_same in Hprec'. destruct Hprec' as [Hprec' _].
      rewrite Hprec. rewrite Hprec'. reflexivity.
    - rewrite Hpred' in Htrans'.
      rewrite <- Htrans' in *.
      apply precedes_self_same in Hprec. destruct Hprec as [Hprec _].
      apply precedes_self_same in Hprec'. destruct Hprec' as [Hprec' _].
      rewrite Hprec. rewrite Hprec'. reflexivity.
    - rewrite Hpred in Htrans.
      rewrite <- Htrans in Htrans'.
      rewrite <- Htrans' in *.
      eapply Hconcr; try assumption.
      admit.
      admit.
      eapply Hprec.
    + rewrite Htrans in *.
      apply precedes_self_same in Hprec. destruct Hprec as [Hprec _].
      apply precedes_self_same in Hprec'. destruct Hprec' as [Hprec' _].
      rewrite Hprec. rewrite Hprec'. reflexivity.
      (*


          
        
        
      (*
*)
*)
  Admitted.
  *)

  Lemma unch_hyper_correct :
    forall unch t, 
      sem_hyper (unch_hyper_concr unch) t -> unch_hyper_concr (unch_trans unch) t. 
    (*
    forall unch k t,
      sem_trace (unch_concr unch) k t -> unch_concr (unch_trans unch) k t.
    *)
  Proof.
    intros unch t Hred.
    unfold sem_hyper in Hred.
    destruct Hred as [ts [Hconcr Hstep]]; subst.
    unfold unch_hyper_concr in Hconcr.
    destruct Hconcr as [Hall Hconcr].
    unfold unch_hyper_concr.
    split; [ eapply all_closed; eassumption |].
    intros k t to i s x Hsem Hin.
    assert (Htrans := unch_trans_spec unch to x).
    destruct Htrans as [[Hroot Htrans] | Htrans].
    + eapply follows_exists_detail in Hin; try auto.
      destruct Hin as [q [j [r Hflw]]].
      assert (Hpred := unch_trans_local_spec q to x unch).
      specialize (Htrans q).
      remember (is_def x q to) as xdef.
      destruct xdef.
    - rewrite Hpred in Htrans.
      rewrite <- Htrans in *.
      exists i; exists s.
      split; [| auto].
      apply precedes_self.
      eapply follows_implies_in.
      eassumption.
    - rewrite <- Htrans.
      rewrite Hpred.
      assert (Hinq := Hflw).
      destruct Hsem as [k0 [t0 [step0 [Hts Hstep]]]]; subst t.
      apply follows_implies_in2_step in Hinq.
      specialize (Hconcr k0 t0 q j r x Hts Hinq).
      destruct Hconcr as [h [u [Hprec Heq]]].
      ++ destruct (equiv_dec (proj1_sig unch q x) to).
         ** rewrite e in *.
            exists i. exists s.
            split; [| reflexivity].
            apply precedes_self.
            eapply follows_implies_in; eassumption.
         ** eapply Prec_other in Hprec.
            exists h. exists u.
            split.
            -- eapply precedes_follows; try eassumption.
            -- rewrite Heq.
               eapply no_def_untouched; [ symmetry; eassumption |].
               eapply follows_implies_step; eassumption.
      + rewrite Htrans.
        exists i; exists s.
        split; [| reflexivity].
        apply precedes_self.
        assumption.
  Qed.


  (*
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
  *)

  Definition lift (tr : Traces) : Hyper :=
    fun ts => ts = tr.

  (*
  Lemma uni_correct :
    forall uni hom unch t,
        sem_hyper (red_prod (red_prod (uni_concr uni) (hom_concr hom)) (unch_hyper_concr unch)) t ->
        uni_concr (uni_trans uni hom unch) t.
  Proof.
    intros uni hom unch t Hred.
    unfold sem_hyper in Hred.
    destruct Hred as [ts [Hconcr Hstep]]; subst.
    destruct Hconcr as [[HCuni HChom] HCunch].
    destruct HCuni as [Hall HCuni].
    unfold uni_concr.
    split; [ eapply all_closed; assumption |].
    
    intros k k' tr tr' Hsem Hsem' x p i s s'.
    intros HIn HIn' Htrans.
    unfold uni_trans in Htrans. 

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
      - apply all_trace in Hsem; try eassumption.
        apply all_trace in Hsem'; try eassumption.
        apply follows_exists in HIn; try eassumption.
        apply follows_exists in HIn'; try eassumption.
        destruct HIn as [[[q j] sq] Hflw].
        destruct HIn' as [[[q' j'] sq'] Hflw'].
    
        cut (q = q' /\ j = j'); intros.
        * inversion_clear H as [Hq Hj]; subst j' q'.
          unfold uni_state_concr in *.
          eapply (local_uni_corr (uni q) q j p i sq sq' s s').
          ** intros.
             eapply (HCuni k k' tr tr' Hsem Hsem' x0 q j); try eapply follows_implies_in2; try eassumption.
          ** eapply follows_implies_step; eassumption.
          ** eapply follows_implies_step; eassumption.
          ** apply Hpred.
             eapply edge_spec.
             unfold is_effect_on.
             exists j. exists i. exists sq. exists s. eapply follows_implies_step. apply Hflw.
        * clear HCuni. subst.
          destruct HChom as [_ HChom].
          eapply (HChom k k' tr tr'); try eassumption.
      - apply all_trace in Hsem; try eassumption.
        apply all_trace in Hsem'; try eassumption.
        destruct HCunch as [_ [Hsync HCunch]].
        assert (HCunch' := HCunch k' tr' p i s' x Hsem' HIn').
        assert (HCunch  := HCunch k tr p i s x Hsem HIn).
        destruct HCunch as [j [r [Hprec Heq]]].
        destruct HCunch' as [j' [r' [Hprec' Heq']]].
        specialize (Hsync k k' tr tr' j j' r r' s s' i (unch p x) p Hsem Hsem' Hprec Hprec').
        subst j'.
        rewrite <- Heq. rewrite <- Heq'.
        eapply (HCuni k k' tr tr' Hsem Hsem' x (unch p x) j r r'); try assumption.
        admit.
        admit.
  Admitted.
  *)

  Lemma uni_correct :
    forall uni hom unch t,
        sem_hyper (red_prod (red_prod (uni_concr uni) (hom_concr hom)) (unch_hyper_concr unch)) t ->
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
          
          eapply (local_uni_corr (uni q) q j p i sq sq' s s'); unfold uni_state_concr in *.
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

        (* The unch hyper case *)
        apply all_trace in Hsem; [|eauto].
        apply all_trace in Hsem'; [|eauto].
        unfold unch_hyper_concr in HCunch.
        destruct HCunch as [_ HCunch].
        assert (HCunch' := HCunch k' tr' p i s' x Hsem' HIn').
        assert (HCunch  := HCunch k tr p i s x Hsem HIn).
        destruct HCunch as [j [r [Hprec Heq]]].
        destruct HCunch' as [j' [r' [Hprec' Heq']]].

        cut (j = j'); intros.
        * (* specialize (Hsync k k' tr tr' j j' r r' s s' i p p p x Hsem Hsem' Hprec Hprec'). *)
          subst j'.
          rewrite <- Heq. rewrite <- Heq'.
          eapply (HCuni k k' tr tr' Hsem Hsem' x (proj1_sig unch p x) j r r'); try eassumption.
          ** eapply precedes_implies_in; eassumption.
          ** eapply precedes_implies_in; eassumption.
        * destruct unch as [unch Hunch_nest].
          eapply ivec_nesting; try eauto.
Qed.

          
      (* The unch non-hyper case 
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
       *)
Qed.