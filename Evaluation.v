Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Utils.
Require Import Coq.Logic.Classical.
Require Import List.
Require Import Nat.
Require Import Bool.Bool.
Require Import Coq.Logic.Eqdep_dec.

Require Graph NeList.
Require Import Util.

Module Evaluation.

  Export Graph.TCFG Graph.CFG NeList.NeList. 

  Parameter Val : Type.

  Definition State := Var -> Val.

  Variable Val_dec : EqDec Val eq.
  Variable Tag_dec : EqDec Tag eq.
  Variable State_dec : EqDec State eq.

  
  Parameter start_tag : Tag.

  Definition States := State -> Prop.
  Definition Conf := prod Coord State.

  Hint Unfold Conf Coord.

  Definition lab_of (k : Conf) :=
    match k with
      ((p, i), s) => p
    end.

  Parameter eff' : Lab * State -> option (Lab * State).
  
  Definition eff (k : Conf) : option Conf
    := match k with
       | (p, i, s) => match eff' (p,s) with
                  | None => None
                  | Some (q, r) => Some (q, eff_tag p q i, r)
                  end
       end.

  Program Instance conf_eq_eqdec : EqDec Conf eq.
  Next Obligation.
    intros.
    destruct x as [[p i] s], y as [[q j] r].
    destruct ((p, i, s) == (q, j, r)); firstorder.
  Qed.
  Definition Conf_dec := conf_eq_eqdec.

  Definition is_effect_on (p q : Lab) :=
    exists i i' s s', eff ((p, i), s) = Some ((q, i'), s').
  Parameter zero : State.

  Parameter edge_spec :
    forall p q, is_effect_on p q -> p --> q.

  Lemma step_conf_implies_edge :
    forall p q i j s r, eff (p, i, s) = Some (q, j, r) -> (p --> q).
  Proof.
    intros.
    eapply edge_spec. 
    unfold is_effect_on. eauto.
  Qed.

  Lemma eff_eff_tag q j r p i s :
    eff (q,j,r) = Some (p,i,s)
    -> eff_tag q p j = i.
  Admitted.
  
  Program Instance EvalGraph : Graph Conf (start_coord,zero)
                                     (fun k k' => match eff k return Prop with
                                                 Some k => k = k' | None => False end).
  Next Obligation.
    destruct (eff p); [apply conf_eq_eqdec|tauto].
  Qed.
  Next Obligation.
    intro N. destruct (eff p) eqn:E.
    - subst c. destruct p,c. apply step_conf_implies_edge in E. apply root_no_pred' in E. assumption.
    - contradiction.
  Qed.

  Parameter def_spec :
    forall p q x, (exists i j s r, eff (p, i, s) = Some (q, j, r) /\ r x <> s x) ->
                  is_def x p q = true.

  Inductive Tr : ne_list Conf -> Prop :=
  | Init : forall s, Tr (ne_single (root, start_tag, s))
  | Step : forall l k, Tr l -> eff (ne_front l) = Some k -> Tr (k :<: l).

  Definition EPath := @Path _ _ _ EvalGraph.
  
  Goal forall (V X Y Z : Type) (x:X) (y:Y) (P : V -> Prop), (X -> Y -> V) -> (forall v:V, P v -> X -> Y -> Z) -> (forall v, P v) -> Z.
    intros V X Y Z x y P Hxy Hv HP. 
    exploit Hxy. exploit Hv. exact Hv.
  Qed.
  
  Lemma EPath_Tr s0 p i s π :
    Path (root,start_tag,s0) (p,i,s) π -> Tr π.
  Proof.
    intro H. 
    dependent induction H; [|destruct b,p0]; econstructor.
    - eapply IHPath; eauto.
    - erewrite path_front; eauto. destruct (eff (l,t,s1)); [subst c; eauto|contradiction].
  Qed.

  Lemma Tr_EPath p i s π :
    Tr π ->  ne_front π = (p,i,s) -> exists s0, Path (root,start_tag,s0) (p,i,s) π.
  Proof.
    intros HTr Hfront. exists (snd (ne_back π)).
    revert p i s Hfront. dependent induction HTr; cbn; intros p i s' Hfront.
    - cbn in *. rewrite <-Hfront; econstructor.
    - rewrite <-Hfront.
      econstructor; [eapply IHHTr; eauto|].
      + repeat rewrite <-surjective_pairing. reflexivity.
      + replace (eff (_,_,_)) with (eff (ne_front l));
          [|f_equal; repeat rewrite <-surjective_pairing; reflexivity].
        destruct (eff _); inversion H; reflexivity.
  Qed.

  Lemma EPath_TPath k k' π :
    EPath k k' π -> TPath (fst k) (fst k') (ne_map fst π).
  Proof.
    intros H. dependent induction H; [|destruct c]; econstructor.
    - apply IHPath.
    - repeat destr_let. destruct (eff _) eqn:E; [|contradiction]. split.
      + subst c; eapply step_conf_implies_edge; eauto.
      + unfold eff in E. destruct (eff' _) eqn:E'; [|congruence]. destruct p. destruct c,c.
        inversion E. inversion H0. subst. reflexivity.
  Qed.

  Ltac inv_dep H Dec := inversion H; subst; 
                        repeat match goal with
                               | [ H0: @existT _ _ _ _ = @existT _ _ _ _  |- _ ]
                                 => apply inj_pair2_eq_dec in H0; try (apply Dec); subst
                               end.

  Ltac inv_tr H := inversion H; subst; 
                   repeat match goal with
                          | [ H0: @existT Conf _ _ _ = @existT _ _ _ _  |- _ ]
                            => apply inj_pair2_eq_dec in H0; try (apply Conf_dec); subst
                          end.

  Definition trace := {l : ne_list Conf | Tr l}.

  Open Scope prg.

  Definition Traces := trace -> Prop.
  Definition Hyper := Traces -> Prop.

  (* This is the concrete transformer for sets of traces *)
  Definition sem_trace (ts : Traces) : Traces :=
    fun tr' => exists tr k', ts tr /\ `tr' = (k' :<: `tr).

  (* This is the hypertrace transformer.
     Essentially, it lifts the trace set transformers to set of trace sets *)
  Definition sem_hyper (T : Hyper) : Hyper :=
    fun ts' => exists ts, T ts /\ ts' = sem_trace ts.

  Lemma ne_hd_hd {A : Type} (a : A) l : a = ne_front l -> Some a = hd_error l.
  Proof.
    intros H.
    induction l; cbn in *; subst a; reflexivity.
  Qed.

  Lemma in_succ_in k p q t :
    Tr (nlcons k t) -> In p t -> eff p = Some q -> In q (k :: t).
  Proof.
    intros.
    revert dependent k. dependent induction t; intros k H; inv_tr H; try firstorder.
    + rewrite nlcons_front in H5. subst a. rewrite H5 in H1. inversion H1. left. reflexivity.
  Qed.

  Lemma in_pred_exists p i s k t :
    In (p,i,s) (k :<: t) ->
    p =/= root ->
    Tr (k :<: t) ->
    exists q j r, In (q, j, r) t /\ eff (q, j, r) = Some (p, i, s).
  Proof.
    revert k.
    dependent induction t; intros k Hin Hneq Htr; inversion Htr.
    - destruct Hin; subst.
      + destruct a as [[q j] r]. exists q,j,r.
        split; cbn; eauto.
      + exfalso. eapply Hneq. inversion H1.
        destruct a,p0. inversion H0; inversion H3; subst; [inversion H;reflexivity |contradiction]. 
    - destruct Hin; subst.
      + destruct a as [[q j] r].
        exists q, j, r. split; [ constructor | assumption ]. reflexivity.
      + edestruct IHt as [q [j [r [Hinq Hstep]]]]; try eassumption.
        exists q, j, r. 
        split; eauto.
        cbn. tauto.
  Qed.

  Lemma ivec_fresh : forall p i s (t : trace),
      eff (ne_front (`t)) = Some (p, i, s) -> forall j r, In (p, j, r) (`t) -> j <> i.
  Proof.
    intros.
    destruct t; cbn in *.
    remember (ne_front x) as c. destruct c,c. 
    eapply eff_tag_fresh.
    - eapply Tr_EPath in t;eauto. destruct t as [s1 t].
      eapply EPath_TPath in t; eauto.
    - eapply eff_eff_tag; eauto.
    - eapply ne_map_in with (f:=fst) in H0. eauto.
  Qed.
  
  Lemma ivec_det : forall q j r r' p i i' s s',
      eff (q, j, r) = Some (p, i, s) ->
      eff (q, j, r') = Some (p, i', s') ->
      i = i'.
  Proof.
    intros.
    eapply eff_tag_det;eapply eff_eff_tag; eauto.
  Qed.
                                                    
  Inductive Precedes : list Conf -> Conf -> Prop :=
  | Pr_in : forall k l, Precedes (k :: l) k
  | Pr_cont : forall c k l, lab_of c <> lab_of k -> Precedes l k -> Precedes (c :: l) k.

  Definition Precedes' (l : list Conf) (k k' : Conf) : Prop :=
    exists l', Prefix (k' :: l') l /\ Precedes (k' :: l') k.

  Lemma precedes_implies_in_pred k t :
    Precedes t k -> In k t.
  Proof.
    intros H.
    dependent induction t.
    - inv_tr H. 
    - inv_tr H; eauto using In; cbn; eauto.
  Qed.

  Lemma start_no_tgt :
    forall i' s' k, eff k = Some (root, i', s') -> False.
  Proof.
    intros. 
    destruct k as [[p i] s].
    unfold start_coord in H.
    cut (is_effect_on p root); intros.
    apply edge_spec in H0.
    eapply root_no_pred'. eassumption.
    unfold is_effect_on.
    exists i, i', s, s'. 
    assumption.
  Qed.

  Lemma precedes_cons (k k' : Conf) l : Precedes' l k' k' -> Precedes' (k :: l) k' k'.
  Proof.
    intro H. destruct H as [l' [H1 H2]].
    unfold Precedes'.
    exists l'. split; econstructor. eauto.
  Qed.
  
  Lemma precedes_self c t :
    In c t -> Precedes' t c c.
  Proof.
    intros H.
    destruct c as [[p i] s].
    induction t.
    + inv_tr H. 
    + destruct a as [[q j] r].
      inv_tr H; eauto using Precedes.
      * rewrite H0. exists t. split; econstructor.
      * eapply precedes_cons; eauto. 
  Qed.

  Lemma precedes_step_inv :
    forall k t p s, Precedes' (nlcons k t) p s ->
               Tr (nlcons k t) ->
               lab_of p =/= lab_of s ->
               In p t.
  Proof.
    intros.
    destruct H as [l [Hpre Hprec]].
    inv_tr Hprec.
    - firstorder.
    - eapply precedes_implies_in_pred in H5.
      rewrite <-nlcons_to_list in Hpre. eapply prefix_cons_cons in Hpre.      
      eapply in_prefix_in; eauto.
  Qed.

  Lemma in_exists_pred p i s k (t : trace) :
    In (p, i, s) (k :<: `t) ->
    eff (ne_front (`t)) = Some k ->
    p <> root ->
    exists q j r, In (q, j, r) (`t) /\ eff (q, j, r) = Some (p, i, s).
  Proof.
    intros H Heff Hneq.
    destruct t as [l tr]; cbn in H, Heff. unfold "`".
    destruct H; [subst k| revert dependent k];
      dependent induction l; inversion tr; subst; intros. 
    - exists root, start_tag, s0. split; [ constructor | eauto ]; eauto.
    - cbn in Heff, H2. destruct a as [[q j] r]. exists q,j,r. firstorder. cbn. left; reflexivity.
    - exfalso. inversion H; inversion H0. subst p; contradiction.
    - destruct H.
      + subst a. remember (ne_front l) as qjr. destruct qjr as [[q j] r].
        exists q,j,r. split; [econstructor 2 | eauto]. setoid_rewrite Heqqjr.
        clear; destruct l; cbn; eauto.
      + eapply IHl in H2; eauto. destruct H2 as [q [j [r [Hin Hstep]]]].
        exists q, j, r. split; eauto. econstructor 2; eauto.
  Qed.

  Lemma root_prefix (t : trace) : exists s, Prefix ((root, start_tag, s) :: nil) (`t).
  Proof.
    destruct t as [l tr].
    induction l; inversion tr; subst; cbn in *.
    - exists s. econstructor.
    - destruct IHl as [s IHl']; eauto. exists s. econstructor; eauto.
  Qed.
  
  Lemma root_start_tag s i (t : trace) : In (root, i, s) (`t) -> i = start_tag.
  Proof.
    intros Hin.
    revert dependent i.
    destruct t as [l tr]. induction l; inversion tr; subst; cbn in *; intros i Hin.
    - destruct Hin as [Hin|Hin]; [inversion Hin; eauto|contradiction].
    - destruct Hin.
      + exfalso. destruct (ne_front l) as [[q j] r]. eapply root_no_pred'. subst a.
        apply edge_spec. unfold is_effect_on. exists j,i,r,s. eapply H2.
      + eapply IHl; eauto.
  Qed.

  Lemma trace_destr_in_in k k' (t : trace) :
    In k (`t) -> In k' (`t)
    -> exists (t': trace), ne_front (`t') = k' /\ In k (`t') \/ ne_front (`t') = k /\ In k' (`t').
  Proof.
    intros Hin Hin'.
    destruct t as [t tr]. cbn in *.
    induction t; inversion tr; cbn in *.
    - destruct Hin; [|contradiction]; destruct Hin'; [|contradiction].
      exists (exist _ (ne_single a) tr). cbn. tauto.
    - destruct Hin, Hin'; [| | |eapply IHt; eauto]; subst.
      + exists (exist _ (k' :<: t) tr ). cbn. tauto.
      + exists (exist _ (k :<: t) tr). cbn. tauto.
      + exists (exist _ (k' :<: t) tr). cbn. tauto.
  Qed.

  Ltac trace_proj t :=
    lazymatch goal with
    | [ H : Tr t |- _ ] =>
      replace t with ( ` (exist Tr t H)) in * by (cbn; reflexivity)
    end.
  
  Lemma tag_inj p i s r (t : trace) : In (p,i,s) (`t) -> In (p,i,r) (`t) -> s = r.
  Proof.
    intros His Hir. eapply trace_destr_in_in in His; eauto.
    destruct His as [[t' tr'] [[Hf Hin]|[Hf Hin]]]; cbn in *.
    - induction t'; inversion tr'.
      + cbn in Hin,Hf. destruct Hin; [|contradiction]. subst a. inversion H. reflexivity.
      + cbn in *. subst. destruct Hin; [inversion H; reflexivity|].
        trace_proj t'.
        eapply ivec_fresh in H2; eauto. contradiction.
    - induction t'; inversion tr'.
      + cbn in Hin,Hf. destruct Hin; [|contradiction]. subst a. inversion H. reflexivity.
      + cbn in *. subst a. destruct Hin; [inversion H3; reflexivity|].
        trace_proj t'. eapply ivec_fresh in H2; eauto. contradiction.
  Qed.

  Lemma prefix_eff_cons_cons k k' l l' l'':
    eff (ne_front l) = Some k
    -> l' = ne_to_list l''
    -> Tr (k' :<: l'')
    -> Prefix l l'
    -> Prefix (k :: l) (k' :: l').
  Proof.
    intros Heff leq Htr Hpre. 
    revert dependent k'. revert dependent l''. dependent induction Hpre; intros l'' leq k' Htr.
    - apply ne_to_list_inj in leq. subst l.
      inversion Htr. subst. rewrite H2 in Heff. inversion Heff. subst k. econstructor.
    - econstructor. destruct l'.
      { inversion Hpre. destruct l; cbn in H1; congruence. }
      eapply IHHpre; eauto.
      + apply nlcons_to_list.
      + enough ((a :<: nlcons c l') = l'') as leqq.
        { inversion Htr. rewrite leqq. assumption. }
        clear - leq. destruct l''; [|destruct l'']; destruct l'; cbn in *; inversion leq; subst;eauto.
        * destruct l''; cbn in H2; congruence.
        * destruct l''.
          -- inversion H2. subst. cbn. reflexivity.
          -- Set Printing Coercions. rewrite nlcons_to_list in H2. apply ne_to_list_inj in H2.
             rewrite H2. reflexivity. Unset Printing Coercions.
  Qed.                                              
  
  Lemma precedes_succ (t : trace) q j r q' j' r' p i s k' :
    Precedes' (`t) (q', j', r') (q, j, r) ->
    eff (q, j, r) = Some (p, i, s) ->
    p =/= q' ->
    Tr (k' :<: (`t)) ->
    Precedes' (k' :<: (`t)) (q', j', r') (p, i, s).
  Proof.
    intros Hprec Heff Hneq Htr.
    destruct Hprec as [t' [Hpre Hprec]].
    exists (nlcons (q,j,r) t').
    split.
    - clear Hprec Hneq. 
      unfold Conf in Hpre. unfold Coord in Hpre.
      set (t2 := (q,j,r) :: t') in *.
      destruct t as [t tr]. cbn.
      eapply prefix_eff_cons_cons; eauto; unfold "`" in *.
      + rewrite nlcons_front; eauto.
      + rewrite <-nlcons_to_list. subst t2; eauto.
    - econstructor; cbn; eauto.
      rewrite <-nlcons_to_list. eauto.
  Qed.
  
  Lemma precedes_step l q j r p i s :
    forall k, In (q, j, r) l ->
         p =/= q ->
         eff (q, j, r) = Some (p, i, s) ->
         Tr (nlcons k l) -> 
         Precedes' (nlcons k l) (q, j, r) (p, i, s).
  Proof.
    intros k Hin Hneq Heff Htr.
    assert (In (p,i,s) (nlcons k l)) as Hin'.
    {
      revert dependent k.
      induction l; intros k Htr; cbn in Htr; inversion Htr; inversion Hin; cbn; subst.
      - left. rewrite nlcons_front in H2. rewrite H2 in Heff. inversion Heff. reflexivity.
      - right. eauto.
    }
    exists (prefix_nincl (p,i,s) (nlcons k l)). split.
    - eapply prefix_nincl_prefix; eauto.
    - revert dependent k. induction l; intros k Htr Hin'; inversion Hin; inversion Hin'; subst.
      + cbn. destruct ((p,i,s) == (p,i,s)); [destruct e|exfalso; eapply c; reflexivity].
        econstructor; [cbn; eauto|]. destruct l; cbn; econstructor.
      + exfalso.
        unfold nlcons in Htr. fold (nlcons (q,j,r) l) in Htr.
        inversion Htr; subst.
        eapply ivec_fresh.
        * rewrite <-Heff. instantiate (1:=exist _ _ H2). unfold "`". rewrite nlcons_front. reflexivity.
        * cbn. eauto.
        * reflexivity.
      + exfalso.
        unfold nlcons in Htr. fold (nlcons a l) in Htr.
        inversion Htr; subst. 
        eapply ivec_fresh.
        * setoid_rewrite <-H3. instantiate (1:=exist _ _ H2). unfold "`". rewrite nlcons_front.
          reflexivity.
        * cbn; rewrite <-nlcons_to_list. eapply in_succ_in in H; eauto. 
        * reflexivity.
      + unfold nlcons. fold (nlcons a l). cbn. destruct ((p,i,s) == k).
        * destruct e. exfalso.
          inversion Htr; subst.
          eapply ivec_fresh.
          -- setoid_rewrite <-H4. instantiate (1:=exist _ _ H3). unfold "`". rewrite nlcons_front.
             reflexivity.
          -- cbn. eauto.
          -- reflexivity.
        * eapply IHl; eauto. cbn in Htr. inversion Htr; subst; eauto.
  Qed.

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
  
  Definition lift (tr : Traces) : Hyper :=
    fun ts => ts = tr.

  Definition red_prod (h h' : Hyper) : Hyper :=
    fun ts => h ts /\ h' ts.

  Lemma postfix_rcons_trace_eff l k k' l' :
    Tr l'
    -> Postfix ((l :r: k) :r: k') l'
    -> eff k' = Some k.
  Proof.
  Admitted.
  
  Lemma prefix_trace (l l' : ne_list Conf) :
    Prefix l l' -> Tr l' -> Tr l.
  Admitted.

  Lemma prefix_incl {A : Type} :
    forall l l' : list A, Prefix l l' -> incl l l'.
  Admitted.
    
  Lemma Tr_CPath l :
    Tr l -> CPath root (fst (fst (ne_front l))) (ne_map fst (ne_map fst l)).
  Proof.
    intro H. eapply Tr_EPath in H;[| repeat rewrite <-surjective_pairing; reflexivity].
    destruct H as [s0 H]. cbn. 
    eapply EPath_TPath in H. cbn in H. eapply TPath_CPath in H. eauto.
  Qed.

  Definition Tr' (l : ne_list Conf) :=
    exists l', Tr l' /\ Postfix l l'.

 
  Definition EPath' `{Graph} π := EPath (ne_front π) (ne_back π) π.

  
  Lemma ne_back_trace t :
    Tr t -> exists s, ne_back t = (root,start_tag,s).
  Proof.
    intro Htr.
    induction Htr; firstorder. exists s. cbn; reflexivity.
  Qed.
  
End Evaluation.
