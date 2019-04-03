Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Utils.
Require Import Coq.Logic.Classical.
Require Import List.
Require Import Nat.
Require Import Bool.Bool.
Require Import Coq.Logic.Eqdep_dec.

Require Export Tagged.

Section eval.

  Context `{C : redCFG}.
  
  Parameter root_no_pred' : forall p, p --> root -> False.

  Parameter Var : Type.
  Parameter Var_dec : EqDec Var eq.
  Parameter is_def : Var -> Lab -> Lab -> bool.

  Parameter def_edge :
    forall p q x, is_def x p q = true -> p --> q.

  Definition is_def_lab x p := exists q, is_def x q p = true.

  Lemma Lab_var_dec :
    forall (x y : (Lab * Var)), { x = y } + { x <> y }.
  Proof.
    intros.
    destruct x as [xa xb], y as [ya yb].
    destruct ((xa, xb) == (ya, yb)); firstorder.
  Qed.
  Program Instance lab_var_eq_eqdec : EqDec (Lab * Var) eq := Lab_var_dec.
  
  Parameter Val : Type.

  Definition State := Var -> Val.

  Parameter Val_dec : EqDec Val eq.
  Parameter Tag_dec : EqDec Tag eq.
  Parameter State_dec : EqDec State eq.

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
  Proof.
    intros Heff. unfold eff in Heff.
    destruct (eff' (q,r)) eqn:E;cbn in Heff. 1:revert Heff;destr_let;intros Heff.
    - inversion Heff;reflexivity.
    - congruence.
  Qed.

  Definition eval_edge := (fun k k' : Conf
                           => match eff k with
                             | Some k => k ==b k'
                             | None => false
                             end).
  
  Parameter def_spec :
    forall p q x, (exists i j s r, eff (p, i, s) = Some (q, j, r) /\ r x <> s x) ->
             is_def x p q = true.

  Inductive Tr : ne_list Conf -> Prop :=
  | Init : forall s, Tr (ne_single (root, start_tag, s))
  | Step : forall l k, Tr l -> eff (ne_front l) = Some k -> Tr (k :<: l).

  Definition EPath := Path eval_edge.

  Hint Unfold Conf Coord.
  
  Lemma EPath_Tr s0 p i s π :
    EPath (root,start_tag,s0) (p,i,s) π -> Tr π.
  Proof.
    intro H. remember (root, start_tag, s0) as start_c.
    remember (p,i,s) as pis_c. revert p i s Heqpis_c.
    induction H; intros p i s Heqpis_c; [rewrite Heqstart_c|];econstructor;destruct b as [[b1 b2] b3].
    - eapply IHPath; eauto.
    - erewrite path_front; eauto. unfold eval_edge in H0.
      unfold Conf,Coord in *.
      destruct (eff (b1,b2,b3)); [subst c; eauto|congruence].
      conv_bool. rewrite H0. reflexivity. 
  Qed.

  Lemma Tr_EPath p i s π :
    Tr π ->  ne_front π = (p,i,s) -> exists s0, EPath (root,start_tag,s0) (p,i,s) π.
  Proof.
    intros HTr Hfront. exists (snd (ne_back π)).
    revert p i s Hfront. dependent induction HTr; cbn; intros p i s' Hfront.
    - cbn in *. rewrite <-Hfront; econstructor.
    - rewrite <-Hfront.
      econstructor; [eapply IHHTr; eauto|].
      + repeat rewrite <-surjective_pairing. reflexivity.
      + unfold eval_edge. do 2 erewrite <-surjective_pairing.
        destruct (eff _); inversion H. apply beq_true. reflexivity.
  Qed.

  Lemma EPath_TPath k k' π :
    EPath k k' π -> TPath (fst k) (fst k') (ne_map fst π).
  Proof.
    intros H. dependent induction H; [|destruct c]; econstructor.
    - apply IHPath.
    - unfold eval_edge in H0. unfold tcfg_edge,tcfg_edge'. repeat destr_let.
      destruct (eff _) eqn:E; conv_bool; [|congruence]. split.
      + rewrite H0 in E. eapply step_conf_implies_edge; eauto.
      + unfold eff in E. destruct (eff' _) eqn:E'; [|congruence]. destruct p. destruct c,c.
        inversion E. inversion H0. subst. reflexivity.
  Qed.

  Lemma EPath_TPath' k k' c c' π ϕ :
    EPath k k' π -> c = fst k -> c' = fst k' -> ϕ = ne_map fst π -> TPath c c' ϕ.
  Proof.
    intros. eapply EPath_TPath in H;subst; eauto.
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
    revert dependent k. 
    dependent induction t; intros k H; inv_tr H; [firstorder|].
    + rewrite nlcons_front in H5. destruct H0;[subst a|].
      * rewrite H5 in H1. inversion H1. left. reflexivity.
      * right. eapply IHt;eauto.
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
        destruct a,p0. cbn in H3. destruct H3;[|contradiction].
        inversion H0;inversion H. reflexivity.
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
  
  Definition Precedes' (l : list Conf) (k k' : Conf) : Prop :=
    exists l', Prefix (k' :: l') l /\ Precedes lab_of (k' :: l') k.


  (*
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
   *)

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
    - eapply precedes_in in H5.
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
      + exfalso. destruct (ne_front l) as [[q j] r].
        eapply root_no_pred'. subst a.
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

  Lemma prefix_trace (l l' : ne_list Conf) :
    Prefix l l' -> Tr l' -> Tr l.
  Proof.
    intros Hpr Htr. induction Htr;cbn in *.
    - inversion Hpr;[simpl_nl' H1;rewrite H1;econstructor|]. inversion H1.
      simpl_nl' H5. contradiction.
    - inversion Hpr.
      + rewrite nlcons_to_list in H2. simpl_nl' H2. rewrite H2. econstructor;eauto.
      + eapply IHHtr;eauto.
  Qed.

  Lemma eval_det c0 c c' : eval_edge c0 c = true -> eval_edge c0 c' = true -> c = c'.
  Proof.
    intros Hcc Hcc'. unfold eval_edge in *. destruct (eff c0); conv_bool;[|congruence].
    rewrite <-Hcc, <-Hcc'. reflexivity.
  Qed.

  Lemma necons_nlcons_inv {A : Type} (a a' : A) l l' :
    (a :<: l) = a' :< l' -> a = a' /\ ne_to_list l = l'.
  Proof.
    intro H. split.
    all:destruct l'; cbn in *; [congruence|].
    1:revert a a' a0 l' H; induction l; intros b b' b0 l' H; cbn in *.
    1,2: inversion H; split;eauto.
    revert a a' a0 l' H; induction l; intros b b' b0 l' H; cbn in *.
    - destruct l'; cbn in *;congruence.
    - f_equal.
      + inversion H. destruct l';inversion H2. reflexivity.
      + destruct l'; cbn in *; inversion H; subst. eapply IHl.
        reflexivity. Unshelve. eauto.
  Qed.

  Lemma tr_succ_eq (l : list Conf) (k k' : Conf) :
    ne_back (k :< l) = ne_back (k' :< l) -> Tr (k :< l) -> Tr (k' :< l) -> k = k'.
  Proof.
    intros Hback Htr Htr'.
    inversion Htr; inversion Htr'; subst.
    1,2: destruct l;cbn in H0,H1;[|congruence].
    3: destruct l;cbn in H3;[|congruence].
    all: cbn in Hback;eauto.
    eapply necons_nlcons_inv in H2 as [H21 H22];eapply necons_nlcons_inv in H as [H01 H02].
    subst k0 k1. destruct l;[exfalso;eapply ne_to_list_not_nil;eauto|].
    rewrite nlcons_to_list in H22. rewrite nlcons_to_list in H02.
    apply ne_to_list_inj in H22. apply ne_to_list_inj in H02. rewrite H22 in H4. rewrite H02 in H1.
    simpl_nl' H1. simpl_nl' H4.
    eapply eval_det; unfold eval_edge; [rewrite H1|rewrite H4]; conv_bool; reflexivity.
  Qed.
  
  Lemma prefix_eff_cons_cons k k' l l' :
    (*    eff (ne_front l) = Some k
    -> l' = ne_to_list l''
    -> Tr (k' :<: l'')
    -> Prefix l l'
    -> Prefix (k :: l) (k' :: l').
     *)
    l <> nil
    -> Tr (k :< l)
    -> Tr (k' :< l')
    -> Prefix l l'
    -> Prefix (k :: l) (k' :: l').
  Proof.
    intros Hemp Htr Htr' Hpre.
    revert dependent k'.
    induction Hpre; intros k' Htr'.
    - enough (k = k').
      + subst k'. econstructor.
      + eapply tr_succ_eq; eauto. destruct l; cbn; eauto; contradiction.
    - econstructor. eapply IHHpre; eauto. inversion Htr'; eauto.
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
      destruct t as [t tr]. unfold "`" in *. cbn. subst t2.
      simpl_nl.
      eapply prefix_eff_cons_cons; eauto;[congruence| |simpl_nl;eauto].
      cbn. econstructor.
      + eapply prefix_trace.
        * simpl_nl;eauto.
        * inversion Htr; eauto.
      + simpl_nl; eauto.
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

  (* not used:
  Lemma postfix_rcons_trace_eff l k k' l' :
    Tr l'
    -> Postfix ((l :r: k) :r: k') l'
    -> eff k' = Some k.
   *)
  
  Lemma Tr_CPath l :
    Tr l -> CPath root (fst (fst (ne_front l))) (ne_map fst (ne_map fst l)).
  Proof.
    intro H. eapply Tr_EPath in H;[| repeat rewrite <-surjective_pairing; reflexivity].
    destruct H as [s0 H]. cbn. 
    eapply EPath_TPath in H. cbn in H. eapply TPath_CPath in H. eauto.
  Qed.

  Definition Tr' (l : ne_list Conf) :=
    exists l', Tr l' /\ Postfix l l'.
  

  Definition EPath' π := EPath (ne_back π) (ne_front π) π.

  Lemma epath_epath' r i0 s0 p i s t
        (Hpath : EPath (r,i0,s0) (p,i,s) t)
    : EPath' t.
  Proof.
    unfold EPath'. eapply path_back in Hpath as Hback.
    eapply path_front in Hpath as Hfront.
    rewrite Hfront,Hback. assumption.
  Qed.

  
  Lemma ne_back_trace t :
    Tr t -> exists s, ne_back t = (root,start_tag,s).
  Proof.
    intro Htr.
    induction Htr; firstorder. exists s. cbn; reflexivity.
  Qed.

  Lemma tr_lc_lt' p i s1 s2 l1 l2
        (Htr1 : Tr ((p, i, s1) :<: l1))
        (Htr2 : Tr ((p, i, s2) :<: l2))
    : exists brk,
      last_common (ne_map fst l1) (ne_map fst l2) (brk).
  Proof.
    eapply ne_last_common. repeat rewrite ne_back_map.
    eapply ne_back_trace in Htr1 as [s1' Htr1]. cbn in Htr1.
    eapply ne_back_trace in Htr2 as [s2' Htr2]. cbn in Htr2.
    setoid_rewrite Htr1. setoid_rewrite Htr2. cbn;eauto.
  Qed.

  Lemma tr_lc_lt p i s1 s2 q1 q2 j1 j2 r1 r2 l1 l2
        (Htr1 : Tr ((p, i, s1) :<: (q1, j1, r1) :< l1))
        (Htr2 : Tr ((p, i, s2) :<: (q2, j2, r2) :< l2))
    : exists br k,
      last_common ((q1, j1) :: map fst l1) ((q2, j2) :: map fst l2) (br,k).
  Proof.
    enough (exists brk,
               last_common (ne_map fst ((q1, j1, r1) :< l1)) (ne_map fst ((q2, j2, r2) :< l2)) brk).
    { (simpl_nl' H;cbn in H;destruct H as [[br k] H];eauto). }
    eapply tr_lc_lt';eauto.
  Qed.

  Lemma tr_tpath_cons2 p i s q j r l
        (Htr : Tr ((p,i,s) :<: (q,j,r) :< l))
    : TPath' ((p, i) :<: (q, j) :< map fst l).
  Proof.
    eapply Tr_EPath in Htr as Htr; cbn;eauto. destruct Htr as [s01 Htr].
    eapply EPath_TPath in Htr.
    cbn in *. unfold TPath'. simpl_nl' Htr. cbn in *.
    eapply path_back in Htr as Hback. cbn in Hback. unfold Coord in *. rewrite Hback;eauto.
  Qed.
  
  Lemma tr_lift_succ l q q' j j'
        (Hpath : Tr l)
        (Hsucc : map fst l ⊢ (q',j') ≻ (q,j))
    : exists r r', l ⊢ (q',j',r') ≻ (q,j,r).
  Proof.
    unfold succ_in in *. destructH.
  Admitted.
  
  Lemma tr_succ_eff' p q q' br i j k s r r' r0 l
        (Htr : Tr ((p, i, s) :< l))
        (Hsucc : (p, i, s) :< l ⊢ (q, j, r) ≻ (br, k, r0))
        (Heff : eff' (br,r0) = Some (q',r'))
    : q = q'.
  Admitted.

  
  Lemma succ_in_rcons2 {A : Type} (a b : A) l
    : l :r: a :r: b ⊢ a ≻ b.
  Proof.
    exists nil, l. unfold rcons. rewrite <-app_assoc. rewrite <-app_comm_cons. cbn. reflexivity.
  Qed.
  
  Lemma succ_in_tpath_eff_tag p q i j t
        (Hpath : TPath' t)
        (Hsucc : t ⊢ (p,i) ≻ (q,j))
    : eff_tag q p j = i.
  Proof.
  Admitted.

  Lemma eff_tcfg p q i j s r
        (Heff : eff (p,i,s) = Some (q,j,r))
    : tcfg_edge (p,i) (q,j) = true.
  Proof.
    eapply eff_eff_tag in Heff as Heff'. unfold tcfg_edge, tcfg_edge'.
    eapply step_conf_implies_edge in Heff. conv_bool; firstorder.
  Qed.

  Lemma tr_tpath_cons1 (l : list Conf) c
        (Htr : Tr (c :< l))
    : TPath' ((fst c) :< map fst l).
  Proof.
    revert dependent c.
    induction l; intros c Htr; inversion Htr; cbn; [econstructor|]. unfold TPath'. cbn.
    econstructor. eapply IHl;eauto.

    simpl_nl' H2. destruct a as [[p i] s]. destruct c as [[q j] r]. cbn. simpl_nl.
    eapply eff_tcfg;eauto.
  Qed.
  
  Lemma prec_lab_prec_fst p i s l
        (Hprec : Precedes lab_of l (p,i,s))
    : Precedes fst (map fst l) (p,i).
  Proof.
    induction l; inversion Hprec;subst;cbn in *.
    - econstructor.
    - econstructor;eauto.
      destruct a as [[a1 a2] a]; cbn in *;eauto.
  Qed.

End eval.


(** spot_path **)

Ltac spot_path_e :=
  let H := fresh "H" in
  let Q := fresh "Q" in
  let p := fresh "p" in
  let i := fresh "i" in
  let s := fresh "s" in
  lazymatch goal with 
  | [ H : Tr ?t |- _ ] => destruct (ne_front t) as [[p i] s] eqn:Q;
                        eapply Tr_EPath in H;[clear Q|apply Q]; destructH' H; cbn_nl' H
  end.

Ltac spot_path_t :=
  try spot_path_e;
  lazymatch goal with
  | [ H : EPath _ _ _ |- _ ] => eapply EPath_TPath in H; cbn_nl' H
  end.

Ltac spot_path_c :=
  try spot_path_t;
  lazymatch goal with
    [ H : TPath _ _ _ |- _ ] => eapply TPath_CPath in H; cbn_nl' H
  end.

Ltac spot_path :=
  lazymatch goal with
  | [ H : CPath' _ |- _ ] => unfold CPath' in H;spot_path
  | [ H : TPath' _ |- _ ] => unfold TPath' in H;spot_path
  | [ H : EPath' _ |- _ ] => unfold EPath' in H;spot_path
  | [ |- CPath' _ ] => repeat spot_path_c; eapply cpath_cpath';eauto
  | [ |- TPath' _ ] => repeat spot_path_t; eapply tpath_tpath';eauto
  | [ |- EPath' _ ] => repeat spot_path_e; eapply epath_epath';eauto
  | [ |- CPath _ _ _ ] => repeat (spot_path_c;eauto)
  | [ |- TPath _ _ _ ] => repeat (spot_path_t;eauto)
  | [ |- EPath _ _ _ ] => repeat (spot_path_e;eauto)
  end.

Section test.
  Variable X : Type.
  Variable A B C : Prop.
  Variable P : X -> Prop.
  
  Local Parameter test1 : A -> (exists x, P x).

  Local Parameter test2 : forall y, P y -> B.

  Ltac xapply H Q :=
    lazymatch type of H with
    | (forall y, ?P y -> ?B) =>
      lazymatch type of Q with
      | (?A -> (exists x, _)) =>
        lazymatch goal with
          [ R: A |- B] => eapply Q in R as R';
                        destructH' R';
                        eapply H;
                        eapply R'
        end
      end
    end.
  
  Lemma test3 : A -> B.
    intro a. xapply test2 test1.
  Qed.

  Parameter x y : X.
  Parameter Heq : x = y.
  Parameter H1 : P x.

  Ltac rapply' H Q :=
    lazymatch Q with
    | _ -> ?Q' => rapply' H Q'
    | _ =>
      lazymatch goal with
      | [ |- ?P ?y1 ?y2 ?y3 ?y4] =>
        lazymatch Q with
        | P ?x1 ?x2 ?x3 ?x4 => replace (P y1 y2 y3 y4) with (P x1 x2 x3 x4);[eapply H|f_equal]
        end
      | [ |- ?P ?y1 ?y2 ?y3] =>
        lazymatch Q with
        | P ?x1 ?x2 ?x3=> replace (P y1 y2 y3) with (P x1 x2 x3);[eapply H|f_equal]
        end
      | [ |- ?P ?y1 ?y2 ?y3] =>
        lazymatch Q with
        | P ?x1 ?x2 ?x3 => replace (P y1 y2 y3) with (P x1 x2 x3);[eapply H|f_equal]
        end
      | [ |- ?P ?y1 ?y2] =>
        lazymatch Q with
        | P ?x1 ?x2 => replace (P y1 y2) with (P x1 x2);[eapply H|f_equal]
        end
      | [ |- ?P ?y] => 
        lazymatch Q with
        | P ?x => replace y with x;[eapply H|]
        end
      end
    end.

  Print Ltac rapply'.
  
  Ltac rapply H := lazymatch type of H with ?Q => rapply' H Q end.
  
  Lemma test4 : P y.
    rapply H1. eapply Heq.
  Qed.

  Parameter Q : X -> X -> Prop.
  Parameter HQ : Q x x.

  Lemma test5 : Q y x.
    rapply HQ. eapply Heq.
  Qed.

  Lemma test6 : forall R, R x y x y -> R x y y x.
    intros. rapply X0. 2: symmetry. 1,2: eapply Heq.
  Qed.

  Lemma test7 : (forall z:X, P x) -> P y.
    intros. rapply H. exact x. exact Heq.
  Qed.

  Lemma test8 : forall z, P z -> (P z -> P z -> P x) -> P y.
    intros. rapply H0;eauto. eapply Heq.
  Qed.

End test.

