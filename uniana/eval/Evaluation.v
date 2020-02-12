Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Utils.
Require Import Coq.Logic.Classical.
Require Import List.
Require Import Nat.
Require Import Bool.Bool.
Require Import Coq.Logic.Eqdep_dec.

Require Export Tagged LastCommon.

Section eval.

  Context `{C : redCFG}.

  Notation "p --> q" := (edge p q = true) (at level 55,right associativity).

  Parameter Var : Type.
  Parameter Var_dec : EqDec Var eq.
  Parameter is_def : Var -> Lab -> Lab -> bool.

  Parameter def_edge :
    forall p q x, is_def x p q = true -> p --> q.

  Definition is_def_lab x p := exists q, is_def x q p = true.

(*  Lemma Lab_var_dec :
    forall (x y : (Lab * Var)), { x = y } + { x <> y }.
  Proof.
    intros.
    destruct x as [xa xb], y as [ya yb].
    
    decide ((xa, xb) = (ya, yb)); firstorder.
  Qed.
  Program Instance lab_var_eq_eqdec : EqDec (Lab * Var) eq := Lab_var_dec.*)
  
  Parameter Val : Type.

  Definition State := Var -> Val.

  Parameter Val_dec : EqDec Val eq.
  Parameter Tag_dec : EqDec Tag eq.
  Parameter State_dec : EqDec State eq.

  Global Existing Instance Val_dec.
  Global Existing Instance Tag_dec.
  Global Existing Instance State_dec.
  

  Definition States := State -> Prop.
  Definition Conf := ((@Coord Lab)* State)%type.

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
                     | Some (q, r) => match eff_tag p q i with
                                     | Some j => Some (q, j, r)
                                     | None => None
                                     end
                     end
       end.
  
  Ltac eff_unf :=
    lazymatch goal with
    | H : context [eff (?q,?j,?r)] |- _
      => unfold eff, eff_tag in H;
        destruct (eff' (q,r));
        [match type of H with
         | context[let (_,_) := ?x in _ ]
           => let x1 := fresh "x" in
             let x2 := fresh "x" in 
             destruct x as [x1 x2];
             decide (edge__P q x1);[|try congruence; try contradiction](*
              unfold eff_tag' in H;
              match goal with
              | Q : edge__P q x1 |- _
                => destruct (edge_Edge Q);
                  inversion H;subst
              end*)
         end
        |try congruence; try contradiction]
    | H : context [eff ?x] |- _
      => destruct x as [[? ?] ?]; eff_unf
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
    -> eff_tag q p j = Some i.
  Proof.
    intros Heff.
    eff_unf. unfold eff_tag. inversion Heff. subst.
    decide (edge__P q p);[|congruence]. f_equal. eapply eff_tag'_eq. 
  Qed.

  Definition eval_edge := (fun k k' : Conf
                           => match eff k with
                             | Some k => k = k'
                             | None => False
                             end).
  
  Parameter def_spec :
    forall p q x, (exists i j s r, eff (p, i, s) = Some (q, j, r) /\ r x <> s x) ->
             is_def x p q = true.

  Definition option_chain (A B : Type) (f : A -> option B) (a : option A) : option B
    := match a with
       | Some a' => f a'
       | _ => None
       end.

  Definition sem_step l k := option_chain eff (hd_error l) = Some k.

  Inductive Tr : list Conf -> Prop :=
  | Init : forall s, Tr [(root, start_tag, s)]
  | Step : forall l (k : Conf), Tr l -> sem_step l k -> Tr (k :: l).

  Definition EPath := Path eval_edge.

  Hint Unfold Conf Coord.
  
  Lemma EPath_Tr s0 p i s π :
    EPath (root,start_tag,s0) (p,i,s) π -> Tr π.
  Proof.
    intro H. remember (root, start_tag, s0) as start_c.
    remember (p,i,s) as pis_c. revert p i s Heqpis_c.
    induction H; intros p i s Heqpis_c; [rewrite Heqstart_c|];econstructor;destruct b as [[b1 b2] b3].
    - eapply IHPath; eauto.
    - subst c. destruct π;[inversion H|].
      unfold sem_step;cbn.
      path_simpl' H.
      unfold eval_edge in H0. clear - H0.
      unfold Coord in *.
      destruct (eff (b1,b2,b3)).
      + subst. reflexivity.
      + contradiction.
  Qed.
  
  Lemma Tr_EPath p i s π :
    Tr π ->  hd_error π = Some (p,i,s) -> exists s0, EPath (root,start_tag,s0) (p,i,s) π.
  Proof.
    intros HTr Hfront.
    revert p i s Hfront. dependent induction HTr; cbn; intros p i s' Hfront.
    - inversion Hfront. subst p i s'. eexists;econstructor.
    - inversion Hfront. subst k.
      remember (hd_error l) as c.
      destruct c.
      + destruct c as [[q j] r].
        specialize (IHHTr q j r). exploit IHHTr.
        destructH. eexists;econstructor;eauto.
        unfold eval_edge.
        unfold sem_step in H.
        destruct l;cbn in H;[congruence|]. unfold EPath in IHHTr. path_simpl' IHHTr.
        destruct (eff (q,j,r)).
        * inversion H;eauto.
        * congruence.
      + unfold sem_step in H. destruct l;cbn in *;congruence.
  Qed.
  
  Lemma eval_edge_tcfg_edge p q i j s r
        (Heval : eval_edge (q,j,r) (p,i,s))
    : tcfg_edge (q,j) (p,i).
  Proof.
    unfold eval_edge in Heval.
    split.
    - destruct (eff (q,j,r)) eqn:E;[|contradiction].
      eapply step_conf_implies_edge. subst c;eauto.
    - eff_unf. unfold eff_tag' in Heval. unfold eff_tag. inversion Heval; subst. decide (edge__P q p).
      2: congruence.
      erewrite eff_tag'_eq. reflexivity.
  Qed.

  Lemma EPath_TPath k k' π :
    EPath k k' π -> TPath (fst k) (fst k') (map fst π).
  Proof.
    intros H. dependent induction H; [|destruct c]; econstructor.
    - apply IHPath.
    - cbn. destruct b. cbn. destruct c0, c. eapply eval_edge_tcfg_edge;eauto.
  Qed.

  Lemma EPath_TPath' k k' c c' π ϕ :
    EPath k k' π -> c = fst k -> c' = fst k' -> ϕ = map fst π -> TPath c c' ϕ.
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


  Definition trace := {l : list Conf | Tr l}.


  Open Scope prg.

  Definition Traces := trace -> Prop.
  Definition Hyper := Traces -> Prop.

  (* This is the concrete transformer for sets of traces *)
  Definition sem_trace (ts : Traces) : Traces :=
    fun tr' => exists tr k', ts tr /\ `tr' = (k' :: `tr).

  (* This is the hypertrace transformer.
     Essentially, it lifts the trace set transformers to set of trace sets *)
  Definition sem_hyper (T : Hyper) : Hyper :=
    fun ts' => exists ts, T ts /\ ts' = sem_trace ts.

  (* possibly unused
  Lemma in_succ_in k p q t :
    Tr (k :: t) -> In p t -> eff p = Some q -> In q (k :: t).
  Proof.
    intros. 
    revert dependent k. 
    dependent induction t; intros k H; inv_tr H; [firstorder|].
    + rewrite nlcons_front in H5. destruct H0;[subst a|].
      * rewrite H5 in H1. inversion H1. left. reflexivity.
      * right. eapply IHt;eauto.
  Qed.
   *)

  Lemma Tr_eff_Some c k t
        (Htr : Tr (c :: k :: t))
    : eff k = Some c.
  Proof.
    inversion Htr.
    unfold sem_step in H2. cbn in H2. eauto.
  Qed.
  
  Lemma in_pred_exists p i s k t :
    (p,i,s) ∈ (k :: t) ->
    p <> root ->
    Tr (k :: t) ->
    exists q j r, (q, j, r) ∈ t /\ eff (q, j, r) = Some (p, i, s).
  Proof.
    revert k.
    dependent induction t; intros k Hin Hneq Htr; inversion Htr.
    - exfalso.
      destruct Hin;[|contradiction].
      subst k. inversion H0. eapply Hneq. rewrite H1. reflexivity.
    - inversion H1. 
    - subst.
      destruct Hin.
      + subst k.
        destruct a as [[q j] r].
        exists q, j, r. split;[left;auto|].
        eapply Tr_eff_Some;eauto.
      + specialize (IHt a).
        exploit IHt.
        destructH. do 3 eexists;eauto.
  Qed.
  
  Lemma ivec_fresh : forall p i s (t : trace),
      sem_step (`t) (p, i, s) -> forall j r, In (p, j, r) (`t) -> j <> i.
  Proof.
    intros.
    destruct t; cbn in *.
    remember (hd_error x) as c. destruct c.
    - destruct c,c. eapply eff_tag_fresh;cycle 2.
      + eapply in_map with (f:=fst) in H0. eauto.
      + eapply Tr_EPath in t;eauto. destruct t as [s1 t].
        eapply EPath_TPath in t; eauto.
      + destruct x;cbn in Heqc;[congruence|].
        inversion Heqc. subst c.
        unfold sem_step in H. cbn in H.
        destruct (eff' (e,s0)).
        * destruct p0. unfold eff_tag in *. decide (edge__P e e0). 2:congruence.
          inversion H. subst. decide (edge__P e p);[|congruence]. erewrite eff_tag'_eq. reflexivity.
        * congruence.
    - destruct x.
      + inversion t.
      + cbn in Heqc. congruence.
  Qed.
  
  Lemma ivec_det : forall q j r r' p i i' s s',
      eff (q, j, r) = Some (p, i, s) ->
      eff (q, j, r') = Some (p, i', s') ->
      i = i'.
  Proof.
    intros. eff_unf. eff_unf. inversion H;subst. inversion H0;subst. eapply eff_tag'_eq.
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
    eapply root_no_pred. eassumption.
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
    forall k t p s, Precedes' (k :: t) p s ->
               Tr (k :: t) ->
               lab_of p <> lab_of s ->
               In p t.
  Proof.
    intros.
    destruct H as [l [Hpre Hprec]].
    inv_tr Hprec.
    - firstorder.
    - eapply precedes_in in H5.
      eapply prefix_cons_cons in Hpre.      
      eapply in_prefix_in; eauto.
  Qed.

  Lemma in_exists_pred p i s k (t : trace) :
    In (p, i, s) (k :: `t) ->
    sem_step (`t) k ->
    p <> root ->
    exists q j r, In (q, j, r) (`t) /\ eff (q, j, r) = Some (p, i, s).
  Proof.
    intros H Heff Hneq.
    destruct t as [l tr]; cbn in H, Heff. unfold "`".
    destruct H; [subst k| revert dependent k];
      dependent induction l; inversion tr; subst; intros. 
    - exists root, start_tag, s0. split; [ constructor | eauto ]; eauto.
    - cbn in Heff, H2. destruct a as [[q j] r]. exists q,j,r. firstorder. 
    - exfalso. inversion H; inversion H0. subst p; contradiction.
    - destruct H.
      + subst a. remember (hd_error l) as qjr. destruct qjr as [qjr|qjr].
        2: destruct l; unfold sem_step in H3;cbn in *;congruence.
        destruct qjr as [[q j] r].
        exists q,j,r. split; [econstructor 2 | eauto].
        * destruct l;[inversion H2|]. cbn in Heqqjr. inversion Heqqjr.
          setoid_rewrite H0. left. auto.
        * unfold sem_step in H3.
          destruct l;[inversion H2|].
          cbn in H3. cbn in Heqqjr. inversion Heqqjr. subst c. eauto.
      + eapply IHl in H2; eauto. destruct H2 as [q [j [r [Hin Hstep]]]].
        exists q, j, r. split; eauto. 
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
      + exfalso. destruct l;[inversion H1|]. destruct c as [[q j] r].
        eapply root_no_pred. subst a.
        apply edge_spec. unfold is_effect_on. exists j,i,r,s.
        eapply Tr_eff_Some;eauto.
      + eapply IHl; eauto.
  Qed.

  Lemma trace_destr_in_in k k' (t : trace) :
    In k (`t) -> In k' (`t)
    -> exists (t': trace), hd_error (`t') = Some k' /\ In k (`t') \/ hd_error (`t') = Some k /\ In k' (`t').
  Proof.
    intros Hin Hin'.
    destruct t as [t tr]. cbn in *.
    induction t; inversion tr; cbn in *.
    - subst t. destruct Hin; [|contradiction]; destruct Hin'; [|contradiction].
      subst a k.
      exists (exist _ [k'] tr). cbn. tauto.
    - destruct Hin, Hin'; [| | |eapply IHt; eauto]; subst.
      + exists (exist _ (k' :: t) tr ). cbn. tauto.
      + exists (exist _ (k :: t) tr). cbn. tauto.
      + exists (exist _ (k' :: t) tr). cbn. tauto.
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
      + cbn in Hin,Hf. subst t'. destruct Hin; [|contradiction]. subst a. inversion Hf. reflexivity.
      + subst. cbn in *. destruct a as [[q j] r']. inversion Hf. subst.
        destruct Hin;  [inversion H; reflexivity|].
        trace_proj t'.
        eapply ivec_fresh in H2; eauto. contradiction.
    - induction t'; inversion tr'.
      + cbn in Hin,Hf. subst t'. destruct Hin; [|contradiction]. subst a. inversion Hf. reflexivity.
      + cbn in *. subst. destruct a as [[q j] r']. inversion Hf. subst.
        destruct Hin; [inversion H; reflexivity|].
        trace_proj t'. eapply ivec_fresh in H2; eauto. contradiction.
  Qed.

  Lemma prefix_trace (l l' : list Conf) c :
    Prefix (c :: l) l' -> Tr l' -> Tr (c :: l).
  Proof.
    intros Hpr Htr. induction Htr;cbn in *.
    - inversion Hpr;[econstructor|]. inversion H1.
    - inversion Hpr.
      + subst. econstructor;eauto.
      + eapply IHHtr;eauto.
  Qed.

  Lemma eval_det c0 c c' : eval_edge c0 c -> eval_edge c0 c' -> c = c'.
  Proof.
    intros Hcc Hcc'. unfold eval_edge in *. destruct (eff c0); subst;auto. contradiction.
  Qed.

(*  Lemma tr_succ_eq (l : list Conf) (k k' : Conf) :
    ne_back (k :: l) = ne_back (k' :: l) -> Tr (k :: l) -> Tr (k' :: l) -> k = k'.
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
  Qed.*)
  
  Lemma prefix_eff_cons_cons k k' l l' :
    (*    eff (ne_front l) = Some k
    -> l' = ne_to_list l''
    -> Tr (k' :<: l'')
    -> Prefix l l'
    -> Prefix (k :: l) (k' :: l').
     *)
    l <> nil
    -> Tr (k :: l)
    -> Tr (k' :: l')
    -> Prefix l l'
    -> Prefix (k :: l) (k' :: l').
  Proof.
    intros Hemp Htr Htr' Hpre.
    revert dependent k'.
    induction Hpre; intros k' Htr'.
    - enough (k = k').
      + subst k'. econstructor.
      + destruct k as [[q j] r]. destruct k' as [[q' j'] r'].
        eapply Tr_EPath in Htr. 2: cbn;reflexivity.
        eapply Tr_EPath in Htr'. 2: cbn;reflexivity.
        do 2 destructH.
        inversion Htr. 1: symmetry in H4;contradiction.
        inversion Htr'. 1: symmetry in H9;contradiction.
        subst. destruct l. 1: inversion H0.
        path_simpl' H0. path_simpl' H5.
        eapply eval_det;eauto.
    - econstructor. eapply IHHpre; eauto. inversion Htr'; eauto.
  Qed.
  
  Lemma precedes_succ (t : trace) q j r q' j' r' p i s k' :
    Precedes' (`t) (q', j', r') (q, j, r) ->
    eff (q, j, r) = Some (p, i, s) ->
    p <> q' ->
    Tr (k' :: (`t)) ->
    Precedes' (k' :: (`t)) (q', j', r') (p, i, s).
  Proof.
    intros Hprec Heff Hneq Htr.
    destruct Hprec as [t' [Hpre Hprec]].
    exists ((q,j,r) :: t').
    split.
    - clear Hprec Hneq. 
      unfold Conf in Hpre. unfold Coord in Hpre.
      set (t2 := (q,j,r) :: t') in *.
      destruct t as [t tr]. unfold "`" in *. cbn. subst t2.
      eapply prefix_eff_cons_cons; eauto;[congruence| eauto].
      cbn. econstructor.
      + eapply prefix_trace.
        * eauto.
        * inversion Htr; eauto. subst t. inversion Hpre. 
      + eauto. 
    - econstructor; cbn; eauto. 
  Qed.
       
  (* possibly unused
  Lemma precedes_step l q j r p i s :
    forall k, (q, j, r) ∈ l ->
         p <> q ->
         eff (q, j, r) = Some (p, i, s) ->
         Tr (k :: l) -> 
         Precedes' (k :: l) (q, j, r) (p, i, s).
  Proof.
    intros k Hin Hneq Heff Htr.
    assert ((p,i,s) ∈ (k :: l)) as Hin'.
    {
      revert dependent k.
      induction l; intros k Htr; cbn in Htr; inversion Htr; inversion Hin; cbn; subst.
      - left. rewrite H2 in Heff. inversion Heff. reflexivity.
      - right. cbn in IHl. eauto.
    }
    exists (prefix_nincl (p,i,s) (k :: l)). split.
    - eapply prefix_nincl_prefix; eauto.
    - revert dependent k. induction l; intros k Htr Hin'; inversion Hin; inversion Hin'; subst.
      + cbn. destruct ((p,i,s) == (p,i,s)); [destruct e|exfalso; eapply c; reflexivity].
        econstructor; [cbn; eauto|]. destruct l; cbn; econstructor.
      + exfalso.
        inversion Htr; subst.
        assert (k = (p,i,s)) as Hk.
        { eapply Tr_eff_Some in Htr. rewrite Htr in Heff. inversion Heff. auto. }
        subst k.
        eapply ivec_fresh.
        * instantiate (4:=exist _ _ H2). unfold "`". eapply H3.
        * cbn. eauto.
        * reflexivity.
      + exfalso.
        inversion Htr; subst.
        destruct a as [[q' j'] r'].
        eapply ivec_fresh.
        * instantiate (4:=exist _ _ H2). unfold "`". eauto.
        * cbn. give_up.
        * reflexivity.
      + cbn. destruct ((p,i,s) == k).
        * destruct e. exfalso.
          inversion Htr; subst.
          eapply ivec_fresh.
          -- instantiate (4:=exist _ _ Htr). unfold "`". eauto. give_up.
          -- cbn. eauto.
          -- reflexivity.
        * eapply IHl; eauto. cbn in Htr. inversion Htr; subst; eauto.
  Qed.
  *)

  Lemma no_def_untouched :
    forall p q x, is_def x q p = false -> forall i j s r, eff (q, j, r) = Some (p, i, s) -> r x = s x.
  Proof.
    intros.
    specialize (@def_spec q p x).
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
    Tr l -> CPath root (fst (fst (hd (root,start_tag,zero) l))) (map fst (map fst l)).
  Proof.
    intro H. destruct l;[inversion H|].
    eapply Tr_EPath in H;[| repeat rewrite <-surjective_pairing; reflexivity].
    destruct H as [s0 H]. cbn. 
    eapply EPath_TPath in H. cbn in H. eapply TPath_CPath in H. eauto.
  Qed.

  Definition Tr' (l : list Conf) :=
    exists l', Tr l' /\ Postfix l l'.

  Lemma tr_lc_lt p i s1 s2 l1 l2 q1 q2 j1 j2 r1 r2
        (Htr1 : Tr ((p, i, s1) :: (q1,j1,r1) :: l1))
        (Htr2 : Tr ((p, i, s2) :: (q2,j2,r2) :: l2))
    : exists brk,
      last_common ((q1,j1) :: map fst l1) ((q2,j2) :: map fst l2) (brk).
  Proof.
    inversion Htr1. subst k l.
    inversion Htr2. subst k l.
    eapply Tr_EPath in H1. 2:cbn;eauto.
    eapply Tr_EPath in H3. 2:cbn;eauto.
    do 2 destructH.
    setoid_rewrite cons_rcons' in H1.
    setoid_rewrite cons_rcons' in H3.
    pose (l1' := (rev (tl (rev ((q1, j1, r1) :: l1))))).
    pose (l2' := (rev (tl (rev ((q2, j2, r2) :: l2))))).
    eapply path_back in H1 as Hback1. rewrite <-Hback1 in *.
    eapply path_back in H3 as Hback2. rewrite <-Hback2 in *.
    specialize (ne_last_common (map fst l1') (map fst l2') (root,start_tag)) as Hlc.
    destructH.
    exists s.
    enough ((q2,j2) :: map fst l2 = map fst l2' :r: (root,start_tag)).
    enough ((q1,j1) :: map fst l1 = map fst l1' :r: (root,start_tag)).
    * rewrite H. rewrite H0. eauto.
    * clear - Hback1. subst l1'.
      fold (fst (root,start_tag,s3)). 
      rewrite <-map_rcons.
      rewrite Hback1.
      rewrite <-cons_rcons'. cbn. eauto.
    * clear - Hback2. subst l2'.
      fold (fst (root,start_tag,s0)).
      rewrite <-map_rcons.
      rewrite Hback2.
      rewrite <-cons_rcons'. cbn. eauto.
  Qed.

  Lemma tr_tpath_cons2 p i s q j r l
        (Htr : Tr ((p,i,s) :: (q,j,r) :: l))
    : TPath (root,start_tag) (p,i) ((p, i) :: (q, j) :: map fst l).
  Proof.
    eapply Tr_EPath in Htr as Htr; cbn;eauto. destruct Htr as [s01 Htr].
    eapply EPath_TPath in Htr.
    cbn in *. auto.
  Qed.

  Lemma Tr_NoDup l
        (Htr : Tr l)
    : NoDup (map fst l).
  Proof.
    destruct l;[inversion Htr|].
    destruct c as [[q j] r]. cbn.
    eapply Tr_EPath in Htr;[|cbn;reflexivity].
    destructH.
    eapply EPath_TPath in Htr. cbn in Htr.
    eapply tpath_NoDup;eauto.
  Qed.

  Lemma tr_lift_succ l q q' j j'
        (Hpath : Tr l)
        (Hsucc : (q',j') ≻ (q,j) | map fst l)
    : exists r r', (q',j',r') ≻ (q,j,r) | l.
  Proof.
    unfold succ_in in Hsucc. destructH.
    revert dependent l1. revert dependent l.
    induction l2;intros;cbn in Hsucc.
    - revert dependent l1. revert q q' j j'. induction l;intros.
      + cbn in *. congruence.
      + cbn in *. inversion Hpath;subst.
        1:cbn in Hsucc; congruence. 
        exploit' IHl. destruct l1.
        * destruct a. inversion H1;subst;cbn in Hsucc; inversion Hsucc;[subst q j|].
          -- cbn in *. 
             exists s0, s, nil, nil. cbn. reflexivity.
          -- exfalso. destruct l0; cbn in H6;[inversion H|congruence].
        * destruct a. cbn in *. destruct c.
          specialize (IHl e q t j l1). inversion Hsucc;subst. exploit IHl. destructH.
          exists r', s, ((e,t,r) :: (tl (tl l))), nil. cbn.
          unfold succ_in in IHl. destructH.
          destruct l2;cycle 1.
          { 
            exfalso.
            eapply Tr_NoDup in H1.
            enough (fst c = (q,j)).
            - rewrite IHl in H1. cbn in H1. rewrite H in H1.
              rewrite map_app in H1. clear - H1.
              inversion H1. eapply H2.
              eapply in_or_app. right. auto.
            - clear - IHl Hsucc.
              inversion Hsucc. rewrite IHl in H0. cbn in H0.
              inversion H0. reflexivity.
          } 
          assert (l1 = map fst l0).
          {
            cbn in IHl. clear - IHl H3.
            rewrite IHl in H3. cbn in H3. inversion H3. reflexivity.
          } 
          rewrite H in H3. cbn in IHl.
          f_equal.
          inversion H1.
          -- exfalso. cbn in *. congruence.
          -- cbn in Hsucc,H2,H3. destruct k. cbn in Hsucc,H3.
             rewrite <-H5 in IHl. 
             inversion H0.
             ++ cbn. destruct c. inversion IHl. subst. congruence.
             ++ cbn. destruct c. inversion IHl. subst. f_equal. f_equal. inversion H13. auto.
    - destruct l; cbn.
      + exfalso. destruct l2;cbn in Hsucc; inversion Hsucc.
      + cbn in Hsucc. inversion Hsucc.
        destruct l. 1: cbn in H1;congruence'.
        inversion Hpath;subst.
        eapply IHl2 in H1;eauto.
        destructH. do 2 eexists. eapply succ_cons. eauto.
  Qed.
  
  Lemma tr_succ_eff' p q q' br i j k s r r' r0 l
        (Htr : Tr ((p, i, s) :: l))
        (Hsucc : (q, j, r) ≻ (br, k, r0) | (p, i, s) :: l)
        (Heff : eff' (br,r0) = Some (q',r'))
    : q = q'.
  Proof.
    unfold succ_in in Hsucc. destructH.
    revert dependent l1. revert dependent l. revert p i s.
    induction l2;intros.
    - cbn in Hsucc.
      destruct l. 1: cbn in *; congruence.
      inversion Hsucc. subst.
      eapply Tr_eff_Some in Htr.
      eff_unf. inversion Heff;inversion Htr;subst. reflexivity.
    - cbn in Hsucc.
      destruct l. 1: cbn in *; destruct l2; cbn in Hsucc;congruence.
      destruct p0. destruct p0.
      eapply IHl2.
      + cbn in Htr. inversion Htr. eapply H1.
      + cbn in Hsucc. inversion Hsucc;subst. eauto.
  Qed.
  
  Lemma succ_in_rcons2 {A : Type} (a b : A) l
    : a ≻ b | l :r: a :r: b.
  Proof.
    exists nil, l. rewrite <-app_assoc. rewrite <-app_comm_cons. cbn. reflexivity.
  Qed.

  Lemma succ_in_cons_eq (A : Type) (a b c : A) l
        (Hsucc : a ≻ b | a :: c :: l)
        (Hnd : NoDup (a :: c :: l))
    : b = c.
  Proof.
    inversion Hnd. subst.
(*    destruct (b == c);[auto|].*)
    unfold succ_in in Hsucc. destructH.
    destruct l2.
    - cbn in *. inversion Hsucc. auto.
    - exfalso.
      eapply H1. cbn in Hsucc. inversion Hsucc;subst.
      clear - H3. destruct l2;intros;inversion H3;subst;cbn in *;eauto.
  Qed.
  
  Lemma succ_in_cons_neq (A : Type) (a b c d : A) l
        (Hsucc : a ≻ b | d :: c :: l)
        (Hnd : NoDup (c :: l))
        (Hneq : a <> d)
    : a ≻ b | c :: l.
  Proof.
    unfold succ_in in Hsucc. destructH.
    destruct l2.
    - cbn in Hsucc. inversion Hsucc. subst. contradiction.
    - cbn in Hsucc. inversion Hsucc. subst. eexists;eexists. eauto.
  Qed.
  
  Lemma succ_in_tpath_eff_tag p q i j t a b
        (Hpath : TPath a b t)
        (Hsucc : (p,i) ≻ (q,j) | t)
    : eff_tag q p j = Some i.
  Proof.
    unfold succ_in in Hsucc. destructH. 
    revert dependent t. revert b. induction l2; cbn in *; intros.
    - rewrite Hsucc in Hpath. unfold TPath in Hpath. destruct b.
      inversion Hpath. subst. destruct b. inversion H3;subst;destruct H5;eauto.
    - destruct t. 1: inversion Hpath.
      inversion Hsucc. subst. inversion Hpath;subst. 1: congruence'.
      eauto.
  Qed.
  
  Lemma eff_tcfg p q i j s r
        (Heff : eff (p,i,s) = Some (q,j,r))
    : tcfg_edge (p,i) (q,j).
  Proof.
    eapply eff_eff_tag in Heff as Heff'. unfold tcfg_edge.
    eapply step_conf_implies_edge in Heff. conv_bool; firstorder.
  Qed.

  (* possibly unused 
  Lemma tr_tpath_cons1 (l : list Conf) c
        (Htr : Tr (c :: l))
    : TPath (root,start_tag) (fst c) ((fst c) :: map fst l).
  Proof.
    revert dependent c.
    induction l; intros c Htr; inversion Htr; cbn; [econstructor|]. unfold TPath'. cbn.
    econstructor. eapply IHl;eauto.

    simpl_nl' H2. destruct a as [[p i] s]. destruct c as [[q j] r]. cbn. simpl_nl.
    eapply eff_tcfg;eauto.
  Qed.
   *)
  
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
  | [ H : Tr ((?p,?i,?s) :: ?t) |- _ ] => eapply Tr_EPath in H;[|cbn;reflexivity]; destructH' H; cbn in H
  | [ H : Tr ?t |- _ ] => destruct (hd_error t) as [[[p i] s]|N] eqn:Q;
                        [eapply Tr_EPath in H;[clear Q|apply Q]; destructH' H; cbn in H
                        |inversion H]
  end.

Ltac spot_path_t :=
  try spot_path_e;
  lazymatch goal with
  | [ H : EPath _ _ _ |- _ ] => eapply EPath_TPath in H; cbn in H
  end.

Ltac spot_path_c :=
  try spot_path_t;
  lazymatch goal with
    [ H : TPath _ _ _ |- _ ] => eapply TPath_CPath in H; cbn in H
  end.

Ltac spot_path :=
  lazymatch goal with
  | [ |- CPath _ _ _ ] => repeat (spot_path_c;eauto)
  | [ |- TPath _ _ _ ] => repeat (spot_path_t;eauto)
  | [ |- EPath _ _ _ ] => repeat (spot_path_e;eauto)
  end.

