Require Import Coq.Classes.EquivDec.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Program.Equality.
Require Import List.
Require Import Nat.
Require Import Omega.
Require Import Coq.Logic.Classical_Prop.

Module Uniana.
  Parameter Lab : Type.
  Parameter Var : Type.
  Parameter Val : Type.
  Parameter init_uni : Var -> Prop.

  Definition IVec := (list nat).
  Definition State := Var -> Val.
  Definition States := State -> Prop.
  Definition Coord := prod Lab IVec.
  Definition Conf := prod Coord State.

  Definition lab_of (k : Conf) :=
    match k with
      ((p, i), s) => p
    end.

  Definition UniState := Var -> bool.

  Parameter eff : Conf -> option Conf.
  Parameter abs_uni_eff : UniState -> UniState.

  Definition uni_state_concr (uni : UniState) : State -> State -> Prop :=
    fun s => fun s' => forall x, uni x = true -> s x = s' x.

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
  Parameter Var_dec : forall (x y : Var), {x = y} + {x <> y}.
  Parameter Conf_dec : forall (x y : Conf), {x = y} + {x <> y}.
  Program Instance lab_eq_eqdec : EqDec Lab eq := Lab_dec.
  Program Instance val_eq_eqdec : EqDec Val eq := Val_dec.
  Program Instance var_eq_eqdec : EqDec Var eq := Var_dec.
  Program Instance conf_eq_eqdec : EqDec Conf eq := Conf_dec.

  Lemma Lab_var_dec :
    forall (x y : (Lab * Var)), { x = y } + { x <> y }.
  Proof.
    intros.
    destruct x as [xa xb], y as [ya yb].
    destruct (xa == ya).
    - rewrite e.
      destruct (xb == yb).
      + rewrite e0.
        left. reflexivity.
      + right. intro. apply c. inversion H. reflexivity.
    - right. intro. apply c. inversion H. reflexivity.
  Qed.
  Program Instance lab_var_eq_eqdec : EqDec (Lab * Var) eq := Lab_var_dec.

  Definition start_ivec := @nil nat.

  Definition start_coord := (root, start_ivec) : Coord.

  Definition is_effect_on (p q : Lab) :=
    exists i i' s s', eff ((p, i), s) = Some ((q, i'), s').

  Parameter root_no_pred : forall p, has_edge p root = false.

  Parameter edge_spec :
    forall p q, is_effect_on p q -> has_edge p q = true.

  Notation "p --> q" := (has_edge p q = true) (at level 70, right associativity).

  Notation "p -->* q" := (p === q \/ p --> q) (at level 70, right associativity).

  Lemma step_conf_implies_edge :
    forall p q i j s r, eff (p, i, s) = Some (q, j, r) -> (p --> q).
  Proof.
    intros.
    eapply edge_spec.
    exists i; exists j; exists s; exists r.
    assumption.
  Qed.

  Parameter def_spec :
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
  Inductive Tr : Conf -> Type :=
    | Init : forall s, Tr (root, start_ivec, s)
    | Step : forall k k', Tr k' -> eff k' = Some k -> Tr k.

  Ltac inv_tr H := inversion H; subst; 
                   repeat match goal with
                          | [ H0: @existT Conf _ _ _ = @existT _ _ _ _  |- _ ] => apply inj_pair2_eq_dec in H0;
                                                                                  try (apply Conf_dec); subst
                          end.

  Lemma beq_true (A : Type) `{EqDec A} (a c : A) :
    (a ==b c) = true <-> (a === c).
  Proof.
    unfold equiv_decb; destruct (a == c); firstorder.
  Qed.

  Lemma beq_false (A : Type) `{EqDec A} (a b : A) :
    (a ==b b) = false <-> (a =/= b).
  Proof.
    unfold equiv_decb; destruct (a == b); firstorder.
  Qed.

  Ltac conv_bool H := repeat match goal with
                             | [ H: context[_ ==b _ = true] |- _ ] => rewrite beq_true in H
                             | [ H: context[_ ==b _ = false] |- _ ] => rewrite beq_false in H
                             | [ H: context[_ || _ = true] |- _ ] => rewrite orb_true_iff in H
                             | [ H: context[_ || _ = false] |- _ ] => rewrite orb_false_iff in H
                             | [ H: context[_ && _ = true] |- _ ] => rewrite andb_true_iff in H
                             | [ H: context[_ && _ = false] |- _ ] => rewrite andb_false_iff in H
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

  Definition Uni := Lab -> Var -> bool.
  Definition Hom := Lab -> bool.
  Definition Unch := Lab -> Var -> Lab.
  Definition Upi := Lab -> Lab -> bool.

  Inductive In : forall k, Tr k -> Conf -> Prop :=
    | In_At : forall k tr, In k tr k
    | In_Other : forall l k k' tr' step, In k' tr' l -> In k (Step k k' tr' step) l.

  Lemma tr_in_dec :
    forall k' k t, {In k t k'} + {~ In k t k'}.
  Proof.
    intros k'.
    induction t.
    - destruct (conf_eq_eqdec (root, start_ivec, s) k').
      + left. rewrite <- e. econstructor.
      + right. intro. apply c. inv_tr H. reflexivity.
    - destruct (conf_eq_eqdec k k').
      + left. rewrite <- e0. constructor.
      + inversion_clear IHt.
        * left. econstructor. eassumption.
        * right. intro. apply H. inv_tr H0; firstorder.
  Qed.

  Parameter ivec_fresh : forall p i s k t, eff k = Some (p, i, s) ->
                                           forall q j r, In k t (q, j, r) ->
                                                         j <> i.

  Parameter ivec_det : forall q j r r' p i i' s s',
      eff (q, j, r) = Some (p, i, s) ->
      eff (q, j, r') = Some (p, i', s') ->
      i = i'.

  Inductive Follows : forall k, Tr k -> Conf -> Conf -> Prop := 
  | Follows_At : forall k pred pred_tr step, Follows k (Step k pred pred_tr step) k pred
  | Follows_Other : forall succ pred k k' tr' step, Follows k' tr' succ pred ->
                                                    Follows k (Step k k' tr' step) succ pred.

  Inductive Precedes : forall k, Tr k -> Conf -> Conf -> Prop :=
  | Prec_in : forall k t , Precedes k t k k
  | Prec_cont : forall q q' p i j j' r' r s t step, Precedes (q', j', r') t (q, j, r) (q', j', r') -> 
                                                    (q === q' -> (j === j' /\ r === r')) ->
                                                    Precedes (p, i, s) (Step (p, i, s) (q', j', r') t step) (q, j, r) (p, i, s)
  | Prec_other : forall k' k t c c' step, Precedes k t c c' ->
                                          Precedes k' (Step k' k t step) c c'.
  Definition unique_preceding q p :=
      forall k k' t t' j j' i r r' s s',
      Precedes k t (q, j, r) (p, i, s) ->
      Precedes k' t' (q, j', r') (p, i, s') ->
      j' = j.

  Inductive Path : Lab -> Lab -> Type :=
    | PathInit : forall p, Path p p
    | PathStep : forall from p to, Path from p -> (p --> to) -> Path from to.

  Fixpoint PathIn (q : Lab) a b (p : Path a b) : Prop :=
    match p with
    | PathInit v => q === v
    | PathStep from mid to p edge => (q === to) \/ PathIn q from mid p
    end.

  Lemma step_exists_path {k k' : Conf} :
    eff k = Some k' -> Path (lab_of k) (lab_of k').
  Proof.
    intros. 
    econstructor. constructor. 
    destruct k as [[q j] r], k' as [[q' j'] r']; simpl in *.
    eauto using step_conf_implies_edge.
  Qed.
       
  Lemma trace_exists_path {p : Lab} {i : IVec} {s : State} {k : Conf} {tr : Tr k} :
    In k tr (p, i, s) -> Path p (lab_of k).
  Proof.
    intros Hin.
    induction tr; intros. simpl. enough (p = root). subst. constructor.
    inv_tr Hin. reflexivity.
    destruct k as [[q j] r], k' as [[q' j'] r']; simpl in *.
    destruct (p == q).
    + rewrite <- e0. clear e0. constructor.
    + econstructor. eapply IHtr. inv_tr Hin. firstorder. eassumption. 
    eauto using step_conf_implies_edge.
  Qed.

  Lemma not_in_trace_exists_path (q : Lab) (k k' : Conf) (t : Tr k) :
    In k t k' ->
    ~ (exists j r, In k t (q, j, r)) ->
    exists (p : Path (lab_of k') (lab_of k)), ~ PathIn q (lab_of k') (lab_of k) p.
  Proof.
    destruct k as [[p i] s].
    destruct k' as [[a l] u].
    simpl in *.
    intros Hin Hnin.
    dependent induction t.
    + inv_tr Hin. exists (PathInit root).
      intro. apply Hnin.
      destruct (q == root).
      - rewrite e in *. exists start_ivec, u. constructor.
      - inversion H. firstorder.
    + admit.
  Admitted.

  Lemma Path_in_dec :
    forall a x z p, {PathIn a x z p} + {~ PathIn a x z p}.
  Proof.
    intros a x z p.
    induction p.
    + destruct (a == p); firstorder.
    + simpl in *. destruct (a == to); firstorder.
  Qed.

  Parameter branch : Lab -> option (Lab * Lab * Var).

  Parameter val_true : Val -> bool.

  Parameter branch_spec : forall b,
      match branch b with
        | Some (t, f, x) => forall i s k, eff (b, i, s) = Some k -> lab_of k = (if val_true (s x) then t else f) /\ t =/= f
        | None => forall i i' s s' k k', eff (b, i, s) = Some k ->
                                         eff (b, i', s') = Some k' ->
                                         lab_of k = lab_of k'
      end.

  Definition DisjointPaths (s t f : Lab) (a : Path s t) (b : Path s f) :=
    forall p, PathIn p s t a -> PathIn p s f b -> p = s.

  Parameter exists_djp : Lab -> Lab -> bool.

  Parameter splits : Lab -> list (Lab * Var).

  Parameter splits_spec : forall conv br x, List.In (br, x) (splits conv) <->
                                            exists qt qf a b, qt -->* conv /\
                                                              qf -->* conv /\
                                                              DisjointPaths br qt qf a b.

  Definition uni_concr (u : Uni) : Hyper :=
    fun ts => forall t t' tr tr', ts t tr -> ts t' tr' ->
                                  forall x p i s s', In t tr ((p, i), s) ->
                                                     In t' tr' ((p, i), s') ->
                                                     u p x = true -> s x = s' x.

  Definition hom_concr (h : Hom) : Hyper :=
    fun ts => forall t t' tr tr', ts t tr -> ts t' tr' ->
                                  forall p, h p = true ->
                                            forall q q' j j'
                                                   i s s'
                                                   s1 s2, Follows t tr ((p, i), s1) ((q, j), s) ->
                                                          Follows t' tr' ((p, i), s2) ((q', j'), s')  ->
                                                          q = q' /\ j = j'.

  
  Definition unch_concr (unch : Unch) : Traces :=
    fun k => fun t => forall to i s x, (In k t (to, i, s) ->
                                       exists j r, Precedes k t (unch to x, j, r) (to, i, s) /\ r x = s x).


  Definition upi_prop q p k k' t t' :=
    forall j j' i r r' s s', Precedes k t (q, j, r) (p, i, s) ->
                             Precedes k' t' (q, j', r') (p, i, s') ->
                             j' = j.

  Definition upi_concr (upi : Upi) : Hyper :=
    fun ts => forall k k' t t',
        ts k t -> ts k' t' ->
        forall q p, upi q p = true -> upi_prop q p k k' t t'.

  Parameter upi_trans : Upi -> Uni -> Upi.

  Parameter upi_correct : forall upi uni t, sem_hyper (upi_concr upi) t -> upi_concr (upi_trans upi uni) t.

  Definition unch_trans_local (upi : Upi) (uni: Uni) (unch : Unch) (q p : Lab) (x : Var) : Lab :=
    if is_def x q p then p else if upi_trans upi uni (unch q x) p then unch q x else p.

  Lemma unch_trans_local_res : forall upi uni unch q p x, unch_trans_local upi uni unch q p x = p \/
                                                          unch q x =/= p /\
                                                          is_def x q p = false /\
                                                          unch_trans_local upi uni unch q p x = unch q x.
  Proof.
    intros.
    unfold unch_trans_local.
    destruct (is_def x q p); auto.
    destruct (upi_trans upi uni (unch q x) p); auto.
    destruct (unch q x == p); auto.
  Qed.

  Parameter preds : Lab -> list Lab.

  Parameter preds_spec : forall p q, has_edge q p = true <-> List.In q (preds p).

  Fixpoint all_equal {A : Type} `{EqDec A} (l : list A) (default : A) : A :=
    match l with
    | nil => default
    | a :: l' => fold_right (fun a acc => if a == acc then a else default) a l'
    end.

  Definition unch_trans (upi : Upi) (uni : Uni) (unch : Unch) : Unch :=
    fun p => fun x => all_equal (map (fun q => unch_trans_local upi uni unch q p x) (preds p)) p.

  Lemma unch_trans_res : forall upi uni unch q p x, q --> p ->
                                                    (unch_trans upi uni unch p x = p \/
                                                     unch q x =/= p /\ is_def x q p = false /\
                                                     unch_trans_local upi uni unch q p x = unch q x /\
                                                     unch_trans upi uni unch p x = unch q x).
  Proof.
    intros.
    unfold unch_trans.
    cut (List.In q (preds p)). 
    - destruct (preds p); intros; [ auto | simpl ]. 
      induction l0; simpl in *.
      + inversion_clear H0; [ subst | contradiction ].
        assert (Hlocal := unch_trans_local_res upi uni unch q p x).
        firstorder.
      + inversion_clear H0; subst; simpl.
        * destruct ((unch_trans_local upi uni unch a p x) == _); auto.
          rewrite e.
          eapply IHl0.
          auto.
        * inversion_clear H1; subst; simpl.
          -- destruct ((unch_trans_local upi uni unch q p x) == _); auto.
             assert (Hlocal := unch_trans_local_res upi uni unch q p x).
             firstorder.
          -- destruct ((unch_trans_local upi uni unch a p x) == _); auto.
             rewrite e.
             eapply IHl0.
             auto.
    - apply preds_spec.
      assumption.
  Qed.

  Lemma upi_unch :
    forall upi uni unch p x,
    unch_trans upi uni unch p x =/= p -> upi_trans upi uni (unch_trans upi uni unch p x) p = true .
  Proof.
    intros.
    remember (preds p) as pr.
    destruct pr.
    + unfold unch_trans in H.
      rewrite <- Heqpr in H.
      simpl in H.
      contradiction H; reflexivity.
    + cut (List.In l (preds p)). intro Hedge.
      - apply preds_spec in Hedge.
        assert (Hunch := unch_trans_res upi uni unch l p x Hedge).
        destruct Hunch as [Hunch | Hunch]; [ exfalso; contradiction H; reflexivity | ].
        destruct Hunch as [Huneq [Hdef [Hlocal Hunch]]].
        rewrite Hunch.
        unfold unch_trans_local in Hlocal.
        destruct (is_def x l p); [ inversion Hdef | clear Hdef ].
        destruct (upi_trans upi uni (unch l x) p).
        * reflexivity.
        * exfalso; apply Huneq; symmetry; assumption.
      - rewrite <- Heqpr. simpl. auto.
  Qed.
  
  Lemma list_emp_in : forall {A: Type} l, (forall (a: A), ~ List.In a l) -> l = nil.
  Proof.
    intros.
    induction l.
    - reflexivity.
    - cut (forall a, ~ List.In a l).
      + intros.
        apply IHl in H0.
        subst. specialize (H a).
        exfalso. simpl in H. auto.
      + intros. specialize (H a0).
        simpl in H. auto.
  Qed.

  Lemma unch_trans_root : forall upi uni unch x, unch_trans upi uni unch root x = root.
  Proof.
    intros.
    cut (preds root = nil); intros.
    + unfold unch_trans.
      rewrite H.
      simpl.
      reflexivity.
    + cut (forall q, ~ List.In q (preds root)); intros.
      * apply list_emp_in.
        assumption.
      * intro.
        eapply preds_spec in H.
        rewrite root_no_pred in H.
        inversion H.
  Qed.

  Definition joinb (l : list bool) := fold_right andb true l.

  Lemma joinb_true_iff {A : Type} : 
    forall f (l : list A), (joinb (map f l) = true) -> (forall x, List.In x l -> f x = true).
  Proof.
    intros.
    unfold joinb in H.
    induction l; inversion H0; simpl in H; apply andb_true_iff in H; try subst; destruct H; auto.
  Qed.

  Definition uni_trans (uni : Uni) (upi : Upi) (unch : Unch) : Uni :=
    fun p => if p == root then uni root
             else fun x => ((joinb (map (fun spl => match spl with (s, x) => uni s x end) (splits p))) 
                              && (joinb (map (fun q => abs_uni_eff (uni q) x) (preds p)))
                              && (joinb (map (fun q => upi_trans upi uni q p) (preds p)))
                           )
                           || (let u := unch_trans upi uni unch p x in (u <>b p) && uni u x).


  Lemma uni_trans_root_inv :
    forall uni hom unch x, uni_trans uni hom unch root x = uni root x.
  Proof.
    intros.
    unfold uni_trans.
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

  Lemma follows_exists_succ :
    forall p i s k tr, In k tr (p, i, s) ->
                       k =/= (p, i, s) ->
                       exists succ, Follows k tr succ (p, i, s).
  Proof.
    intros p i s k tr Hin Hneq.
    induction tr; inv_tr Hin; firstorder.
    destruct ((p, i, s) == k').
    - exists k. rewrite e0 in *. econstructor. 
    - symmetry in c. destruct H as [succ Hflw]; eauto.
      exists succ. constructor. eassumption.
  Qed.

  Lemma in_step_implies_follows k t p q :
    In k t p -> p =/= k -> eff p = Some q -> Follows k t q p.
  Proof.
    intros.
    induction t; inv_tr H; firstorder.
    - destruct (p == k').
      + rewrite e0 in *. rewrite e in H1. inversion H1; subst. constructor.
      + constructor. eauto.
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

  (*
  Lemma follows_implies_in_pred :
    forall k' k tr step succ pred, Follows k' (Step k' k tr) k' k -> In k tr k.
  Proof.
    intros k tr.
    induction tr; intros; inv_tr H.
    - repeat constructor. 
    - econstructor. eapply IHtr. eauto.
  Qed.
*)

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

  Lemma follows_pred_unique :
    forall c s s' k t step d, Follows (c, s) (Step (c, s) k t step) (c, s') d -> d = k.
  Proof.
    intros.
    inv_tr H.
    - reflexivity.
    - apply follows_implies_in in H5.
      destruct c as [p i].
      eapply ivec_fresh in step1; [| apply H5].
      firstorder.
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
    induction t; intros; inv_tr H; econstructor; eauto.
   Qed.

  Lemma follows_implies_precedes :
    forall k t p q i j s r,
      Follows k t (p, i, s) (q, j, r) -> Precedes k t (q, j, r) (p, i, s).
  Proof.
    intros k t p q i j s r Hflw.
    induction t; inv_tr Hflw.
    - constructor; try reflexivity. constructor. intros; split; reflexivity.
    - constructor. eauto.
  Qed.

  Lemma precedes_step :
    forall k k' t step p s, Precedes k' (Step k' k t step) p s ->
                            lab_of p =/= lab_of s ->
                            In k t p.
  Proof.
    intros.
    inv_tr H.
    - exfalso. apply H0. reflexivity.
    - eapply precedes_implies_in. eauto.
    - eapply precedes_implies_in. eauto.
  Qed.

  Lemma precedes_follows :
    forall k t c d e,
      Precedes k t c d ->
      Follows k t e d ->
      (lab_of c =/= lab_of d \/ c = d) ->
      Precedes k t c e.
  Proof.
    intros k t.
    induction t; intros c d next Hprec Hflw Hlab.
    - inv_tr Hflw.
    - destruct (k == next).
      * rewrite <- e0 in *; clear e0.
        inv_tr Hprec.
        + constructor.
        + constructor.
          assumption. assumption.
        + cut (d === k'). intros Heq.
          -- rewrite Heq in *.
             inversion_clear Hlab.
             ** destruct c as [[cp ci] cs].
                destruct k as [[kp ki] ks].
                destruct k' as [[kp' ki'] ks'].
                eapply Prec_cont; [ eassumption |].
                intros. contradiction H.
             ** rewrite H in *.
                destruct k as [[kp ki] ks].
                destruct k' as [[kp' ki'] ks'].
                eapply Prec_cont; [ eassumption | firstorder ].
          -- destruct k. eapply follows_pred_unique. eassumption.
      * inv_tr Hflw.
        + contradiction c0; reflexivity.
        + cut (k =/= d); intros.
          -- eapply Prec_other.
             inv_tr Hprec; try (exfalso; apply H; reflexivity).
             eauto.
          -- intro.
             apply follows_implies_step in Hflw.
             destruct k as [[p i] s].
             destruct d as [[q j] r].
             eapply follows_implies_in2 in H4.
             eapply ivec_fresh in step0; [| eassumption].
             injection H; intros.
             auto.
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

  Lemma unch_correct :
    forall upi uni unch k t,
      sem_trace (unch_concr unch) k t -> unch_concr (unch_trans upi uni unch) k t.
  Proof.
    intros upi uni unch k t Hred.
    unfold sem_trace in Hred.
    destruct Hred as [k' [t' [step [Hconcr H]]]]; subst.
    unfold unch_concr in *.
    intros to i s x.
    intros Hin.
    destruct (to == root).
    - rewrite e in *.
      exists i. exists s.
      split; [| reflexivity ].
      rewrite unch_trans_root.
      apply precedes_self.
      assumption.
    - apply follows_exists_detail in Hin; auto.
      destruct Hin as [q [j [r Hflw]]].
      specialize (Hconcr q j r x).
      assert (Hinq := Hflw).
      apply follows_implies_in2_step in Hinq.
      specialize (Hconcr Hinq).
      destruct Hconcr as [h [u [Hprec Heq]]].
      assert (Htrans := unch_trans_res upi uni unch q to x).
      destruct Htrans.
      apply edge_spec.
      unfold is_effect_on.
      exists j. exists i. exists r. exists s.
      eapply follows_implies_step; eassumption.
      * rewrite H.
        exists i. exists s.
        split; [| reflexivity].
        apply precedes_self.
        eapply follows_implies_in; eassumption.
      * destruct H as [Hqto [Hdef [_ H]]].
        rewrite H.
        destruct (unch q x == q).
        + exists j. exists r.
          split.
          -- eapply precedes_follows; [ | eassumption | ].
             ** rewrite e. apply precedes_self.
                eapply follows_implies_in2; eassumption.
             ** right. rewrite e. reflexivity.
          -- eapply no_def_untouched; try eassumption.
             eapply follows_implies_step; eassumption.
        + exists h. exists u.
          split.
          -- eapply precedes_follows; [ constructor | | left; simpl ]; eassumption.
          -- rewrite Heq. eapply no_def_untouched; try eassumption.
             eapply follows_implies_step; eassumption.
  Qed.

  Definition lab_tag_matches (l : Lab) (j : IVec) (k : Conf) : bool :=
    match k with
    | ((p, i), s) => (j ==b i) && (l ==b p) 
    end.

  Fixpoint label_tag_in_trace (l : Lab) (i : IVec) (k : Conf) (t : Tr k) : bool :=
    match t with
    | (Init s) => lab_tag_matches l i (root, start_ivec, s)
    | (Step k' k t _) => (lab_tag_matches l i k') || (label_tag_in_trace l i k t)
    end.

  Fixpoint label_in_trace (l : Lab) (k : Conf) (t : Tr k) : bool :=
    match t with
    | (Init s) => l ==b root
    | (Step k' k t _) => (l ==b lab_of k') || (label_in_trace l k t)
    end.

  Fixpoint last_inst_of (l : Lab) (k : Conf) (t : Tr k) : option IVec :=
    match t with
    | (Init s) => if l ==b root then Some start_ivec else None
    | (Step (q, j, _) k t _) => if (l ==b q) then Some j else last_inst_of l k t
    end.

  Lemma last_inst_not_exists :
    forall l k t, last_inst_of l k t = None <-> ~ exists i s, In k t (l, i, s).
  Proof.
    intros.
  Admitted.

  Lemma last_inst_precedes :
    forall l k t i, last_inst_of l k t = Some i <-> exists s, Precedes k t (l, i, s) k.
  Proof.
    intros.
    dependent induction t.
  Admitted.

  Lemma label_in_trace_in :
    forall l k t, label_in_trace l k t = true <-> exists i s, In k t (l, i, s).
  Proof.
    intros.
    induction t.
    - simpl. split; intros.
      + exists start_ivec, s. conv_bool H. rewrite H. constructor.
      + destruct H as [i [s' Hin]].
        inv_tr Hin.
        unfold equiv_decb.
        destruct (root == root); destruct (start_ivec == start_ivec); firstorder.
    - destruct k as [[p j] s].
      split; intros.
      + destruct (l == p).
        * rewrite e0 in *. exists j, s. constructor.
        * destruct IHt as [IHt _].
          simpl in H. conv_bool H.
          destruct H; [ exfalso; firstorder |].
          destruct IHt as [r [s' Hin]]; eauto.
          exists r, s'. eauto using In.
      + destruct IHt as [_ IHt].
        destruct H as [r [s' Hin]].
        simpl.
        inv_tr Hin; unfold equiv_decb.
        * destruct (l == l); firstorder.
        * destruct (l == p); simpl; auto; eapply IHt; eauto.
  Qed.

  Lemma not_label_in_trace_in :
    forall l k t, label_in_trace l k t = false <-> ~ exists i s, In k t (l, i, s).
  Proof.
    intros.
    split; intros. intro.
    + rewrite <- negb_true_iff in H.
      apply Is_true_eq_left in H.
      apply negb_prop_elim in H.
      apply H.
      apply Is_true_eq_left.
      apply label_in_trace_in; assumption.
    + rewrite <- negb_true_iff.
      apply Is_true_eq_true.
      apply negb_prop_intro.
      intro. apply H.
      apply Is_true_eq_true in H0.
      apply label_in_trace_in; assumption.
  Qed.

  Lemma label_tag_in_trace_in :
    forall l i k t, label_tag_in_trace l i k t = true <-> exists s, In k t (l, i, s).
  Proof.
    intros.
    induction t.
    - simpl. split; intros.
      + exists s. conv_bool H. destruct H. rewrite H. rewrite H0. constructor.
      + destruct H as [s' Hin].
        inv_tr Hin.
        unfold equiv_decb.
        destruct (root == root); destruct (start_ivec == start_ivec); firstorder.
    - destruct k as [[p j] s].
      split; intros.
      remember (lab_tag_matches l i (p, j, s)) as eq.
      symmetry in Heqeq. simpl in Heqeq.
      + destruct eq; conv_bool Heqeq.
        * destruct Heqeq. rewrite H0. rewrite H1. exists s. constructor.
        * destruct IHt as [IHt _].
          simpl in H. conv_bool H.
          destruct H; [ exfalso; firstorder |].
          destruct IHt as [r Hin]; eauto.
          exists r. eauto using In.
      + destruct IHt as [_ IHt].
        destruct H as [r Hin].
        simpl.
        inv_tr Hin; unfold equiv_decb.
        * destruct (l == l); destruct (i == i); firstorder.
        * destruct (l == p); destruct (i == j); simpl; auto; eapply IHt; eauto.
  Qed.

  Lemma not_label_tag_in_trace_in :
    forall l i k t, label_tag_in_trace l i k t = false <-> ~ exists s, In k t (l, i, s).
  Proof.
    intros.
    split; intros. intro.
    + rewrite <- negb_true_iff in H.
      apply Is_true_eq_left in H.
      apply negb_prop_elim in H.
      apply H.
      apply Is_true_eq_left.
      apply label_tag_in_trace_in; assumption.
    + rewrite <- negb_true_iff.
      apply Is_true_eq_true.
      apply negb_prop_intro.
      intro. apply H.
      apply Is_true_eq_true in H0.
      apply label_tag_in_trace_in; assumption.
  Qed.
  
  Lemma in_succ_in k p q t :
    In k t p -> p =/= k -> eff p = Some q -> In k t q.
  Proof.
    intros.
    dependent induction t; inv_tr H; try firstorder.
    destruct (p == k').
    + rewrite e0 in *. clear e0.
      inv_tr H; firstorder.
      rewrite H1 in step1. injection step1; intros. symmetry in H3. subst. constructor.
    + constructor. eauto.
  Qed.

  Lemma in_succ_exists p q i j s r t :
    In (p, i, s) t (q, j, r) -> (exists k', eff (q, j, r) = Some k' /\ In (p, i, s) t k') \/ (p, i, s) = (q, j, r).
  Proof.
    intros Hin.
    dependent induction t; inv_tr Hin; eauto.
    destruct k' as [[a l] u].
    left.
    specialize (IHt a l u t).
    destruct IHt; eauto.
    + destruct H as [k' H]. exists k'. split; try constructor; firstorder.
    + injection H; intros; subst. exists (p, i, s). firstorder. constructor.
  Qed.

  Definition DivergentBranch br k k' t t' :=
    (exists a b, DisjointPaths br (lab_of k) (lab_of k') a b) /\
    (exists x l u u', val_true (u x) =/= val_true (u' x) /\
                      In k t (br, l, u) /\
                      In k' t' (br, l, u') /\
                      exists tt ff, branch br = Some (tt, ff, x)).

  Lemma different_tgt_is_branch {br : Lab} {i : IVec} {s s' : State} {k k' : Conf} :
    eff (br, i, s) = Some k ->
    eff (br, i, s') = Some k' ->
    lab_of k =/= lab_of k' ->
    exists x, val_true (s x) =/= val_true (s' x) /\ (branch br = Some (lab_of k, lab_of k', x) \/
                                                     branch br = Some (lab_of k', lab_of k, x)).
  Proof.
    intros Hstep Hstep' Hneq.
    assert (Hspec := branch_spec br).
    destruct (branch br) as [[[tt ff] x] | ].
    + assert (Hspec' := Hspec i s' k' Hstep').
      specialize (Hspec i s k Hstep).
      destruct k as [[q j] r], k' as [[q' j'] r']. simpl in *.
      destruct Hspec as [Hspec _].
      destruct Hspec' as [Hspec' _].
      destruct (val_true (s x) == val_true (s' x)).
      * rewrite <- e in *. clear e.
        destruct (val_true (s x)), (val_true (s' x)); subst; firstorder.
      * exists x. split. eassumption.
        destruct (val_true (s x)), (val_true (s' x)); subst; 
          solve [ exists x; eauto | firstorder ].
    + specialize (Hspec i i s s' k k' Hstep Hstep'). firstorder.
  Qed.

  Lemma single_edge_disjoint_path (q a q' : Lab) (p : Path a q') :
    ~ PathIn q a q' p ->
    a --> q ->
    exists p', DisjointPaths a q' q p p'.
  Proof.
    intros Hnin Hedge.
    exists (PathStep a a q  (PathInit a) Hedge).
    unfold DisjointPaths.
    intros p' H H'.
    simpl in H'.
    inversion_clear H'.
    rewrite H0 in *. clear H0. contradiction H. eauto.
  Qed.

  Section Disjoint.
    Variable p q q' : Lab.
    Variable i j j' : IVec.
    Variable s s' r r' : State.

    Variable t : Tr (q, j, r).
    Variable t' : Tr (q', j', r').

    Variable Hstep: eff (q, j, r) = Some (p, i, s).
    Variable Hstep': eff (q', j', r') = Some (p, i, s').

    Section ContainsQ.
    
      Lemma contains_label_tag_disjoint : 
        label_tag_in_trace q j (q', j', r') t' = true ->
        q =/= q' \/ j =/= j' ->
        DivergentBranch q (q, j, r) (q', j', r') t t'.
      Proof.
        intros Hintr Hneq.
        apply label_tag_in_trace_in in Hintr.
        destruct Hintr as [u Hinq].
        + assert (Hnext := Hinq).
          apply in_succ_exists in Hnext.
          destruct Hnext as [[k' [Hnext Hin]] | H]; [| injection H; intros; subst; firstorder ].
          destruct k' as [[b m] w].
          enough (b =/= p).
          * specialize (different_tgt_is_branch Hnext Hstep H) as Hbr.
            destruct Hbr as [x [Hneqx Hbr]]. simpl in Hbr.
            unfold DivergentBranch. split; simpl.
            - unfold DisjointPaths.
              exists (PathInit q). exists (trace_exists_path Hinq).
              intros p' Paq' Paa. simpl in Paa. eauto.
            - exists x, j, r, u. symmetry in Hneqx.
              repeat split; try eauto; try constructor.
              inversion_clear Hbr; eauto.
          * intro. rewrite H in *. clear H. eapply ivec_fresh.
            apply Hstep'. apply Hin. eauto using ivec_det.
      Qed.

    End ContainsQ.

    Section NotContainsQ.

      Variable Hqq' : label_tag_in_trace q j (q', j', r') t' = false.
      Variable Hq'q : label_tag_in_trace q' j' (q, j, r) t = false.

      Lemma last_instance :
        forall j'', last_inst_of q (q', j', r') t' = Some j'' ->
        j = j'' \/ ~ upi_prop q p (q, j, r) (q', j', r') t t'.
      Proof.
      Admitted.


  Lemma not_contains_label_tag_last_common p i s' q q' j j' r r' step' t t' : 
    Follows (p, i, s') (Step (p, i, s') (q', j', r') t' step') (p, i, s') (q', j', r') ->
    (exists s, eff (q, j, r) = Some (p, i, s)) ->
    label_tag_in_trace q j (q', j', r') t' = false ->
    label_tag_in_trace q' j' (q, j, r) t = false ->
    (exists br, DivergentBranch br (q', j', r') (q, j, r) t' t) \/ ~ upi_prop q p (q, j, r) (q', j', r') t t'.
  Proof.
    intros Hflw' Hstepqp Hqq' Hq'q.
    (* assert (Hsucc : exists k', eff (q, j, r) = Some k') by (eauto using follows_implies_step). *)
    dependent induction t.
    - simpl in Hqq'.
      apply not_label_tag_in_trace_in in Hqq'.
      exfalso. apply Hqq'.
      clear Hflw' Hqq' Hq'q step'.
      induction t'.
      + exists s; eauto using In.
      + destruct IHt'; eauto using In.
    - destruct k' as [[a l] u].
      specialize (IHt a l u step' t).
      simpl in Hq'q. conv_bool Hq'q. destruct Hq'q as [Hnj Hnq].
      destruct (label_tag_in_trace a l (q', j', r') t') eqn:Hal.
      + clear IHt.

        (* show that q',j' cannot be the branch *)
        apply not_label_tag_in_trace_in in Hnq.
        assert (Haq: (a, l) =/= (q', j')).
        intro. apply Hnq. injection H; intros; subst. exists u. constructor.
        
        (* show that a,l has a successor that is on the q',j' trace *)
        apply label_tag_in_trace_in in Hal. destruct Hal as [u' Hain].
        assert (Hain' := Hain).
        eapply in_succ_exists in Hain'.
        inversion_clear Hain'.
        -- destruct H as [[[b m] w] [step Hxin]].
           enough (q =/= b).
           ** destruct (last_inst_of q (q', j', r') t') as [j''|] eqn:Hinst.
              ++ eapply last_inst_precedes in Hinst. destruct Hinst as [s'' Hinst].
                 destruct (j'' == j).
                 +++ exfalso. rewrite e0 in *. clear e0.
                     apply precedes_implies_in in Hinst.
                     eapply not_label_tag_in_trace_in in Hqq'. firstorder.
                 +++ right. intro. apply c. eapply H0; admit.
              ++ eapply last_inst_not_exists in Hinst.
                 left. exists a. unfold DivergentBranch. split.
                 +++ remember (trace_exists_path Hain) as Paq'.
                     eapply (not_in_trace_exists_path _ _ _ _ Hain) in Hinst.
                     destruct Hinst as [path Hinst]. 
                     simpl in *. eexists path.
                     eauto using single_edge_disjoint_path, step_conf_implies_edge.
                 +++ assert (Hdiff := different_tgt_is_branch e step H).
                     destruct Hdiff as [x [Hneq Hbr]].
                     simpl in Hbr. exists x, l, u', u. symmetry in Hneq.
                     repeat split; eauto; try repeat constructor.
                     inversion Hbr; eauto.
           ** intro. rewrite H in *. clear H.
              replace m with j in * by (eauto using ivec_det).
              apply not_label_tag_in_trace_in in Hqq'. apply Hqq'; eauto.
        -- injection H; intros; subst. exfalso. apply Hnq. exists u. constructor.
      + destruct (last_inst_of q (q', j', r') t') as [j''|] eqn:Hinst.
        ++ eapply last_inst_precedes in Hinst. destruct Hinst as [s'' Hinst].
           destruct (j'' == j).
           +++ exfalso. rewrite e0 in *. clear e0.
               apply precedes_implies_in in Hinst.
               eapply not_label_tag_in_trace_in in Hqq'. firstorder.
           +++ right. intro. apply c. eapply H; admit.
        ++

        assert (exists br, DivergentBranch br (q', j', r') (a, l, u) t' t) by eauto.
        clear Hflw' IHt.
        unfold DivergentBranch in *. 
        destruct H as [br [[Pbrq' [Pbra Hdisj]] [x [m [w [w' [Hneqx [Hin [Hin' Hbr']]]]]]]]].
        simpl in *.
        exists br.
        split.
        * exists Pbrq'.
          destruct (Path_in_dec q br q' Pbrq') eqn:Hinp.
          +++ admit.
        * exists x, m, w, w'.
          repeat split; try repeat constructor; eauto.
   Admitted.

  Definition lift (tr : Traces) : Hyper :=
    fun ts => ts = tr.

  Definition red_prod (h h' : Hyper) : Hyper :=
    fun ts => h ts /\ h' ts.

  Lemma uni_correct :
    forall uni upi unch t,
        sem_hyper (red_prod (red_prod (uni_concr uni) (upi_concr upi)) (lift (unch_concr unch))) t ->
        uni_concr (uni_trans uni upi unch) t.
  Proof.
    intros uni upi unch t Hred.
    unfold sem_hyper in Hred.
    destruct Hred as [ts [Hconcr Hstep]].
    intros k k' tr tr' Hsem Hsem' x p i s s'.
    intros HIn HIn' Htrans.

    assert (upi_concr (upi_trans upi uni) t) as HCupi.
    apply upi_correct.
    destruct Hconcr as [[_ Hhom] _].
    exists ts; auto.

    assert (unch_concr (unch_trans upi uni unch) k tr) as HCunch.
    destruct Hconcr as [[_ _] Hunch].
    unfold lift in *; subst.
    apply unch_correct. assumption.
    
    assert (unch_concr (unch_trans upi uni unch) k' tr') as HCunch'.
    destruct Hconcr as [[_ _] Hunch].
    unfold lift in *; subst.
    apply unch_correct. assumption.

    destruct Hconcr as [[HCuni HCupi'] _].

    subst.
    destruct Hsem as [l [ltr [lstep [Hts Hlstep]]]]; subst.
    destruct Hsem' as [l' [ltr' [lstep' [Hts' Hlstep']]]]; subst.
    unfold uni_trans in Htrans. 

    destruct (equiv_dec p root); [ subst | ].
    + rewrite e in *; clear e.
      inv_tr HIn.
      - exfalso. eapply start_no_tgt. eassumption.
      - inv_tr HIn'.
        * exfalso. eapply start_no_tgt. eassumption.
        * eapply (HCuni l l' ltr ltr'); try eassumption.

    + rewrite orb_true_iff in Htrans.
      destruct Htrans as [Htrans | Hunch].
        (* The uni/hom case *)
      - repeat rewrite andb_true_iff in Htrans.
        destruct Htrans as [[Hsplit Hpred] Hupi].
        apply follows_exists in HIn; try eassumption.
        apply follows_exists in HIn'; try eassumption.
        destruct HIn as [[[q j] sq] Hflw].
        destruct HIn' as [[[q' j'] sq'] Hflw'].
        assert (List.In q (preds p)) as Hqpred.
        eapply preds_spec. eapply edge_spec. 
        exists j. exists i. exists sq. exists s. eapply follows_implies_step. apply Hflw.
        cut (q' = q); intros; subst.
        * cut (j' = j); intros; subst.
          -- eapply (local_uni_corr (uni q) q j p i sq sq' s s');
               unfold uni_state_concr in *.
             ** intros.
                unfold uni_concr in HCuni .
                eapply (HCuni l l' ltr ltr' Hts Hts' x0 q j);
                  try eapply follows_implies_in2_step; eassumption.
             ** eapply follows_implies_step; eassumption.
             ** eapply follows_implies_step; eassumption.
             ** eapply joinb_true_iff in Hpred.
                eapply Hpred.
                assumption.
          -- (* unique preceding instances *)
             eapply HCupi.
             exists l; exists ltr; exists lstep; auto.
             exists l'; exists ltr'; exists lstep'; auto.
             eapply joinb_true_iff in Hupi.
             eapply Hupi.
             eassumption.
             eapply follows_implies_precedes; try eassumption.
             eapply follows_implies_precedes; try eassumption.
        * (* disjoint paths! *)
          destruct (q == q'); [ eauto | exfalso ].
          

          admit.

        (* The unch case *)
      - specialize (HCunch p i s x).
        specialize (HCunch' p i s' x).
        destruct HCunch as [j [r [Hprec Heq]]]; try eassumption.
        destruct HCunch' as [j' [r' [Hprec' Heq']]]; try eassumption.
        apply andb_true_iff in Hunch.
        destruct Hunch as [ Hlab Hunch ].
        unfold nequiv_decb in Hlab.
        unfold equiv_decb in Hlab.
        apply negb_true_iff in Hlab.
        destruct (equiv_dec (unch_trans upi uni unch p x));
          [inversion Hlab | clear Hlab].
        rewrite <- Heq. rewrite <- Heq'.
        cut (j' = j); intros.
        * subst j'.
          eapply HCuni; [ apply Hts | apply Hts' | | | ].
          eapply precedes_step; eassumption.
          eapply precedes_step; eassumption.
          assumption.
        * eapply HCupi.
          -- exists l; exists ltr; exists lstep; auto.
          -- exists l'; exists ltr'; exists lstep'; auto.
          -- eapply upi_unch. apply c0.
          -- eassumption.
          -- eassumption.
Qed.
