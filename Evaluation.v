Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Utils.
Require Import Coq.Logic.Classical.
Require Import List.
Require Import Nat.
Require Import Bool.Bool.
Require Import Coq.Logic.Eqdep_dec.

Require Graph.
Require Import Util.

Module Evaluation.

  Export Graph.Graph.

  Parameter Val : Type.
  Definition Tag := list nat.

  Definition State := Var -> Val.

  Variable Val_dec : EqDec Val eq.
  Variable Tag_dec : EqDec Tag eq.
  Variable State_dec : EqDec State eq.

  
  Parameter start_tag : Tag.

  Definition States := State -> Prop.
  Definition Coord := prod Lab Tag.
  Definition Conf := prod Coord State.

  Hint Unfold Conf Coord.

  Definition lab_of (k : Conf) :=
    match k with
      ((p, i), s) => p
    end.

    Parameter eff' : Lab * State -> option (Lab * State).
  
  Fixpoint eff_tag (k : Conf) : Tag
    := match k with
         (p, i, s)
         => match eff' (p,s) with
             Some (q , r)
             => if is_back_edge p q
               then match i with
                    | nil => nil
                    | n :: l => (S n) :: l
                    end
               else 
                    let l' := @iter Tag (@tl nat) i (loop_exit p) in
                    @iter Tag (@cons nat O) l' (loop_head q)
                |
             None => nil
           end
       end.

  Definition eff (k : Conf) : option Conf
    := match k with
       | (p, i, s) => match eff' (p,s) with
                  | None => None
                  | Some (q, r) => Some (q, eff_tag k, r)
                  end
       end.

    Lemma Conf_dec :
    forall (x y : Conf), {x = y} + {x <> y}.
  Proof.
    intros.
    destruct x as [[p i] s], y as [[q j] r].
    destruct ((p, i, s) == (q, j, r)); firstorder.
  Qed.
  Instance conf_eq_eqdec : EqDec Conf eq := Conf_dec.


  Definition start_coord := (root, start_tag) : Coord.

  Definition is_effect_on (p q : Lab) :=
    exists i i' s s', eff ((p, i), s) = Some ((q, i'), s').

  Parameter edge_spec :
    forall p q, is_effect_on p q -> p --> q.

  Lemma step_conf_implies_edge :
    forall p q i j s r, eff (p, i, s) = Some (q, j, r) -> (p --> q).
  Proof.
    intros.
    eapply edge_spec. 
    unfold is_effect_on. eauto.
  Qed.

  Parameter def_spec :
    forall p q x, (exists i j s r, eff (p, i, s) = Some (q, j, r) /\ r x <> s x) ->
                  is_def x p q = true.

  Inductive ne_list (A : Type) : Type :=
  | ne_single : A -> ne_list A
  | ne_cons : A -> ne_list A -> ne_list A.


  Arguments ne_single {_} _.
  Arguments ne_cons {_} _ _.
  
  Infix ":-:" := ne_cons (at level 70).

  Fixpoint ne_hd {A : Type} (l : ne_list A) : A
    := match l with
       | ne_single a => a
       | ne_cons a _ => a
       end.

  Fixpoint ne_to_list {A : Type} (l : ne_list A) : list A
    := match l with
       | ne_single a => a :: nil
       | a :-: l => a :: ne_to_list l
       end.

  Coercion ne_to_list : ne_list >-> list.

  Fixpoint ne_tl {A : Type} (l : ne_list A) : list A
    := match l with
       | ne_single _ => nil
       | _ :-: l => l
       end.  

  Definition ne_In {A : Type} (a : A) (l : ne_list A) : Prop
    := a = ne_hd l \/ In a l.

  Inductive Tr : ne_list Conf -> Prop :=
    | Init : forall s, Tr (ne_single (root, start_tag, s))
    | Step : forall l k, Tr l -> eff (ne_hd l) = Some k -> Tr (k :-: l).

  Ltac inv_dep H Dec := inversion H; subst; 
                        repeat match goal with
                               | [ H0: @existT _ _ _ _ = @existT _ _ _ _  |- _ ] =>
                                 apply inj_pair2_eq_dec in H0; try (apply Dec); subst
                               end.

  Ltac inv_tr H := inversion H; subst; 
                   repeat match goal with
                          | [ H0: @existT Conf _ _ _ = @existT _ _ _ _  |- _ ] => apply inj_pair2_eq_dec in H0; try (apply Conf_dec); subst
                          end.

  Definition trace := {l : ne_list Conf | Tr l}.

  Definition Traces := trace -> Prop.
  Definition Hyper := Traces -> Prop.

  (* This is the concrete transformer for sets of traces *)
  Definition sem_trace (ts : Traces) : Traces :=
    fun tr => ts tr /\ exists k, Tr (k :-: (` tr)%prg).

  (* This is the hypertrace transformer.
     Essentially, it lifts the trace set transformers to set of trace sets *)
  Definition sem_hyper (T : Hyper) : Hyper :=
    fun ts' => exists ts, T ts /\ ts' = sem_trace ts.

  Lemma ne_hd_hd {A : Type} (a : A) l : a = ne_hd l -> Some a = hd_error l.
  Proof.
    intros H.
    induction l; cbn in *; subst a; reflexivity.
  Qed.

  Lemma tr_in_dec :
    forall (k : Conf) t, {ne_In k t} + {~ ne_In k t}.
  Proof.
    intros k t. unfold ne_In.
    induction t; cbn in *.
    - destruct (k == a ); [left|right]; eauto.
      intro H. destruct H as [H | [H | H]]; eauto. apply c. subst a. reflexivity. 
    - inversion_clear IHt. 
      + left. destruct H.
        * right. right. apply ne_hd_hd in H. 
          induction (ne_to_list t); cbn in *.
          -- congruence.
          -- left. inversion H. reflexivity.
        * tauto.
      + destruct (k == a); [left|right]; eauto. firstorder.
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

  Lemma in_pred_exists p i s k t :
    forall k' step, In k' (Step k' k t step) (p, i, s) ->
    p =/= root ->
    exists q j r, In k t (q, j, r) /\ eff (q, j, r) = Some (p, i, s).
  Proof.
    intros k' step Hin Hneq.
    dependent induction t.
    - inv_tr Hin.
      + exists root, start_tag, s0. split; [ constructor | assumption ].
      + inv_tr H3. firstorder.
    - inv_tr Hin.
      + destruct k as [[q j] r].
        exists q, j, r. split; [ constructor | assumption ].
      + edestruct IHt as [q [j [r [Hinq Hstep]]]]; try eassumption.
        exists q, j, r. 
        split; eauto using In.
  Qed.


  Parameter ivec_fresh : forall p i s k t, eff k = Some (p, i, s) ->
                                      forall q j r, In k t (q, j, r) ->
                                               j <> i.

  Parameter ivec_det : forall q j r r' p i i' s s',
      eff (q, j, r) = Some (p, i, s) ->
      eff (q, j, r') = Some (p, i', s') ->
      i = i'.

  Inductive Precedes : forall k, Tr k -> Conf -> Conf -> Prop :=
  | Pr_in : forall k t, Precedes k t k k
  | Pr_cont : forall q q' p i j j' r' r s t step, Precedes (q', j', r') t (q, j, r) (q', j', r') -> 
                                                  p =/= q ->
                                                  Precedes (p, i, s) (Step (p, i, s) (q', j', r') t step) (q, j, r) (p, i, s)
  | Pr_other : forall k' k t c c' step, Precedes k t c c' ->
                                        Precedes k' (Step k' k t step) c c'.


  Lemma precedes_implies_in_pred k t k' k'' :
    Precedes k t k' k'' -> In k t k'.
  Proof.
    intros H.
    dependent induction t.
    - inv_tr H. constructor.
    - inv_tr H; eauto using In.
  Qed.

  Lemma precedes_implies_in_succ k t k' k'' :
    Precedes k t k' k'' -> In k t k''.
  Proof.
    intros H.
    dependent induction t.
    - inv_tr H. constructor.
    - inv_tr H; eauto using In.
  Qed.

  Inductive Prefix : forall k, Tr k -> forall k', Tr k' -> Prop :=
  | PrefixSame : forall k t, Prefix k t k t
  | PrefixStep : forall k'' k' k step t t', Prefix k t k' t' ->
                                       Prefix k t k'' (Step k'' k' t' step).
    
  Lemma precedes_prefix k t c c' : 
    Precedes k t c c' ->
    exists tr, Prefix c' tr k t /\ Precedes c' tr c c'.
  Proof.
    intros Hprec.
    dependent induction t.
    + inv_tr Hprec.
      - eexists. split; eauto using Prefix.
    + inv_tr Hprec.
      - eexists. split; constructor.
      - eexists. split; [ constructor | eassumption ].
      - eapply IHt in H4.
        destruct H4 as [tr [Hprefix Hprec']].
        exists tr. split; eauto using Prefix. 
  Qed.

  Lemma precedes_prefix_inv k t c c' l tr k' step : 
    Precedes k' (Step k' k t step) c c' ->
    Prefix k t l tr ->
    forall l' step', Precedes l' (Step l' l tr step') c c'.
  Proof.
    intros Hprec Hprefix.
    dependent induction Hprefix; intros l' step'.
    + cut (Some k' = Some l'); intros.
      - inject H.
        cut (step = step'); intros; subst; try eassumption.
        clear Hprec. destruct step'. apply UIP_refl.
      - rewrite <- step. eassumption.
    + constructor. eapply IHHprefix. eassumption.
  Qed.

    Lemma in_prefix k t c : 
    In k t c ->
    exists pt, Prefix c pt k t /\
          In c pt c.
  Proof.
    intros.
    dependent induction t.
    + inv_tr H. exists (Init s). split; constructor.
    + inv_tr H.
    - exists tr0. split; constructor.
    - eapply IHt in H4. destruct H4 as [pt [Hprefix Hin]].
      exists pt. split; [ constructor | ]; eassumption.
  Qed.
  
  Lemma in_prefix_in k t c k' t' :
    In k t c ->
    Prefix k t k' t' ->
    In k' t' c.
  Proof.
    intros Hin Hprefix. dependent induction Hprefix; eauto using In.
  Qed.

  Fixpoint last_inst_of (l : Lab) (k : Conf) (t : Tr k) : option Tag :=
    match t with
    | (Init s) => if l == root then Some start_tag else None
    | (Step (q, j, _) k t _) => if (l == q) then Some j else last_inst_of l k t
    end.

  Lemma last_inst_precedes_inv_helper q j r q' j' r' t e br m w :
    Precedes (q, j, r) (Step (q, j, r) (q', j', r') t e)
            (br, m, w) (q, j, r) ->
    br =/= q ->
    Precedes (q', j', r') t (br, m, w) (q', j', r').
  Proof.
    intros Hprec Hneq.
    inv_tr Hprec.
    - contradiction Hneq; reflexivity.
    - eauto.
    - exfalso. eapply (ivec_fresh _ _ _ _ _ step0); [ |reflexivity].
      eauto using precedes_implies_in_succ. 
  Qed.

  Lemma last_inst_precedes_inv q j r br m w t : 
    Precedes (q, j, r) t (br, m, w) (q, j, r) ->
    last_inst_of br (q, j, r) t = Some m.
  Proof.
    intros Hprec.
    dependent induction t; intros; simpl.
    + destruct (br == root).
      rewrite e in *. clear e.
      inv_tr Hprec.
      - reflexivity.
      - inv_tr Hprec.
        contradiction c; reflexivity.
    + destruct k' as [[q' j'] r']. 
      destruct (br == q).
      * rewrite e0 in *. clear e0.
        inv_tr Hprec; try reflexivity.
        - contradiction H10; reflexivity.
        - exfalso. eapply ivec_fresh. eapply step0.
          eapply precedes_implies_in_succ. eassumption. reflexivity.
      * eapply IHt; try reflexivity. 
        eauto using last_inst_precedes_inv_helper.
  Qed.

  Lemma last_inst_precedes q j r br m t : 
    last_inst_of br (q, j, r) t = Some m -> 
    exists w, Precedes (q, j, r) t (br, m, w) (q, j, r).
  Proof.
    intros Hin.
    dependent induction t; intros; simpl in Hin.
    + destruct (br == root).
      - rewrite e in *. clear e.
        injection Hin; intros; subst.
        exists r. constructor.
      - inversion Hin.
    + destruct k' as [[q' j'] r']. 
      destruct (br == q).
      * rewrite e0 in *. clear e0.
        injection Hin; intros; subst; clear Hin.
        exists r. constructor.
      * eapply IHt in Hin; eauto.
        destruct Hin as [w Hprec].
        exists w. symmetry in c. eauto using Precedes.
  Qed.

(*  Definition unique_preceding q p :=
      forall k k' t t' j j' i r r' s s',
      Precedes k t (q, j, r) (p, i, s) ->
      Precedes k' t' (q, j', r') (p, i, s') ->
      j' = j.*)

  Lemma path_for_trace k tr k' (Hin : In k tr k') :
    { p: Path (lab_of k') (lab_of k) | forall q, PathIn q p -> exists j r, In k tr (q, j, r) }.
  Proof.
    destruct k as [[q j] r], k' as [[p i] s]. simpl.
    dependent induction tr; intros.
    + simpl.
      enough (p = root).
      - subst. exists (PathInit root). simpl. intros. rewrite H. eauto.
      - inv_tr Hin; reflexivity.
   + destruct k' as [[q' j'] r']; simpl in *.
     destruct (p == q).
     * rewrite e0. clear e0. exists (PathInit q). intros. 
       inversion_clear H; subst. exists j, r. constructor.
     * edestruct IHtr; eauto. inv_tr Hin.
       - contradiction c; reflexivity.
       - eapply H3.
       - exists (PathStep p q' q x (step_conf_implies_edge q' q _ _ _ _ e)).
         intros. simpl in H. inversion_clear H.
         ++ rewrite H0. exists j, r. constructor.
         ++ eapply e0 in H0. destruct H0 as [j0 [r0 H0]].
            exists j0, r0. eauto using In.
  Qed.

  Lemma not_in_trace_exists_path (q : Lab) (k k' : Conf) (t : Tr k) (Hin : In k t k') : 
    ~ (exists j r, In k t (q, j, r)) ->
    ~ PathIn q (proj1_sig (path_for_trace k t k' Hin)).
  Proof.
    intros Hnin.
    intro. apply Hnin. clear Hnin.
    remember (path_for_trace k t k' Hin) as p.
    clear Heqp.
    destruct p as [p Hpin]; simpl in *.
    eauto.
  Qed.
  
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

  Lemma precedes_self k t :
    forall c, In k t c -> Precedes k t c c.
  Proof.
    intros c H.
    destruct c as [[p i] s].
    dependent induction t.
    + inv_tr H. constructor.
    + destruct k' as [[q j] r].
      inv_tr H; eauto using Precedes.
  Qed.

  Lemma precedes_step_inv :
    forall k k' t step p s, Precedes k' (Step k' k t step) p s ->
                            lab_of p =/= lab_of s ->
                            In k t p.
  Proof.
    intros.
    inv_tr H.
    - firstorder.
    - eapply precedes_implies_in_pred. eauto.
    - eapply precedes_implies_in_pred. eauto.
  Qed.

  Lemma precedes_incl k t c c' :
    Precedes k t c c' -> exists t', Precedes c' t' c c'.
  Proof.
    intros. dependent induction t; inv_tr H; eauto.
  Qed.

  Lemma in_exists_pred p i s k t :
    forall k' step, In k' (Step k' k t step) (p, i, s) ->
    p <> root ->
    exists q j r, In k t (q, j, r) /\ eff (q, j, r) = Some (p, i, s).
  Proof.
    intros k' step H Hneq.
    dependent induction t; inv_tr H.
    - exists root, start_tag, s0. split; [ constructor | eauto ].
    - inv_tr H4. firstorder.
    - destruct k as [[q j] r]. exists q, j, r.
      split; [ constructor | eauto ].
    - eapply IHt in H4; eauto. destruct H4 as [q [j [r [Hin Hstep]]]].
      exists q, j, r. split; [ constructor |]; eauto.
  Qed.

  Lemma precedes_succ k t :
    forall q j r q' j' r' p i s k' step, Precedes k t (q', j', r') (q, j, r) ->
                                         eff (q, j, r) = Some (p, i, s) ->
                                         p =/= q' ->
                                         Precedes k' (Step k' k t step) (q', j', r') (p, i, s).
  Proof.
    dependent induction t.
    - intros.
      destruct k' as [[p' i'] s'].
      inv_tr H. enough (Some (p, i, s0) = Some (p', i', s')).
      injection H2; intros; subst. eauto using Precedes.
      rewrite <- H0. eauto.
    - intros. inv_tr H.
      * injection H5; intros; subst.
        enough (Some k'0 = Some (p, i, s)). injection H2; intros; subst.
        eauto using Precedes.
        rewrite <- step. eassumption.
      * enough (Some k'0 = Some (p, i, s)). injection H4; intros; subst.
        eauto using Precedes.
        rewrite <- step. eassumption.
      * eauto using Precedes.
  Qed.

  Lemma precedes_step k t q j r to i s :
    forall k' step, In k t (q, j, r) ->
                    to =/= q ->
                    eff (q, j, r) = Some (to, i, s) ->
                    Precedes k' (Step k' k t step) (q, j, r) (to, i, s).
  Proof.
    intros k' step Hin Hneq Hstep.
    dependent induction t.
    - inv_tr Hin.
      enough (Some k' = Some (to, i, s0)).
      injection H; intros; subst. eauto using Precedes.
      rewrite <- step. eassumption.
    - inv_tr Hin.
      * enough (Some k'0 = Some (to, i, s)).
        injection H; intros; subst. eauto using Precedes.
        rewrite <- step. eassumption.
      * eauto using Precedes.
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

    
  Definition lab_tag_matches (l : Lab) (j : Tag) (k : Conf) : bool :=
    match k with
    | ((p, i), s) => (j ==b i) && (l ==b p) 
    end.

  Fixpoint label_tag_in_trace (l : Lab) (i : Tag) (k : Conf) (t : Tr k) : bool :=
    match t with
    | (Init s) => lab_tag_matches l i (root, start_tag, s)
    | (Step k' k t _) => (lab_tag_matches l i k') || (label_tag_in_trace l i k t)
    end.

  Fixpoint label_in_trace (l : Lab) (k : Conf) (t : Tr k) : bool :=
    match t with
    | (Init s) => l ==b root
    | (Step k' k t _) => (l ==b lab_of k') || (label_in_trace l k t)
    end.

  Lemma last_inst_self a l u t :
     last_inst_of a (a, l, u) t = Some l.
  Proof.
    dependent induction t.
    + simpl. destruct (root == root); firstorder. 
    + simpl. destruct (a == a); firstorder. 
  Qed.

  Lemma last_inst_step l p i s k t step : 
    l =/= p -> last_inst_of l k t = last_inst_of l (p, i, s) (Step (p, i, s) k t step).
  Proof.
    intros Hneq.
    simpl. destruct (l == p); firstorder. 
  Qed.
    
  Lemma last_inst_not_exists :
    forall l k t, last_inst_of l k t = None <-> ~ exists i s, In k t (l, i, s).
  Proof.
    intros.
    destruct k as [[p i] s].
    dependent induction t.
    + split; intros.
      - simpl in H. destruct (l == root); try inversion H.
        intro. destruct H0 as [j [r H0]].
        inv_tr H0. contradiction c. reflexivity.
      - simpl. destruct (l == root); try firstorder.
        exfalso. rewrite e in *. eapply H. exists s. constructor.
    + destruct k' as [[q j] r].
      split; intros.
      - simpl in H. destruct (l == p); [ inversion H |].
        intro. eapply IHt; eauto.
        destruct H0 as [m [w H0]]. exists m, w.
        inv_tr H0; firstorder.
      - simpl.
        destruct (l == p).
        * exfalso. apply H. rewrite e0. eauto using In.
        * eapply IHt; eauto. intro. apply H.
          destruct H0 as [m [w H0]].
          eauto using In.
  Qed.

  Lemma last_inst_in :
    forall l k t i, last_inst_of l k t = Some i -> exists s, In k t (l, i, s).
  Proof.
    intros. dependent induction t; simpl in H.
    + destruct (l == root). 
      - rewrite e in *. simpl in H. inversion H; subst. eexists. constructor.
      - inversion H.
    + destruct k as [[q j] r].
      destruct (l == q).
      - rewrite e0 in *. inversion H; subst. eexists. constructor.
      - edestruct IHt; eauto. exists x. constructor. eassumption.
  Qed.
  
  Lemma last_inst_in_inv :
    forall k t l i s, In k t (l, i, s) -> exists j, last_inst_of l k t = Some j.
  Proof.
    intros. dependent induction t; simpl in H.
    + destruct (l == root). 
      - rewrite e in *. simpl. exists start_tag. destruct (root == root); firstorder.
      - inv_tr H. firstorder.
    + destruct k as [[q j] r].
      destruct (l == q).
      - rewrite e0 in *. simpl. exists j. destruct (q == q); firstorder.
      - inv_tr H.
        * firstorder.
        * eapply IHt in H4. destruct H4 as [j' Hlast].
          eexists. simpl. destruct (l == q).
          ** contradiction c. 
          ** eapply Hlast.
  Qed.

  Lemma precedes_same p m s w t :
    Precedes (p, m, s) t (p, m, w) (p, m, s) -> w === s.
  Proof.
    intros H.
    eapply precedes_implies_in_pred in H.
    inv_tr H; try reflexivity. 
    exfalso. eapply ivec_fresh; eauto.
  Qed.

  Lemma in_same_state p i s s' t :
    In (p, i, s) t (p, i, s') -> s === s'.
  Proof.
    intros.
    inv_tr H; try reflexivity.
    + inv_tr H. reflexivity.
      exfalso. eapply ivec_fresh; eauto.
  Qed.

    Lemma last_inst_step_pred p j r a l u t e : 
    a =/= p -> last_inst_of a (p, j, r) (Step (p, j, r) (a, l, u) t e) = Some l.
  Proof.
    intros Hneq.
    simpl.
    destruct (a == p); firstorder. eapply last_inst_self.
  Qed.

  Lemma label_in_trace_in :
    forall l k t, label_in_trace l k t = true <-> exists i s, In k t (l, i, s).
  Proof.
    intros.
    induction t.
    - simpl. split; intros.
      + exists start_tag, s. conv_bool. rewrite H. constructor.
      + destruct H as [i [s' Hin]].
        inv_tr Hin.
        unfold equiv_decb.
        destruct (root == root); destruct (start_tag == start_tag); firstorder.
    - destruct k as [[p j] s].
      split; intros.
      + destruct (l == p).
        * rewrite e0 in *. exists j, s. constructor.
        * destruct IHt as [IHt _].
          simpl in H. conv_bool.
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
      + exists s. conv_bool. destruct H. rewrite H. rewrite H0. constructor.
      + destruct H as [s' Hin].
        inv_tr Hin.
        unfold equiv_decb.
        destruct (root == root); destruct (start_tag == start_tag); firstorder.
    - destruct k as [[p j] s].
      split; intros.
      remember (lab_tag_matches l i (p, j, s)) as eq.
      symmetry in Heqeq. simpl in Heqeq.
      + destruct eq; conv_bool.
        * destruct Heqeq. rewrite H0. rewrite H1. exists s. constructor.
        * destruct IHt as [IHt _].
          simpl in H. conv_bool.
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

  Definition lift (tr : Traces) : Hyper :=
    fun ts => ts = tr.

  Definition red_prod (h h' : Hyper) : Hyper :=
    fun ts => h ts /\ h' ts.
  
End Evaluation.
