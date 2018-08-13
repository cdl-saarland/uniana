Require Import Coq.Classes.EquivDec.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.Decidable.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Utils.
Require Import Lists.ListSet.
Require Import List.
Require Import Nat.

Require Import Util.

Module Uniana.
  Parameter Lab : Type.
  Parameter Var : Type.
  Parameter Val : Type.
  Definition Tag := list nat.

  Definition State := Var -> Val.

  Variable Lab_dec' : forall (l l' : Lab), { l = l' } + { l <> l'}.
  Variable Lab_dec : EqDec Lab eq.
  Variable Val_dec : EqDec Var eq.
  Variable Var_dec : EqDec Val eq.
  Variable Tag_dec : EqDec Tag eq.
  Variable State_dec : EqDec State eq.

  Parameter init_uni : Var -> Prop.
  Parameter start_tag : Tag.
  Parameter all_lab : set Lab.
  Parameter all_lab_spec : forall l, set_In l all_lab.

  Definition States := State -> Prop.
  Definition Coord := prod Lab Tag.
  Definition Conf := prod Coord State.

  Hint Unfold Conf Coord.

  Definition lab_of (k : Conf) :=
    match k with
      ((p, i), s) => p
    end.

  Definition UniState := Var -> bool.

  
  Parameter loop_head : Lab -> nat.
  Parameter loop_exit : Lab -> nat.
  Parameter is_back_edge : Lab -> Lab -> bool.
  
  Fixpoint iter {X : Type} (f : X -> X) (l : X) (n : nat) : X
    := match n with
       | O => l
       | S n => iter f (f l) n
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
         
  Parameter abs_uni_eff : UniState -> UniState.

  Definition uni_state_concr (uni : UniState) : State -> State -> Prop :=
    fun s => fun s' => forall x, uni x = true -> s x = s' x.

  Parameter local_uni_corr : forall uni p i q j s s' qs qs', 
      uni_state_concr uni s s' ->
      eff (p, i, s) = Some (q, j, qs) ->
      eff (p, i, s') = Some (q, j, qs') ->
      uni_state_concr (abs_uni_eff uni) qs qs'.

  Parameter is_def : Var -> Lab -> Lab -> bool.
  Parameter root : Lab.

  Parameter preds : Lab -> list Lab.
  Notation "p --> q" := (List.In p (preds q)) (at level 70, right associativity).

  Notation "p -->* q" := (p === q \/ p --> q) (at level 70, right associativity).

  Definition is_def_lab x p := exists q, is_def x q p = true.

  Lemma Conf_dec :
    forall (x y : Conf), {x = y} + {x <> y}.
  Proof.
    intros.
    destruct x as [[p i] s], y as [[q j] r].
    destruct ((p, i, s) == (q, j, r)); firstorder.
  Qed.
  Instance conf_eq_eqdec : EqDec Conf eq := Conf_dec.

  Lemma Lab_var_dec :
    forall (x y : (Lab * Var)), { x = y } + { x <> y }.
  Proof.
    intros.
    destruct x as [xa xb], y as [ya yb].
    destruct ((xa, xb) == (ya, yb)); firstorder.
  Qed.
  Program Instance lab_var_eq_eqdec : EqDec (Lab * Var) eq := Lab_var_dec.

  Definition start_coord := (root, start_tag) : Coord.

  Definition is_effect_on (p q : Lab) :=
    exists i i' s s', eff ((p, i), s) = Some ((q, i'), s').

  Parameter root_no_pred : forall p, ~ p --> root.

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

  Parameter def_edge :
    forall p q x, is_def x p q = true -> p --> q.

  (* TODO *)
  Inductive Tr : Conf -> Type :=
    | Init : forall s, Tr (root, start_tag, s)
    | Step : forall k k', Tr k' -> eff k' = Some k -> Tr k.

  Ltac inv_dep H Dec := inversion H; subst; 
                        repeat match goal with
                               | [ H0: @existT _ _ _ _ = @existT _ _ _ _  |- _ ] =>
                                 apply inj_pair2_eq_dec in H0; try (apply Dec); subst
                               end.

  Ltac inv_tr H := inversion H; subst; 
                   repeat match goal with
                          | [ H0: @existT Conf _ _ _ = @existT _ _ _ _  |- _ ] => apply inj_pair2_eq_dec in H0; try (apply Conf_dec); subst
                          end.

  Inductive Prefix : forall k, Tr k -> forall k', Tr k' -> Prop :=
  | PrefixSame : forall k t, Prefix k t k t
  | PrefixStep : forall k'' k' k step t t', Prefix k t k' t' ->
                                            Prefix k t k'' (Step k'' k' t' step).

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
  Definition Upi := Lab -> Lab -> bool.

  Inductive In : forall k, Tr k -> Conf -> Prop :=
    | In_At : forall k tr, In k tr k
    | In_Other : forall l k k' tr' step, In k' tr' l -> In k (Step k k' tr' step) l.

  Lemma tr_in_dec :
    forall k' k t, {In k t k'} + {~ In k t k'}.
  Proof.
    intros k'.
    induction t.
    - destruct (conf_eq_eqdec (start_coord, s) k').
      + left. rewrite <- e. econstructor.
      + right. intro. apply c. inv_tr H. reflexivity.
    - destruct (k == k').
      + left. rewrite <- e0. constructor.
      + inversion_clear IHt.
        * left. econstructor. eassumption.
        * right. intro. apply H. inv_tr H0; firstorder.
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
    - exfalso. eapply (ivec_fresh _ _ _ _ _ step0). 
      eauto using precedes_implies_in_succ. reflexivity.
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

  Inductive Path : Lab -> Lab -> Type :=
    | PathInit : forall p, Path p p
    | PathStep : forall from p to, Path from p -> (p --> to) -> Path from to.

  Fixpoint PathIn {a b} (q : Lab) (p : Path a b) : Prop :=
    match p with
    | PathInit v => q = v
    | PathStep from mid to p edge => (q = to) \/ PathIn q p
    end.

  Definition step_exists_path {q p} {j i} {r s} (step : eff (q, j, r) = Some (p, i, s)) :=
           (PathStep q q p (PathInit q) (step_conf_implies_edge q p j i r s step)).

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

  Lemma Path_in_dec {z a} x (p: Path a z) :
    {PathIn x p} + {~ PathIn x p}.
  Proof.
    induction p.
    + destruct (x == p); firstorder.
    + simpl in *. destruct (x == to); firstorder.
  Qed.

  Lemma path_first_in {a} b (p : Path a b) :
    PathIn a p.
  Proof.
    induction p.
    + constructor.
    + simpl. eauto.
  Qed.

  Lemma path_last_in {a} b (p : Path a b) :
    PathIn b p.
  Proof.
    induction p.
    + constructor.
    + simpl. left. reflexivity.
  Qed.

  Fixpoint acyclic {a c} (p : Path a c) : Prop :=
    match p with
    | PathInit p => True
    | PathStep a b c p' e => acyclic p' /\ ~ PathIn c p'
    end.

  Lemma path_in_single_acyclic {a} (p : Path a a) :
    acyclic p -> forall q, PathIn q p -> q = a.
  Proof.
    intros Hacyc q Hin.
    dependent induction p; simpl in Hin; [ eauto |].
    simpl in Hacyc.
    exfalso. apply Hacyc. eapply path_first_in.
  Qed.

  Lemma acyclic_prefix {a b c} (p : Path a b) (e : b --> c) :
    acyclic (PathStep a b c p e) -> acyclic p.
  Proof.
    intros.
    destruct p; simpl in *; firstorder.
  Qed.

  Parameter branch : Lab -> option (Lab * Lab * Var * Var).

  Definition is_branch br x := exists tt ff xb, branch br = Some (tt, ff, x, xb).

  Parameter val_true : Val -> bool.

  Parameter branch_spec :
    forall b, match branch b with
              | Some (t, f, x, xb) => t =/= f /\
                                      forall i s k, eff (b, i, s) = Some k ->
                                                    lab_of k = (if val_true (s x) then t else f)
              | None => forall i i' s s' k k', eff (b, i, s) = Some k ->
                                               eff (b, i', s') = Some k' ->
                                               lab_of k = lab_of k'
              end.

  Parameter branch_spec_var : 
    forall b t f x xb, branch b = Some (t, f, x, xb) -> is_def xb b t = true /\ is_def xb b f = true /\
                                                        forall b', b =/= b' -> forall p, is_def xb b' p = false.

  Parameter in_out_spec :
   forall p q q', (exists x, is_branch p x) -> q --> p -> q' --> p -> q = q'.

  Parameter no_self_loops :
    forall q p, q --> p -> q =/= p.

  Definition DisjointPaths (s : Lab) (x : Var) (t f : Lab) (a : Path s t) (b : Path s f) :=
    is_branch s x /\
    (forall p, PathIn p a -> PathIn p b -> p = s).

  Parameter splits : Lab -> list (Lab * Var).

  Parameter splits_spec : forall conv br x, (exists qt qf a b, qt -->* conv /\
                                                               qf -->* conv /\
                                                               DisjointPaths br x qt qf a b) <->
                                            List.In (br, x) (splits conv).

  Definition uni_concr (u : Uni) : Hyper :=
    fun ts => forall t t' tr tr', ts t tr -> ts t' tr' ->
                                  forall x p i s s', In t tr ((p, i), s) ->
                                                     In t' tr' ((p, i), s') ->
                                                     u p x = true -> s x = s' x.


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
  
  Definition Unch := Lab -> Var -> set Lab.

  Definition unch_concr (unch : Unch) : Traces :=
    fun k => fun t => forall to i s u x, In k t (to, i, s) ->
                              set_In u (unch to x) ->
                              exists j r, Precedes k t (u, j, r) (to, i, s) /\
                                     r x = s x.

  (*
  Definition unch_concr (unch : Unch) : Traces :=
    fun k => fun t => forall to i s u x, In k t (to, i, s) ->
                              set_In u (unch to x) ->
                              exists d dj dr j r, is_def_lab x d /\
                                             Precedes k t (d, dj, dr) (u, j, r) -> 
                                             Precedes k t (u, j, r) (to, i, s) /\
                                             r x = s x.
  *)
                           
  Definition unch_join_ptw (d d' : set Lab) := set_inter Lab_dec' d d'. 

  Definition unch_join (u u' : Unch) : Unch :=
    fun l x => unch_join_ptw (u l x) (u' l x).

  Definition unch_trans_local (unch : Unch) (q p : Lab) (x : Var) : set Lab :=
    set_add Lab_dec' p (if is_def x q p then empty_set Lab else unch q x).

  Definition unch_trans_ptw (unch : Unch) l x : set Lab :=
    if Lab_dec' l root then set_add Lab_dec' root (empty_set Lab) else
    let f := fun q acc => set_inter Lab_dec' q acc in
    let t := fun q => unch_trans_local unch q l x in
    fold_right f all_lab (map t (preds l)).
      
  Definition unch_trans (unch : Unch) : Unch :=
    fun l x => unch_trans_ptw unch l x.

  Lemma unch_trans_root : forall unch x, unch_trans unch root x = set_add Lab_dec' root (empty_set Lab).
  Proof.
    intros.
    cut (preds root = nil); intros.
    + unfold unch_trans, unch_trans_ptw.
      destruct (Lab_dec' root root); firstorder.
    + cut (forall q, ~ List.In q (preds root)); intros; eauto using list_emp_in, root_no_pred. 
  Qed.

  Inductive Front (u : Unch) : Var -> Lab -> Prop :=
    | FrontDef : forall x p, is_def_lab x p -> Front u x p
    | FrontIter : forall x l l' r r' p, l <> r ->
                                   Front u x l ->
                                   Front u x r ->
                                   l' --> p ->
                                   r' --> p ->
                                   set_In l (u l' x) ->
                                   set_In r (u r' x) ->
                                   ~ set_In l (u r' x) ->
                                   ~ set_In r (u l' x) ->
                                   Front u x p.

  Definition DisjPaths {a b c d} (π : Path a b) (π' : Path c d) :=
    forall p, (PathIn p π -> ~ PathIn p π') /\ (PathIn p π' -> ~ PathIn p π).

  (*
  Lemma unch_dom (u : Unch) x l l' :
    set_In l (u l' x) -> forall q, is_def_lab x q -> forall (π : Path q l'), PathIn l π.
  Proof.
  Admitted.

  Lemma unch_path_exist (u : Unch) x l l' r :
    set_In l (u l' x) -> ~ set_In r (u l' x) -> exists (π : Path l l'), ~ PathIn r π.
  Proof.
  Admitted.
    
  Lemma front_and_join (u : Unch) x p :
    Front u x p <-> is_def_lab x p \/ exists d d' q q' (π : Path d q) (π' : Path d' q'), is_def_lab x d /\
                                                                                 is_def_lab x d' /\
                                                                                 q --> p /\ q' --> p /\
                                                                                 DisjPaths π π'.
  Proof.
    split; intros.
    - induction H; [ left; assumption | right ].
      eapply unch_path_exist in H6; try eassumption.
      eapply unch_path_exist in H7; try eassumption.
      destruct H6 as [π Hπ], H7 as [π' Hπ'].
      specialize (unch_dom _ _ _ _ H4). intro Hdom.
      specialize (unch_dom _ _ _ _ H5). intro Hdom'.
      assert (Hdom := unch_dom _ _ _ _).
      assert (DisjPaths π π'). {
        unfold DisjPaths.
        intros q.
        split; intros.
        - 

      destruct IHFront1, IHFront2.
      + exists l, r, l', r', π, π'.
        do 4 (split; [ assumption |]).
        unfold DisjPaths.
        admit.
      + 

      assert  
      (*
      destruct IHFront1, IHFront2.
      + exists l, r, l', r'.
        eexists. eexists. 
        do 4 (split; [ assumption |]).
        admit.
      +
       *)
      admit.
    - admit.
                           
  *)

  (* Paths *)

  Lemma path_exists_pred {a b} (p : Path a b) :
    a <> b -> exists q (p' : Path a q) (e : q --> b),  p = (PathStep a q b p' e).
  Proof.
    intros.
    induction p; [ firstorder |].
    destruct (from == p).
    - rewrite e in *. eauto.
    - eapply IHp in c. eauto. 
  Qed.

  Lemma path_acyclic_pred {a q} (p : Path a q) b e :
    acyclic (PathStep a q b p e) -> acyclic p.
  Proof.
    intros.
    dependent induction p; simpl in *; firstorder.
  Qed.

  Lemma path_acyclic_next {a q p} (π : Path a q) (edge : q --> p) :
        acyclic π -> acyclic (PathStep a q p π edge) \/ exists (π' : Path a p), acyclic π' /\ forall q, PathIn q π' -> PathIn q π.
  Proof.
    intros.
    simpl.
    destruct (Path_in_dec p π).
    - right.
      clear edge.
      induction π.
      + inject p0. exists (PathInit p1). simpl. eauto.
      + inject p0.
        * exists (PathStep from p1 to π i). split; try eauto.
        * eapply path_acyclic_pred in H. destruct (IHπ H H0) as [π' [Hacyc Hin]].
          exists π'. split; [ assumption |]. intros. simpl. eauto.
    - left. eauto.
  Qed.
  
  Fixpoint path_concat {a b c} (π : Path a b) (π' : Path b c) : Path a c.
    refine ((match π' as y in (Path b' c) return
                  (b' = b -> Path a c) with
    | PathInit _ => _
    | PathStep b c c' π' e => _
    end) (eq_refl b)); intros; subst.
    - apply π.
    - eapply (PathStep _ _ _ (path_concat _ _ _ π π') e).
  Defined.
  
  Lemma concat_in1 {a b c} (π : Path a b) (π' : Path b c) :
    forall q, PathIn q π -> PathIn q (path_concat π π').
  Proof.
    intros. induction π'; simpl; eauto.
  Qed.

  Lemma path_pred {a b} (p : Path a b) :
    a = b \/ exists pred, pred --> b.
  Proof.
    induction p; eauto.
  Qed.

  Lemma path_nodes_neq {a b} (p : Path a b) r s :
    PathIn r p ->
    ~ PathIn s p ->
    r <> s.
  Proof.
    intros Hin Hnin.
    induction p.
    - inject Hin. intro. apply Hnin. subst. constructor.
    - intro. subst. apply Hnin. assumption.
  Qed.

  (*
  Definition disjoint {a b c d} (p : Path a b) (p' : Path c d) :=
    (forall q, PathIn q p -> ~ PathIn q p') /\ (forall q, PathIn q p' -> ~ PathIn q p).
  *)

  Definition deciabable_PathIn a b (p : Path a b) q :
    decidable (PathIn q p).
  Proof.
    unfold decidable.
    induction p.
    + simpl. destruct (q == p); firstorder.
    + simpl. destruct IHp; firstorder.
      destruct (q == to); firstorder.
  Qed.

  (*
  Section Disj.
    Variable unch : Unch.
    Variable s t f : Lab.
    Variable x xs : Var.
    Variable Hst : s --> t.
    Variable Hsf : s --> f.
    Variable Hbr : branch s = Some (t, f, x, xs).
    Variable Hfp : unch_lfp unch.

    Lemma unch_split_is_on_path dl to (p : Path f to) :
      unch to xs = Some dl ->
      PathIn dl p.
    Proof.
      intros Hunch.
      induction p.
      - rename p into f. simpl.
        assert (Hbrspec := branch_spec_var s t f x xs Hbr).
        destruct Hbrspec as [Hl [Hr _]].
        destruct (unch_trans_res unch s f xs Hsf).
        + rewrite unch_lfp_trans_eq in H; try eassumption.
          rewrite Hunch in H. inject H. reflexivity.
        + destruct H as [_ [H _]].  rewrite H in *; firstorder.
      - rename from into f. rename p into q. simpl.
        destruct (unch_trans_res unch q to xs e).
        + rewrite unch_lfp_trans_eq in H; try eassumption.
          rewrite Hunch in H. inject H. left. reflexivity.
        + destruct H as [_ [_ [_ H]]].
          rewrite unch_lfp_trans_eq in H; try eassumption.
          rewrite H in Hunch. right. eauto.
    Qed.
    
    Lemma unch_split_exists {to} (p : Path f to) :
      exists dl, unch to xs = Some dl /\ PathIn dl p.
    Proof.
      induction p.
      - rename p into f. simpl.
        assert (Hbrspec := branch_spec_var s t f x xs Hbr).
        destruct Hbrspec as [Hl [Hr _]].
        destruct (unch_trans_res unch s f xs Hsf).
        + rewrite unch_lfp_trans_eq in H; try eassumption.
          exists f. split; [ eauto | reflexivity ].
        + destruct H as [_ [H _]]. rewrite H in *; firstorder.
      - rename from into f. rename p into q. simpl.
        destruct (unch_trans_res unch q to xs e).
        + rewrite unch_lfp_trans_eq in H; try eassumption.
          exists to. split; eauto. 
        + destruct H as [_ [_ [_ H]]].
          rewrite unch_lfp_trans_eq in H; try eassumption.
          destruct IHp as [dl [IHp Hin]]; try eassumption. rewrite IHp in H.
          exists dl. eauto. 
    Qed.

    Variable l r : Lab.

    Section PathsGiven.
      Variable a : Path t l.
      Variable b : Path f r.
  
      Lemma unch_disj_l :
        disjoint a b ->
        exists dl dr, unch l xs = Some dl /\ unch r xs = Some dr /\ dl =/= dr.
      Proof.
        intros Hdis.
        unfold disjoint in Hdis.
        destruct Hdis as [Hl Hr].
        induction a as [t | t].
        - destruct (branch_spec_var s t f x xs Hbr) as [Hdef _].
          destruct (unch_trans_res unch s t xs Hst); rewrite unch_lfp_trans_eq in H; try eassumption.
          + destruct (unch_split_exists b) as [dr [Hu Hp]].
            exists t, dr. repeat split; try eassumption.
            intro. eapply Hl. constructor. rewrite H0. assumption.
          + destruct H as [_ [H _]]. rewrite Hdef in H. firstorder.
        - rename p0 into b', p into l.
          destruct IHp; try eassumption.
          + intros. apply Hl. simpl. auto.
          + intros. apply Hr in H. contradict H. simpl. auto.
          + destruct H as [dr [Hul [Hur Hneq]]].
            destruct (unch_trans_res unch l to xs e); rewrite unch_lfp_trans_eq in H; try eassumption.
            * exists to, dr. repeat split; eauto. 
              intro. eapply (Hl to). simpl. left. reflexivity. eapply unch_split_is_on_path. auto.
              rewrite H0. eassumption.
            * destruct H as [_ [_ [_ H]]].
              rewrite H. eauto.
      Qed.

*)
  
  Definition join_andb (l : list bool) := fold_right andb true l.

  Lemma join_andb_true_iff {A : Type} : 
    forall f (l : list A), (join_andb (map f l) = true) -> (forall x, List.In x l -> f x = true).
  Proof.
    intros.
    unfold join_andb in H.
    induction l; inversion H0; simpl in H; apply andb_true_iff in H; try subst; destruct H; auto.
  Qed.

  Definition join_orb (l : list bool) := fold_right orb false l.

  Lemma join_orb_true_iff {A : Type} :
    forall f (l : list A), (join_orb (map f l) = true) -> (exists x, List.In x l /\ f x = true).
  Proof.
    intros.
    unfold join_orb in H.
    induction l; simpl in H.
    - inversion H.
    - conv_bool.
      inject H.
      * exists a. simpl. eauto.
      * eapply IHl in H0. destruct H0 as [x [Hin Hf]].
        exists x. simpl. eauto.
  Qed.

  Definition uni_trans (uni : Uni) (upi : Upi) (unch : Unch) : Uni :=
    fun p => if p == root then uni root
             else fun x => ((join_andb (map (fun spl => 
                                           match spl with (s, x) => uni s x &&
                                                upi_trans upi uni s p end) (splits p))) 
                              && (join_andb (map (fun q => abs_uni_eff (uni q) x) (preds p)))
                              && (join_andb (map (fun q => upi_trans upi uni q p) (preds p)))
                           )
                        || join_orb (map (fun q => (q <>b p) && uni q x && upi_trans upi uni q p) (unch_trans unch p x)).

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

  Lemma unch_trans_lem u to x unch :
    set_In u (unch_trans unch to x) ->
    u = to \/ (forall q, List.In q (preds to) -> (is_def x q to = false /\ set_In u (unch q x))).
  Proof.
    intros.
    unfold unch_trans, unch_trans_ptw, unch_join_ptw, unch_trans_local in H.
    induction (preds to); simpl in *.
    - right. intros. inject H0.
    - destruct (Lab_dec' to root).
      + simpl in H. destruct H; [ subst | firstorder ]. eauto.
      + eapply set_inter_elim in H.
        destruct H as [Hin Hother].
        eapply IHl in Hother. clear IHl.
        inject Hother; [ eauto |].
        destruct (Lab_dec' u to); subst; eauto.
        right.
        intros.
        inject H0; [ subst | eauto].
        destruct (is_def x q to).
        * simpl in Hin. firstorder.
        * eauto using set_add_elim2.
  Qed.

  Lemma unch_correct :
    forall unch k t,
      sem_trace (unch_concr unch) k t -> unch_concr (unch_trans unch) k t.
  Proof.
    intros unch k t Hred.
    unfold sem_trace in Hred.
    destruct Hred as [k' [t' [step [Hconcr H]]]]; subst.
    unfold unch_concr in *.
    intros to i s u x.
    intros Hin Hunch.
    destruct (Lab_dec' to root); subst.
    - unfold unch_trans, unch_trans_ptw in Hunch. destruct (Lab_dec' root root); [ | firstorder ].
      simpl in Hunch. destruct Hunch; [ | firstorder ]. subst.
      exists i, s. eauto using precedes_self.
    - assert (Hpred := Hin).
      eapply in_exists_pred in Hpred; try eassumption.
      destruct Hpred as [q [j [r [Hpredin Hpred]]]].
      assert (Hedge: q --> to) by (eauto using step_conf_implies_edge).
      eapply unch_trans_lem in Hunch; try eassumption.
      destruct (Lab_dec' to u) as [ | Hneq ]; subst.
      + exists i, s. split; [ | reflexivity ].  eauto using precedes_self.
      + destruct Hunch; [ firstorder |].
        eapply H in Hedge. destruct Hedge as [Hndef Huin].
        edestruct Hconcr as [j' [r' [Hprec Heq]]]; eauto.
        exists j', r'. rewrite Heq. eauto using precedes_succ, no_def_untouched.

        split.
        * eauto using precedes_succ. admit.
        * rewrite Heq. eauto using no_def_untouched.

    intros Hin Hunch Hdef.
    destruct (to == root).
    - rewrite e in *; clear e.
      exists i, s.
      split; [| reflexivity ].
      rewrite unch_trans_root in Hunch. inversion Hunch. 
    - assert (Hpred := Hin).
      eapply in_exists_pred in Hpred; eauto.
      destruct Hpred as [q [j [r [Hpredin Hpred]]]].
      assert (Hedge: q --> to) by (eauto using step_conf_implies_edge).
      eapply unch_trans_lem in Hunch.
      destruct (Lab_dec' to u) as [ Heq | Hneq ]; subst.
      + exists i, s. split; [ | reflexivity ]. eapply precedes_self. assumption.
      + inject Hunch; [ firstorder |].
        eapply H in Hedge. destruct Hedge as [Hndef Huin].
        edestruct Hconcr as [j' [r' [Hprec Heq]]]; eauto.
        exists j', r'. split.
        * eauto using precedes_succ.
        * rewrite Heq. eauto using no_def_untouched.
  Qed.
  *)

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

  Lemma last_inst_upi_prop {p br m m' w w' q q' i j j' s s' r r' step step' t t'} :
    let tr := (Step (p, i, s) (q, j, r) t step) in
    let tr' := (Step (p, i, s') (q', j', r') t' step') in
    upi_prop br p (p, i, s) (p, i, s') tr tr' ->
    In (q, j, r) t (br, m, w) ->
    In (q', j', r') t' (br, m', w') ->
    p =/= br ->
    last_inst_of br (q, j, r) t = last_inst_of br (q', j', r') t'.
  Proof.
    simpl. intros Hupi Hin Hin' Hneq.
    eapply last_inst_in_inv in Hin.
    eapply last_inst_in_inv in Hin'.
    destruct Hin as [k Hlast].
    destruct Hin' as [k' Hlast'].
    rewrite Hlast. rewrite Hlast'.
    unfold upi_prop in Hupi.
    eapply last_inst_precedes in Hlast. destruct Hlast as [u Hprec]. 
    eapply last_inst_precedes in Hlast'. destruct Hlast' as [u' Hprec']. 
    symmetry. f_equal. eauto using Precedes.
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
  
  Definition DivergenceWitness br x xb k k' t t' := 
    (exists l u u', val_true (u x) =/= val_true (u' x) /\
                    In k t (br, l, u) /\
                    In k' t' (br, l, u') /\
                    exists tt ff, branch br = Some (tt, ff, x, xb)).

  Lemma different_tgt_is_branch {br : Lab} {i : Tag} {s s' : State} {k k' : Conf} :
    eff (br, i, s) = Some k ->
    eff (br, i, s') = Some k' ->
    lab_of k =/= lab_of k' ->
    exists x, val_true (s x) =/= val_true (s' x) /\ is_branch br x.
  Proof.
    intros Hstep Hstep' Hneq.
    assert (Hspec := branch_spec br).
    destruct (branch br) as [ [[[tt ff] x] xb] | ] eqn:Hbr.
    + destruct Hspec as [Hneqtf Hspec].
      assert (Hspec' := Hspec i s' k' Hstep').
      specialize (Hspec i s k Hstep).
      destruct k as [[q j] r], k' as [[q' j'] r']. simpl in *.
      exists x. split.
      - destruct (val_true (s x)) eqn:Hv, (val_true (s' x)) eqn:Hv';
          subst; firstorder.
      - unfold is_branch. firstorder.
    + specialize (Hspec i i s s' k k' Hstep Hstep'). firstorder.
  Qed.

  Lemma single_edge_disjoint_path (q a q' : Lab) x (p : Path a q') :
    is_branch a x ->
    ~ PathIn q p ->
    a --> q -> 
    exists p', DisjointPaths a x q' q p p'.
  Proof.
    intros Hbr Hnin Hedge.
    exists (PathStep a a q (PathInit a) Hedge).
    unfold DisjointPaths.
    split. assumption.
    intros p' H H'.
    simpl in H'.
    inversion_clear H'.
    rewrite H0 in *. clear H0. contradiction H. eauto.
  Qed.

  Lemma single_edge_disjoint_path_detail (q a q' : Lab) l u j r x
        (step : eff (a, l, u) = Some (q, j, r)) (p : Path a q') :
    is_branch a x ->
    ~ PathIn q p ->
    DisjointPaths a x q' q p (step_exists_path step).
  Proof.
    simpl.
    intros Hbr Hnin.
    unfold DisjointPaths.
    split; try assumption.
    intros p' H H'.
    simpl in H'.
    inversion_clear H'; [| eauto].
    rewrite H0 in *. contradiction H. 
  Qed.

  Lemma contains_label_tag_disjoint p q q' i j j' s s' r r' t t' : 
    label_tag_in_trace q j (q', j', r') t' = true ->
    eff (q, j, r) = Some (p, i, s) ->
    eff (q', j', r') = Some (p, i, s') ->
    q =/= q' \/ j =/= j' ->
    exists x xb, (exists a b, DisjointPaths q x q q' a b) /\
            DivergenceWitness q x xb (q, j, r) (q', j', r') t t'.
  Proof.
    intros Hintr Hstep Hstep' Hneq.
    apply label_tag_in_trace_in in Hintr.
    destruct Hintr as [u Hinq].
    + assert (Hnext := Hinq).
      apply in_succ_exists in Hnext.
      destruct Hnext as [[k' [Hnext Hin]] | H]; [| injection H; intros; subst; firstorder ].
      destruct k' as [[b m] w].
      enough (b =/= p).
      * specialize (different_tgt_is_branch Hnext Hstep H) as Hbr.
        destruct Hbr as [x [Hneqx Hbr]].
        unfold is_branch in Hbr.
        destruct Hbr as [tt [ff [xb Hbr]]]. exists x, xb.
        split; simpl.
        - unfold DisjointPaths.
          exists (PathInit q). eexists (proj1_sig (path_for_trace _ _ _ Hinq)).
          split; [ firstorder |].
          intros p' Paq' Paa. simpl in Paa. eauto.
        - exists j, r, u. symmetry in Hneqx. unfold is_branch in Hbr.
          repeat split; try eauto; try constructor.
      * intro. rewrite H in *. clear H. eapply ivec_fresh.
        apply Hstep'. apply Hin. eauto using ivec_det.
  Qed.

  Lemma last_instance p q q' i j j' s' r' t' :
    eff (q', j', r') = Some (p, i, s') -> 
    label_tag_in_trace q j (q', j', r') t' = false ->
    forall j'', last_inst_of q (q', j', r') t' = Some j'' ->
                j <> j''.
  Proof.
    intros Hstep' Hqq' j'' Hinst.
    eapply not_label_tag_in_trace_in in Hqq'. intro. subst j''. eapply Hqq'.
    eauto using last_inst_in.
  Qed.

  Lemma not_contains_label_tag_last_common p q q' i j j' s' r r' t t' :
    eff (q', j', r') = Some (p, i, s') -> 
    label_tag_in_trace q j (q', j', r') t' = false ->
    label_tag_in_trace q' j' (q, j, r) t = false ->
    (exists br x xb, (exists m w Hinbr Pbrq, 
                      let Pbrq' := proj1_sig (path_for_trace (q', j', r') t' (br, m, w) Hinbr) in
                      DisjointPaths br x q' q Pbrq' Pbrq) /\
                  (exists m w, In (q, j, r) t (br, m, w)) /\ 
                  (last_inst_of br (q', j', r') t' = last_inst_of br (q, j, r) t ->
                   DivergenceWitness br x xb (q', j', r') (q, j, r) t' t)) \/
    (exists j'', j <> j'' /\ last_inst_of q (q', j', r') t' = Some j'') \/
    (exists j'', j' <> j'' /\ last_inst_of q' (q, j, r) t = Some j'').
  Proof.
    intros Hstep' Hqq' Hq'q.
    dependent induction t.
    - apply not_label_tag_in_trace_in in Hqq'.
      exfalso. apply Hqq'.
      clear Hqq' Hq'q Hstep'.
      induction t'.
      + exists s; eauto using In. 
      + destruct IHt'; eauto using In.
    - destruct k' as [[a l] u].
      simpl in Hq'q. conv_bool. destruct Hq'q as [Hnj Hnq].
      destruct (label_tag_in_trace a l (q', j', r') t') eqn:Hal.
      + clear IHt.

        (* show that q',j' cannot be the branch *)
        apply not_label_tag_in_trace_in in Hnq.
        assert (Haq: (a, l) =/= (q', j')). {
          intro. apply Hnq. injection H; intros; subst. exists u. constructor.
        }
        
        (* show that a,l has a successor that is on the q',j' trace *)
        apply label_tag_in_trace_in in Hal. destruct Hal as [u' Hain].
        assert (Hain' := Hain).
        eapply in_succ_exists in Hain'.
        inversion_clear Hain'.
        -- destruct H as [[[b m] w] [step Hxin]].
           enough (q =/= b).
           ++ destruct (last_inst_of q (q', j', r') t') as [j''|] eqn:Hinst;
                [ right; eauto using last_instance |].
              assert (Hdiff := different_tgt_is_branch e step H).
              destruct Hdiff as [x [Hneqx Hbr]]. unfold is_branch in Hbr.
              destruct Hbr as [tt [ff [xb Hbr]]].
              left. eapply last_inst_not_exists in Hinst. exists a, x, xb. split.
              ** exists l, u', Hain.
                 eapply (not_in_trace_exists_path _ _ _ _ Hain) in Hinst. 
                 assert (Hbr' : is_branch a x) by (firstorder).
                 eauto 30 using single_edge_disjoint_path, step_conf_implies_edge. 
              ** split.
                 --- exists l, u. eauto using In.
                 --- unfold DivergenceWitness.
                     simpl in Hbr. exists l, u', u. symmetry in Hneqx.
                     repeat split; eauto; try repeat constructor.
           ++ intro. rewrite H in *. clear H.
              replace m with j in * by (eauto using ivec_det).
              apply not_label_tag_in_trace_in in Hqq'. apply Hqq'; eauto.
        -- injection H; intros; subst. exfalso. apply Hnq. exists u. constructor.
      + destruct (last_inst_of q (q', j', r') t') as [l''|] eqn:Hinst;
          [ right; eauto using last_instance |].
        eapply last_inst_not_exists in Hinst.
        edestruct IHt; eauto; clear IHt.
        * left. destruct H as [br [x [xb [Hdisj [Hinbr' Hwit]]]]].
          exists br, x, xb. split.
          ** clear Hwit.
             destruct Hdisj as [m [w [Hinbr [Pbra [Hbr Hdisj]]]]].
             exists m, w, Hinbr. eapply step_conf_implies_edge in e.
             eexists (PathStep br a q Pbra e).
             split; [ eassumption |].
             intros p'. intros Pbrq'1. intros Pbrq1. eapply Hdisj; eauto.
             destruct Pbrq1; try eassumption.
             exfalso. rewrite H in *. clear H.
             eapply (not_in_trace_exists_path _ _ _ _ Hinbr) in Hinst. simpl in *. eauto.
          ** split.
             *** destruct Hinbr' as [l' [u' Hinbr']].
                 exists l', u'. eauto using In.
             *** clear Hdisj. intros Hlast.
                 simpl in Hlast.
                 destruct (br == q).
                 ++ rewrite <- e0 in *. clear e0. conv_bool.
                    exfalso. eapply not_label_tag_in_trace_in. eapply Hqq'. eapply last_inst_in.
                    eassumption.
                 ++ replace (br ==b q) with false in Hlast
                     by (symmetry; apply beq_false; eassumption).
                    specialize (Hwit Hlast). clear Hlast.
                    destruct Hwit as [m [w [w' [Hneq [Hin [Hin' Hbr]]]]]].
                    unfold DivergenceWitness.
                    exists m, w, w'.
                    repeat split; try repeat constructor; eauto.
        * destruct H as [[l' [Hlneq Hlast]] | [j'' [Hjneq Hlast]]].
          eapply last_inst_in in Hlast. destruct Hlast as [u' Hlast].
          destruct (branch a) as [[[[tt ff] x] xb] | ] eqn:Hbr.
          ++ left. exists a, x, xb. split.
             ** exists l', u', Hlast.
                eapply (not_in_trace_exists_path _ _ _ _ Hlast) in Hinst. simpl in *.
                assert (Hbr': is_branch a x) by (unfold is_branch; eauto).
                eauto using single_edge_disjoint_path, step_conf_implies_edge.
             ** split.
                *** exists l, u. eauto using In.
                *** intros. unfold DivergenceWitness. simpl in H.
                    exfalso. 
                    destruct (a == q).
                    -- rewrite <- e0 in *. clear e0.
                       eapply not_label_tag_in_trace_in. eapply Hqq'. 
                       eauto using last_inst_in. 
                    -- rewrite last_inst_self in H.
                       eapply not_label_tag_in_trace_in. eapply Hal. eauto using last_inst_in.
          ++ assert (Hbrspec := branch_spec a). rewrite Hbr in Hbrspec.
             eapply in_succ_exists in Hlast.
             inversion_clear Hlast.
             ** destruct H as [[[b m] w] [Hnext' Hin']].
                specialize (Hbrspec l l' u u' _ _ e Hnext').
                simpl in Hbrspec. subst b. exfalso. apply Hinst.
                exists m, w; assumption.
             ** injection H; intros; subst; clear H.
                specialize (Hbrspec l l' _ _ _ _ e Hstep'). simpl in Hbrspec. subst q.
                right. right. exists l. split; [ firstorder |]. eapply last_inst_step_pred.
                intro. apply Hinst. rewrite <- H in *. exists l', u'. constructor.
          ++ right. right. exists j''. split; [ firstorder |]. simpl.
             destruct (q' == q); try eassumption.
             rewrite <- e0 in *. exfalso. apply Hinst. exists j', r'. constructor.
  Qed.

  Lemma disjoint_contains p q q' i j j' s s' r r' t t' :
    label_tag_in_trace q j (q', j', r') t' = true ->
    eff (q, j, r) = Some (p, i, s) ->
    eff (q', j', r') = Some (p, i, s') ->
    q =/= q' ->
    exists br x xb, DivergenceWitness br x xb (q, j, r) (q', j', r') t t' /\ List.In (br, x) (splits p).
                 
  Proof.
    intros Hcont Hstep Hstep' Hneq.
    edestruct contains_label_tag_disjoint as [x [xb [Hdis Hwit]]]; eauto.
    destruct Hdis as [a [b [Hbr Hdis]]].
    exists q, x, xb. split; eauto.
    eapply splits_spec. 
    exists q, q'. eexists. eexists.
    repeat split; eauto using step_conf_implies_edge.
  Qed.

  Lemma witness_commutative br x xb q q' j j' r r' t t' :
    DivergenceWitness br x xb (q, j, r) (q', j', r') t t' <->
    DivergenceWitness br x xb (q', j', r') (q, j, r) t' t.
  Proof.
    unfold DivergenceWitness.
    split; intros; destruct H as [l [u [u' [Hneq [Hin [Hin' Hbr]]]]]]; exists l, u', u; firstorder.
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
      - inversion H; subst.
        cut (step = step'); intros; subst; try eassumption.
        clear Hprec H. destruct step'. admit.
      - rewrite <- step. eassumption.
    + constructor. eapply IHHprefix. eassumption.
  Admitted.

  Lemma upi_prefix {b p i s s' q j r q' j' r' k k' kp kp' pstep pstep' t t' tr tr'}
        (step : eff (q, j, r) = Some (p, i, s)) 
        (step' : eff (q', j', r') = Some (p, i, s')) :
    Prefix (q, j, r) tr kp t ->
    Prefix (q', j', r') tr' kp' t' ->
    upi_prop b p k k' (Step k kp t pstep) (Step k' kp' t' pstep') ->
    upi_prop b p (p, i, s) (p, i, s') (Step (p, i, s) (q, j, r) tr step)
             (Step (p, i, s') (q', j', r') tr' step').
  Proof.
    intros Hupi Hprefix Hprefix'.
    repeat split; try assumption; unfold upi_prop in *; intros; eauto using precedes_prefix_inv.
  Qed.

  Lemma upi_comm q p k k' t t' :
    upi_prop q p k k' t t' ->
    upi_prop q p k' k t' t.
  Proof.
    unfold upi_prop in *. intros. symmetry. eauto.
  Qed.  

  Lemma disjoint p q q' i j j' s s' r r' l l' k k' tr tr' step step'
        (Hstep : eff (q, j, r) = Some (p, i, s))
        (Hstep' : eff (q', j', r') = Some (p, i, s')) :
    let ltr := (Step l k tr step) in
    let ltr' := (Step l' k' tr' step') in 
    In k tr (q, j, r) ->
    In k' tr' (q', j', r') ->
    upi_prop q p l l' ltr ltr' ->
    upi_prop q' p l l' ltr ltr' ->
    (forall spl x, List.In (spl, x) (splits p) -> upi_prop spl p l l' ltr ltr') ->
    q' =/= q ->
    exists br x xb, DivergenceWitness br x xb k' k tr' tr /\
               List.In (br, x) (splits p).
  Proof.
    simpl.
    intros Hpref Hpref' Hupi Hupi' Hspl Hneq.
    eapply in_prefix in Hpref.
    eapply in_prefix in Hpref'.
    destruct Hpref as [t [Hpref Hqin]].
    destruct Hpref' as [t' [Hpref' Hqin']].
    eapply (upi_prefix Hstep Hstep') in Hupi; try eassumption.
    eapply upi_comm in Hupi'.
    eapply (upi_prefix Hstep' Hstep) in Hupi'; try eassumption.
    eapply upi_comm in Hupi'.

    cut (exists br x xb, DivergenceWitness br x xb (q', j', r') (q, j, r) t' t /\
                    List.In (br, x) (splits p)); intros.
    destruct H as [br [x [xb [Hwit Hinbr]]]].
    unfold DivergenceWitness in *.
    destruct Hwit as [m [u [u' [Hneqv [Hin [Hin' Hbr]]]]]].
    exists br, x, xb. split; [|eassumption].
    exists m, u, u'. repeat split; eauto using in_prefix_in.

    destruct (label_tag_in_trace q j (q', j', r') t') eqn:Hin,
             (label_tag_in_trace q' j' (q, j, r) t) eqn:Hin';
      eauto using disjoint_contains.
    + symmetry in Hneq. edestruct disjoint_contains as [br [x [xb Hcont]]]; eauto. 
      exists br, x, xb. rewrite witness_commutative. eauto.
    + edestruct not_contains_label_tag_last_common; eauto.
      - destruct H as [br [x [xb [Hdis [Hinbr Hwit]]]]].
        destruct Hinbr as [m' [w' Hinbr]].
        clear Hupi Hupi'. exists br, x, xb.
        destruct Hdis as [m [w [Hinbr' [Pbrq [Hbr Hdis]]]]]. 
        assert (List.In (br, x) (splits p)). {
          eapply (splits_spec).
          exists q', q. eexists. exists Pbrq.
          repeat split; eauto using step_conf_implies_edge. 
        }
        specialize (Hspl _ _ H).
        split; [ | assumption].
        eapply (upi_prefix Hstep Hstep' Hpref Hpref') in Hspl.
        eapply Hwit. symmetry. eapply last_inst_upi_prop; try eassumption.
        destruct (p == br); try eassumption.
        rewrite <- e in *. clear e. exfalso. eapply Hneq.
        eapply in_out_spec; eauto using step_conf_implies_edge.
      - clear Hspl.
        assert (p =/= q /\ p =/= q'). {
          split; symmetry; eauto using step_conf_implies_edge, no_self_loops.
        }
        destruct H0 as [Hnqp Hnqp'].
        exfalso.
        destruct H as [[j'' [Hneq'' Hin'']] | [j'' [Hneq'' Hin'']]].
        * eapply last_inst_precedes in Hin''.
          destruct Hin'' as [s'' Hin''].
          eapply Hneq''. symmetry. eapply Hupi.
          ++ repeat constructor. eassumption.
          ++ eauto using Precedes.
        * eapply last_inst_precedes in Hin''.
          destruct Hin'' as [s'' Hin''].
          eapply Hneq''. eapply Hupi'.
          ++ eauto using Precedes.
          ++ repeat constructor. eassumption.
  Qed.

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

    assert (upi_concr (upi_trans upi uni) t) as HCupi. {
      apply upi_correct. 
      destruct Hconcr as [[_ Hhom] _].
      exists ts; auto.
    }

    assert (unch_concr (unch_trans unch) k tr) as HCunch. {
      destruct Hconcr as [[_ _] Hunch].
      unfold lift in *; subst.
      apply unch_correct. assumption.
    } 
    
    assert (unch_concr (unch_trans unch) k' tr') as HCunch'. {
      destruct Hconcr as [[_ _] Hunch].
      unfold lift in *; subst.
      apply unch_correct. assumption.
    }

    destruct Hconcr as [[HCuni HCupi'] _].

    subst.
    unfold uni_trans in Htrans. 
    assert (X := Hsem). destruct X as [l [ltr [lstep [Hts Hlstep]]]]; subst.
    assert (X := Hsem'). destruct X as [l' [ltr' [lstep' [Hts' Hlstep']]]]; subst.

    destruct (p == root); [ subst | ].
    + rewrite e in *; clear e.
      inv_tr HIn.
      - exfalso. eauto using start_no_tgt. 
      - inv_tr HIn'; [ exfalso |]; eauto using start_no_tgt. 

    + conv_bool.
      destruct Htrans as [Htrans | Hunch].
        (* The uni/hom case *)
      - destruct Htrans as [[Hsplit Hpred] Hupi].
        eapply in_pred_exists in HIn; try eassumption.
        eapply in_pred_exists in HIn'; try eassumption.
        destruct HIn as [q [j [r [HIn Hstep]]]].
        destruct HIn' as [q' [j' [r' [HIn' Hstep']]]].
        assert (List.In q (preds p)) as Hqpred by (eauto using step_conf_implies_edge).

        cut (q' = q); intros; subst.
        * cut (j' = j); intros; subst.
          -- eapply (local_uni_corr (uni q) q j p i r r' s s'); try eassumption.
             ** unfold uni_state_concr. intros.
                unfold uni_concr in HCuni .
                eapply (HCuni l l' ltr ltr' Hts Hts' x0 q j); eassumption.
             ** eapply join_andb_true_iff in Hpred; try eassumption.
          -- (* unique preceding instances *)
             eapply join_andb_true_iff in Hupi; try eassumption.
             assert (p =/= q) by (symmetry; eauto using step_conf_implies_edge, no_self_loops).
             eapply HCupi; [ eapply Hsem | eapply Hsem' | eassumption | | ].
             all: eauto using precedes_step.
        * (* disjoint paths! *)
          destruct (q == q') as [ Heq | Hneq ]; [ eauto | exfalso ].
          assert (List.In q' (preds p)) as Hqpred' by (eauto using step_conf_implies_edge).
          unfold upi_concr in HCupi.
          eapply (join_andb_true_iff _ _ Hupi) in Hqpred'.
          eapply (join_andb_true_iff _ _ Hupi) in Hqpred.
          symmetry in Hneq.
          eapply disjoint with (q := q) (step := lstep) in Hneq; eauto.
          ++ destruct Hneq as [br [y [yb [Hwit Hspl]]]].
             destruct Hwit as [m [u' [u [Hney [Hinbr' [Hinbr _]]]]]].
             eapply join_andb_true_iff in Hsplit; try eapply Hspl. simpl in Hsplit. conv_bool.
             destruct Hsplit as [Hsplit _].
             apply Hney.
             cut (u' y = u y); intros. rewrite H. reflexivity.
             eapply HCuni; [ exact Hts' | exact Hts | | | ]; eauto.
          ++ intros.
             eapply HCupi; eauto.
             eapply (join_andb_true_iff _ _ Hsplit) in H.
             conv_bool. destruct H as [_ H]. eassumption.
        (* The unch case *)
      - rename Hunch into H.
        eapply join_orb_true_iff in H.
        destruct H as [u H].
        conv_bool.
        destruct H as [Hunch [[Hneq' Huni] Hupi]].
        specialize (HCunch p i s u x HIn Hunch).
        specialize (HCunch' p i s' u x HIn' Hunch).
        destruct HCunch as [j [r [Hprec Heq]]]; try eassumption.
        destruct HCunch' as [j' [r' [Hprec' Heq']]]; try eassumption.
        rewrite <- Heq. rewrite <- Heq'.
        cut (j' = j); intros.
        * subst j'. eauto using precedes_step_inv.  
        * eapply (HCupi _ _ _ _ Hsem Hsem'); eauto. 
Qed.

End Uniana.



