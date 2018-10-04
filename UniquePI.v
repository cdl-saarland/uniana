Require Import Coq.Classes.EquivDec.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.Decidable.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Utils.
Require Import Lists.ListSet.
Require Import List.
Require Import Nat.

Require Evaluation Disjoint Util.

Module UniquePI.
  Export Evaluation.Evaluation Disjoint.Disjoint Util.
  
  Definition Upi := Lab -> Lab -> bool.

  Definition Uni := Lab -> Var -> bool.

  Definition tag_of (c : Conf) := match c with (_,i,_) => i end.

  Definition upi_prop p q t1 t2 :=
    forall i j j' r r' q' s s', 
      Precedes' t1 (q,j,r) (p,i,s) -> Precedes' t2 (q',j',r') (p,i,s') -> j = j'.
  
(*  Definition upi_prop q p k k' t t' :=
    forall j j' i r r' s s', Precedes k t (q, j, r) (p, i, s) ->
                             Precedes k' t' (q, j', r') (p, i, s') ->
                             j' = j.*)

  Definition upi_concr (upi : Upi) : Hyper :=
    fun ts => forall t t',
        ts t -> ts t' ->
        forall q p, upi q p = true -> upi_prop q p (`t)%prg (`t')%prg.

  Parameter lh_p_le_q : Lab -> Lab -> list (Lab * Var).
  
  Parameter lh_p_le_q_spec :
    forall (p q le : Lab) (x : Var), List.In (le,x) (lh_p_le_q p q)
                               <-> (exists (lh : Lab),
                                     le --> lh
                                     /\ AcyPath lh p
                                     /\ AcyPath p le
                                     /\ AcyPath le q
                                     /\ exists a b, branch le = Some (a, b, x)).

  Parameter loop_splits : Lab -> Lab -> list (Lab * Var).

  Parameter loop_splits_spec :
    forall (p q s : Lab) (x : Var), List.In (s,x) (loop_splits p q)
                               <-> (exists (lh le le' : Lab),
                                     le --> lh
                                     /\ AcyPath lh p
                                     /\ AcyPath p le
                                     /\ AcyPath lh le'
                                     /\ AcyPath le q
                                     /\ le =/= le'
                                     /\ List.In (s,x) (splits le')).
   
  Definition upi_trans (upi : Upi) (uni : Uni) : Upi :=
    fun p
    => fun q
      => join_andb (map (fun spl
                    => match spl with (s,x) => uni s x end)
                           (lh_p_le_q p q
                           ++  loop_splits p q))
                  && (join_andb (map (upi p) (preds q))).

(*  Lemma last_inst_upi_prop {p br m m' w w' q q' i j j' s s' r r' step step' t t'} :
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
  
  Lemma upi_comm q p k k' t t' :
    upi_prop q p k k' t t' ->
    upi_prop q p k' k t' t.
  Proof.
    unfold upi_prop in *. intros. symmetry. eauto.
  Qed.
  *)
  Lemma upi_correct :
    forall upi uni ts, sem_hyper (upi_concr upi) ts -> upi_concr (upi_trans upi uni) ts.
  Proof.
    intros.
    unfold sem_hyper in H. destruct H as [ts' [Hconcr Htrace]].
    unfold upi_concr. intros k k' t t' ts_t ts_t' q p upi_trans_true.
    unfold upi_prop. intros * Hprec1 Hprec2.
  Admitted. (*
    remember (q,j,r) as q1;
      remember (q,j',r') as q2;
      remember (p,i,s) as p1;
      remember (p,i,s') as p2.
    revert dependent ts. revert dependent ts'.
    induction Hprec1; induction Hprec2; intros.
    - subst k k0. inversion Heqp1; inversion Heqp2. reflexivity.
    - exfalso. apply H. subst k.
      inversion Heqp1;
        inversion Heqp2;
        inversion Heqq2.
      rewrite H1. reflexivity.
    - eapply IHHprec2; eauto.
      admit.     
      
    - exfalso. apply H. subst k.
      inversion Heqp2;
        inversion Heqp1;
        inversion Heqq1.
      rewrite H1. reflexivity.
    - admit.
  Admitted.*)

(*  Lemma upi_prefix {b p i s s' q j r q' j' r' k k' kp kp' pstep pstep' t t' tr tr'}
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
*)
(*
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
  *)
End UniquePI.