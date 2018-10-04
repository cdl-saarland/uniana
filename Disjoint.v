Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Utils.
Require Import Coq.Logic.Classical.
Require Import List.
Require Import Nat.
Require Import Bool.Bool.
Require Import Coq.Logic.Eqdep_dec.

Require Evaluation Util.

Module Disjoint.
  Import Evaluation.Evaluation Util.

  Parameter branch: Lab -> option (Lab * Lab * Var * Var).

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

  Definition DisjointBranch (s : Lab) (x : Var) (t f : Lab) π ϕ :=
    Path s t π /\ Path s f ϕ /\ is_branch s x /\ Disjoint π ϕ.

  Parameter splits : Lab -> list (Lab * Var).

  Parameter splits_spec : forall conv br x,
      (exists qt qf π ϕ, qt -->* conv /\ qf -->* conv /\
                    DisjointBranch br x qt qf π ϕ) <->
      List.In (br, x) (splits conv).
  
  Definition DivergenceWitness (br : Lab) x xb t t' := 
    (exists (l : Tag) u u', val_true (u x) =/= val_true (u' x) /\
                    In (br, l, u) t /\
                    In (br, l, u') t' /\
                    exists tt ff, branch br = Some (tt, ff, x, xb)).

(*  Lemma different_tgt_is_branch {br : Lab} {i : Tag} {s s' : State} {k k' : Conf} :
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
  Qed.*)

(*  Lemma single_edge_disjoint_path (q a q' : Lab) x (p : Path a q') :
    is_branch a x ->
    ~ PathIn q p ->
    a --> q -> 
    exists p', DisjointBranch a x q' q p p'.
  Proof.
    intros Hbr Hnin Hedge.
    exists (PathStep a a q (PathInit a) Hedge).
    unfold DisjointBranch.
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
    DisjointBranch a x q' q p (step_exists_path step).
  Proof.
    simpl.
    intros Hbr Hnin.
    unfold DisjointBranch.
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
    exists x xb, (exists a b, DisjointBranch q x q q' a b) /\
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
        - unfold DisjointBranch.
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
                      DisjointBranch br x q' q Pbrq' Pbrq) /\
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
  Qed.*)
    
End Disjoint.