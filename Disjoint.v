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

  Parameter branch: Lab -> list Var.

  Definition is_branch br x := x ∈ branch br.

  Parameter val_true : Val -> bool.

  Parameter branch_spec :
    forall b, exists (d : list Val -> Lab), forall s, match (eff' (b, s)) with
                                      | Some (q,_) => q = d (map s (branch b))
                                      | None => True
                                      end.
  
  Definition DisjointBranch `{redCFG} (s : Lab) (xl : list Var) (qt qf : Lab) (π ϕ : list Lab) :=
    CPath s qt (π >: s) /\ CPath s qf (ϕ >: s) /\ branch s =' xl /\ Disjoint π ϕ.

  Parameter path_splits : forall `{redCFG}, Lab -> list (Lab * Lab * Lab).

  Parameter loop_splits : forall `{redCFG}, Lab -> Lab -> list (Lab * Lab * Lab).

  (* remove branch from splits, we can use the assumed global branch function to get varsets back*)
  Definition pl_split `{redCFG} (qh qe q1 q2 br : Lab) :=
      (exists π ϕ, CPath br qh (π >: q1 :>: br)
              /\ CPath br qe (ϕ >: q2 :>: br)
              /\ Disjoint (tl π :r: q1) (tl ϕ :r: q2)).

  Parameter path_splits_spec : forall `{redCFG} p q1 q2 br,
      pl_split p p q1 q2 br <->
      (br, q1, q2) ∈ path_splits p.
  
  Parameter loop_splits_spec : forall `{redCFG} qh qe q1 q2 br,
      loop_contains qh br /\ (* otherwise some splits would be considered as loop splits *)
      pl_split qh qe q1 q2 br <->
      (br, q1, q2) ∈ loop_splits qh qe.

  Parameter splits' : forall `{redCFG}, Lab -> Lab -> list (Lab * Lab * Lab).
  Parameter splits  : forall `{redCFG}, Lab -> list (Lab * Lab * Lab).

  Definition path_splits__imp `{C : redCFG} p
    := @path_splits _ _ _ _ (local_impl_CFG C (get_innermost_loop p)) p.
  Definition loop_splits__imp `{C : redCFG} h
    := @loop_splits _ _ _ _ (local_impl_CFG C h) h.

  Definition splits'_spec `{redCFG} {h': Lab} {H : loop_head h'}
    := forall h e sp, sp ∈ splits' h e
                 <-> sp ∈ loop_splits__imp h e
                   \/ exists br q q', (br,q,q') ∈ loop_splits__imp h e
                                   /\ (sp ∈ splits' br q
                                      \/ sp ∈ splits' br q').

  Definition splits_spec `{redCFG} := forall p sp, sp ∈ splits p
                                              <-> sp ∈ path_splits__imp p
                                                \/ exists br q q', (br,q,q') ∈ path_splits__imp p
                                                                /\ (sp ∈ splits' br q
                                                                   \/ sp ∈ splits' br q').

  Ltac path_simpl' H :=
    lazymatch type of H with
    | Path ?edge ?x ?y (?z :<: ?π) => let Q := fresh "Q" in
                                     eapply path_front in H as Q;
                                     cbn in Q; subst z
    | Path ?edge ?x ?y (?π :>: ?z) => let Q := fresh "Q" in
                                     eapply path_back in H as Q;
                                     cbn in Q; subst z
    end.
  
  Theorem lc_join_path_split `{redCFG} t1 t2 (p q1 q2 s : Lab) (i : Tag)
        (Hlc : last_common t1 t2 (s,i))
        (Hneq : q1 <> q2)
        (Hpath1 : TPath' ((p,i) :<: (q1,i) :<: t1))
        (Hpath2 : TPath' ((p,i) :<: (q2,i) :<: t2))
    : exists qq qq', (s,qq,qq') ∈ path_splits p.
  Proof.
    setoid_rewrite <-path_splits_spec. unfold pl_split.
    unfold TPath' in *;cbn in *. unfold last_common in Hlc; destructH.
    eapply postfix_path in Hpath1;eauto.
    2: eapply postfix_cons in Hlc0; eapply postfix_cons in Hlc0;
      do 2 rewrite <-cons_rcons_assoc in Hlc0; simpl_nl; eassumption.
    eapply postfix_path in Hpath2;eauto.
    2: eapply postfix_cons in Hlc2; eapply postfix_cons in Hlc2;
      do 2 rewrite <-cons_rcons_assoc in Hlc2; simpl_nl; eassumption.
    assert (forall L ed x y z l, @Path L ed x y (y :<: z :<: l >: x)
                            -> exists w l', Path ed x y ((l' >: w) :>: x)
                                      /\ (w :: tl l') ⊆ (z :: l)) as Hppath.
    {
      clear. intros. revert dependent y. revert z.
      induction l; intros z y H;cbn in *.
      - exists z, (y :: nil). cbn. split;[eassumption|]. firstorder.
      - inversion H;subst. path_simpl' H1.
        edestruct IHl as [w [l' IHl']];eauto.
        exists w, (y :: l'). cbn. unfold ne_rcons in IHl'. split;destructH;[econstructor;eauto|].
        admit.
    }
    eapply TPath_CPath in Hpath1. eapply TPath_CPath in Hpath2. cbn in Hpath2,Hpath1.
    Lemma ne_map_nl_rcons {A B : Type} (l : list A) a (f : A -> B)
      : ne_map f (l >: a) = (map f l) >: (f a).
    Admitted.
    rewrite ne_map_nl_rcons in Hpath1, Hpath2. cbn in *.
    eapply Hppath in Hpath1;eauto. eapply Hppath in Hpath2;eauto.
    destructH. destructH.
    exists w, w0, l', l'0.
    split_conj;eauto.
    (* open : what about q1 ∈ l2' & q2 ∈ l1' ? *)
    (* /\ move the q1/q2 into the last_common *)
  Admitted.

  Definition lc_disj_exit_lsplits_def (d : nat)
    := forall `{redCFG} (s e q h : Lab) (i1 i2 j k : Tag) t1 t2 (n : nat)
         (Hdep : d >= depth s - depth e)
         (Hlc : last_common t1 t2 (s,k))
         (Hhead : loop_head h)
         (Hqeq : ne_front t1 = (q, n :: j))
         (Hloop : loop_contains h q)
         (Hexit : exited h e)
         (Hpath1 : TPath (ne_back t1) (e,i1) ((e,i1) :<: t1))
         (Hpath2 : TPath (ne_back t2) (e,i2) ((e,i2) :<: t2)),
      exists (qq qq' : Lab) (xl : list Var), (s,qq,qq') ∈ loop_splits h e.

  Definition lc_disj_exits_lsplits_def (d : nat)
    := forall `{redCFG} (s e1 e2 q1 q2 h : Lab) (i1 i2 j k : Tag) t1 t2 (n m : nat)
         (Hdep : d >= depth s - depth e1)
         (Hdep : d >= depth s - depth e2)
         (Hlc : last_common t1 t2 (s,k))
         (Hhead : loop_head h)
         (Hqeq1 : ne_front t1 = (q1, n :: j))
         (Hqeq2 : ne_front t2 = (q2, m :: j))
         (Hloop1 : loop_contains h q1)
         (Hloop2 : loop_contains h q2)
         (Hexit1 : exited h e1)
         (Hexit2 : exited h e2)
         (Hpath1 : TPath (ne_back t1) (e1,i1) ((e1,i1) :<: t1))
         (Hpath2 : TPath (ne_back t2) (e2,i2) ((e2,i2) :<: t2)),
      exists (qq qq' : Lab), (s,qq,qq') ∈ (loop_splits h e1 ++ loop_splits h e2).

  Lemma lc_disj_exit_to_exits_lsplits d : lc_disj_exit_lsplits_def d -> lc_disj_exits_lsplits_def d.
  Proof.
    unfold lc_disj_exit_lsplits_def, lc_disj_exits_lsplits_def. intro Hlc_disj. intros.
  Admitted.

  Lemma lc_disj_exit_lsplits d : lc_disj_exit_lsplits_def d.
  Proof.
    unfold lc_disj_exit_lsplits_def;intros.
    
    
  Admitted.

  Lemma lc_disj_exits_lsplits d : lc_disj_exits_lsplits_def d.
  Proof.
    apply lc_disj_exit_to_exits_lsplits,lc_disj_exit_lsplits.
  Qed.      
  
  Lemma lc_join_split `{redCFG} t1 t2 (p q1 q2 s : Lab) (i j1 j2 k : Tag)
        (Hlc : last_common t1 t2 (s,k))
        (Hneq : q1 <> q2 \/ j1 <> j2)
        (Hpath1 : TPath' ((p,i) :<: (q1,j1) :< t1))
        (Hpath2 : TPath' ((p,i) :<: (q2,j2) :< t2))
    : exists qq qq', (s,qq,qq') ∈ splits p.
  Admitted.

  
End Disjoint.