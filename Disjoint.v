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
              /\ Disjoint (tl (π :r: q1)) (tl (ϕ :r: q2))).

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


  Lemma lc_join_path_split_help1 (L : Type) (edge : L -> L -> bool) (x y : L) (l : list L)
    : @Path L edge x y (y :<: l >: x)
      -> exists z l', Path edge x y ((l' >: z) :>: x)
                /\ (tl (l' :r: z)) ⊆ l.
  Proof.
  Admitted.

  Lemma disjoint2 {A : Type} `{EqDec A} (l1 l2 : list A)
    : Disjoint l1 l2 <-> forall x y, x ∈ l1 -> y ∈ l2 -> x <> y.
  Proof.
    split;unfold Disjoint;intros.
    - intro N. subst x. firstorder.
    - split;intros;intro N;eapply H0;eauto.
  Qed.

  (* TODO: this implementation of impl_list doesn't output a TPath given a TPath,
   * because the tags are the old ones. This has the advantage that it remains a subset
   * of the input on the other hand. I might want to change this. 
   * This change would simplify impl_disj_coord_impl_disj_lab but complicate 
   * impl_disj_lab_disj_lab and the helper2 lemma. *)
  Definition impl_list `{redCFG} (n : nat) :=
    filter (fun qj : Coord => let (q,j) := qj in (depth q ==b n)
                                              || (depth q ==b S n)
                                                  && loop_head_b q
                                                  && match j with nil => false
                                                             | a :: j => (0 ==b a)
                                                     end).

  Definition TPath'' `{redCFG} l := match l with nil => True | (a :: l) => TPath' (a :< l) end.

  Definition impl_list' `{redCFG} p := impl_list (depth p).

  Lemma impl_disj_coord_impl_disj_lab `{redCFG} l1 l2 s p i
        (Hpath1 : TPath' ((p,i) :< l1 :>: (s,i)))
        (Hpath2 : TPath' ((p,i) :< l2 :>: (s,i)))
        (Hdisj : Disjoint (impl_list' p l1) (impl_list' p l2))
    : Disjoint (map fst (impl_list' p l1)) (map fst (impl_list' p l2)).
  Proof.
    (* divide the labs in three classes: tophead, notheads or otherheads.
     * - if there is a tophead it has to be s and s is not in l1/l2
     * - all notheads have tag i
     * - all otherheads have tag 0::i 
     * then inside both class they are disjoint, because of same tag
     * and since they are pairwise different labs they are all disjoint *)
  Admitted.

  Lemma impl_disj_lab_disj_lab `{redCFG} l1 l2 s p i 
        (Hpath1 : TPath' ((p,i) :< l1 :>: (s,i)))
        (Hpath2 : TPath' ((p,i) :< l2 :>: (s,i)))
        (Hdisj : Disjoint (map fst (impl_list' p l1)) (map fst (impl_list' p l2)))
    : Disjoint (map fst l1) (map fst l2).
  Proof.
    (* all new members of "map fst l" are hidden in loop-headers - which are disjoint *)
    (* this requires also another lemma about the absence of labs outside of p's or s's head*)
  Admitted.
  
  Lemma filter_incl `{A : Type} (l : list A) (f : A -> bool) : filter f l ⊆ l.
  Proof.
    induction l;cbn;unfold "⊆";eauto.
    intros. destruct (f a);unfold In in *;firstorder.
  Qed.             
  
  Lemma lc_join_path_split_help2 `{redCFG} (p s q1 q2 : Lab) (t1 t2 : ne_list Coord) l1 l2 i
        (Hpath1 : TPath' ((p,i) :< l1 :>: (s,i)))
        (Hpath2 : TPath' ((p,i) :< l2 :>: (s,i)))
        (Hdisj : Disjoint l1 l2)
    : Disjoint (map fst l1) (map fst l2).
  Proof.
    eapply impl_disj_lab_disj_lab;eauto.
    eapply impl_disj_coord_impl_disj_lab;eauto.
    eapply disjoint_subset;unfold impl_list;eauto using filter_incl.
  Qed.

(*    Lemma impl_list_spec1 `{redCFG} p q i j l
          (Hpath : TPath' ((p,i) :< l))
          (Hin1 : (q,j) ∈ l)impl_list (depth p) (map fst l))
          (Hnloop : ~ loop_head q)
      : j = i.*)
    
    (*disjoint2. rewrite disjoint2 in Hdisj. intros r1 r2 Hr1 Hr2 Hreq. subst r2.
    eapply in_fst in Hr1 as [j1 Hr1]. eapply in_fst in Hr2 as [j2 Hr2].
    eapply Hdisj; eauto. enough (j1 = j2) by (subst j1;reflexivity).*)
    (* implode list *)
  
  
  Theorem lc_join_path_split `{redCFG} t1 t2 (p q1 q2 s : Lab) (i : Tag)
          (Hlc : last_common ((q1,i) :<: t1) ((q2,i) :<: t2) (s,i))
          (Hneq : q1 <> q2)
          (Hpath1 : TPath' ((p,i) :<: (q1,i) :<: t1))
          (Hpath2 : TPath' ((p,i) :<: (q2,i) :<: t2))
    : exists qq qq', (s,qq,qq') ∈ path_splits p.
  Proof.
    setoid_rewrite <-path_splits_spec. unfold pl_split.
    unfold TPath' in *;cbn in *. unfold last_common in Hlc; destructH.
    eapply id in Hpath1 as Hpath1'; eapply id in Hpath2 as Hpath2'.
    eapply postfix_path in Hpath1;eauto. 
    2: eapply postfix_cons in Hlc0;
      rewrite <-cons_rcons_assoc in Hlc0; simpl_nl; eassumption.
    eapply postfix_path in Hpath2;eauto.
    2: eapply postfix_cons in Hlc2;
      rewrite <-cons_rcons_assoc in Hlc2; simpl_nl; eassumption.
    cbn in Hpath1,Hpath2.                                  
    eapply TPath_CPath in Hpath1. eapply TPath_CPath in Hpath2. cbn in Hpath2,Hpath1.
    rewrite ne_map_nl_rcons in Hpath1, Hpath2. cbn in *.
    let help := lc_join_path_split_help1 in eapply help in Hpath1;eauto; eapply help in Hpath2;eauto.
    destructH. destructH.
    exists z0, z, l'0, l'.
    split_conj;eauto.
    eapply disjoint_subset;eauto.
    eapply lc_join_path_split_help2;eauto.
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