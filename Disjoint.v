Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Utils.
Require Import Coq.Logic.Classical.
Require Import List.
Require Import Nat.
Require Import Bool.Bool.
Require Import Coq.Logic.Eqdep_dec.

Require Import Tagged.

Parameter path_splits : forall `{redCFG}, Lab -> list (Lab * Lab * Lab).

Parameter loop_splits : forall `{redCFG}, Lab -> Lab -> list (Lab * Lab * Lab).

(* remove branch from splits, we can use the assumed global branch function to get varsets back*)
Definition pl_split `{redCFG} (qh qe q1 q2 br : Lab) :=
  (exists π ϕ, CPath br qh (π >: q1 :>: br)
          /\ CPath br qe (ϕ >: q2 :>: br)
          /\ q1 <> q2
          /\ Disjoint (tl π) (tl ϕ)).

Parameter path_splits_spec : forall `{redCFG} p q1 q2 br,
    pl_split p p q1 q2 br <->
    (br, q1, q2) ∈ path_splits p.

Parameter loop_splits_spec : forall `{redCFG} qh qe q1 q2 br,
    loop_contains qh br /\ (* otherwise some splits would be considered as loop splits *)
    pl_split qh qe q1 q2 br <->
    (br, q1, q2) ∈ loop_splits qh qe.

Parameter splits' : forall `{redCFG}, Lab -> Lab -> list (Lab * Lab * Lab).
Parameter splits  : forall `{redCFG}, Lab -> list (Lab * Lab * Lab).
Parameter rel_splits : forall `{redCFG}, Lab -> Lab -> list (Lab * Lab * Lab).

Definition path_splits__imp `{C : redCFG} p
  := @path_splits _ _ _ _ (local_impl_CFG C (get_innermost_loop p)) p.
Definition loop_splits__imp `{C : redCFG} h
  := @loop_splits _ _ _ _ (local_impl_CFG C h) h.

Parameter splits'_spec 
  : forall `{redCFG} h e sp, sp ∈ splits' h e
                        <-> sp ∈ loop_splits__imp h e
                          \/ exists br q q', (br,q,q') ∈ loop_splits__imp h e
                                       /\ (sp ∈ splits' br q
                                          \/ sp ∈ splits' br q').

Parameter rel_splits_spec 
  : forall `{redCFG} p q sp, sp ∈ rel_splits p q
                        <-> exists h e, exited h e
                                 /\ e -a>* p (* acyclic, bc. otw. path could use back_edge of outer loop *)
                                 /\ loop_contains h q
                                 /\ sp ∈ loop_splits h e.
(* sp ∈ splits' h e. <--- deprecated *)

Parameter splits_spec
  : forall `{redCFG} p sp, sp ∈ splits p
                      <-> sp ∈ path_splits__imp p (* usual split *)
                        \/ (exists h, (* lsplits of exited loops: *)
                              exited h p /\ sp ∈ splits' h p)
                        \/ exists br q q',(br,q,q') ∈ path_splits__imp p
                                    (* loop_split of splitting heads *)
                                    /\ (sp ∈ splits' br q
                                       \/ sp ∈ splits' br q').

Arguments loop_splits : default implicits.
Lemma loop_splits_impl_invariant q p x `(C : redCFG)
      (Hin : x ∈ loop_splits C (get_innermost_loop q) p)
  : x ∈ loop_splits (local_impl_CFG C (get_innermost_loop q)) (get_innermost_loop q) p.
Admitted.
Arguments loop_splits {_ _ _ _ _}.

Lemma lc_join_path_split_help1 (L : Type) (edge : L -> L -> bool) (x y : L) (l : list L)
  : @Path L edge x y (y :<: l >: x)
    -> exists z l', Path edge x y ((l' >: z) :>: x)
              /\ z ∈ l /\ (tl l') ⊆ l.
Proof.
Admitted.

Lemma disjoint2 {A : Type} `{EqDec A} (l1 l2 : list A)
  : Disjoint l1 l2 <-> forall x y, x ∈ l1 -> y ∈ l2 -> x <> y.
Proof.
  split;unfold Disjoint;intros.
  - intro N. subst x. firstorder.
  - split;intros;intro N;eapply H0;eauto.
Qed.

Definition impl_list `{redCFG} (h : Lab) :=
  filter (fun q : Lab => (loop_contains_b h q)
                        && ((depth q ==b depth h)
                            || (depth q ==b S (depth h))
                                && loop_head_b q
                           )
         ).

Definition impl_list' `{redCFG} (p : Lab) (i : Tag) (l : list Coord):=
  map (fun q => (q,i)) (impl_list (get_innermost_loop p) (map fst l)).


Lemma impl_list_cfg_tpath `{C : redCFG} l p i
      (Hin : forall q, q ∈ map fst l -> loop_contains (get_innermost_loop p) q)
      (Hpath : TPath' ((p,i) :< l))
      (D := local_impl_CFG C (get_innermost_loop p))
  : TPath' ((p,i) :< impl_list' p i l).
Proof.
Admitted.

Lemma impl_disj_coord_impl_disj_lab `{redCFG} l1 l2 s p i
      (Hpath1 : TPath' ((p,i) :< l1 :>: (s,i)))
      (Hpath2 : TPath' ((p,i) :< l2 :>: (s,i)))
      (Hdisj : Disjoint (impl_list' p i l1) (impl_list' p i l2))
  : Disjoint (impl_list (get_innermost_loop p) (map fst l1))
             (impl_list (get_innermost_loop p) (map fst l2)).
Proof.
(* everything has tag i
 * thus they are disjoint, because of same tag *)
Admitted.

Lemma impl_disj_lab_disj_lab `{redCFG} l1 l2 s p i 
      (Hpath1 : TPath' ((p,i) :< l1 :>: (s,i)))
      (Hpath2 : TPath' ((p,i) :< l2 :>: (s,i)))
      (Hdisj : Disjoint (impl_list (get_innermost_loop p) (map fst l1))
                        (impl_list (get_innermost_loop p) (map fst l2)))
  : Disjoint (map fst l1) (map fst l2).
Proof.
  (* all new members of "map fst l" are hidden in loop-headers - which are disjoint *)
Admitted.

Lemma coord_disj_impl_coord `{redCFG} l1 l2 s p i 
      (Hpath1 : TPath' ((p,i) :< l1 :>: (s,i)))
      (Hpath2 : TPath' ((p,i) :< l2 :>: (s,i)))
      (Hdisj : Disjoint l1 l2)
  : Disjoint (impl_list' p i l1) (impl_list' p i l2).
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
  eapply coord_disj_impl_coord;eauto.
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
  eapply lc_join_path_split_help2 in Hlc1;eauto.
  - split_conj;eauto;[|eapply disjoint_subset;eauto]. eapply disjoint2;eauto.
  - admit.
  - admit.
Admitted.

Definition lc_disj_exit_lsplits_def (d : nat)
  := forall `{redCFG} (s e q1 q2 h : Lab) (i j1 j2 k : Tag) (t1 t2 : list Coord)
       (Hdep : d = depth s - depth e)
       (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
       (Hexit1 : exit_edge h q1 e)
       (Hexit2 : exit_edge h q2 e)
       (Hpath1 : TPath' ((e,i) :<: (q1, j1) :< t1))
       (Hpath2 : TPath' ((e,i) :<: (q2, j2) :< t2)),
    exists (qq qq' : Lab), (s,qq,qq') ∈ loop_splits h e.

Definition lc_disj_exits_lsplits_def (d : nat)
  := forall `{redCFG} (s e1 e2 q1 q2 h : Lab) (i j1 j2 k : Tag) (t1 t2 : list Coord)
       (Hdep : d >= depth s - depth e1)
       (Hdep : d >= depth s - depth e2)
       (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
       (Hexit1 : exit_edge h q1 e1)
       (Hexit2 : exit_edge h q2 e2)
       (Hpath1 : TPath' ((e1,i) :<: (q1,j1) :< t1))
       (Hpath2 : TPath' ((e2,i) :<: (q2,j2) :< t2)),
    exists (qq qq' : Lab), (s,qq,qq') ∈ (loop_splits h e1 ++ loop_splits h e2).

Theorem lc_disj_exit_to_exits_lsplits d : lc_disj_exit_lsplits_def d -> lc_disj_exits_lsplits_def d.
Proof.
  unfold lc_disj_exit_lsplits_def, lc_disj_exits_lsplits_def. intro Hlc_disj. intros.
Admitted.

Theorem lc_disj_exit_lsplits' d : lc_disj_exit_lsplits_def d.
Proof.
  unfold lc_disj_exit_lsplits_def;intros.
Admitted.

Corollary lc_disj_exit_lsplits `{redCFG} (s e q1 q2 h : Lab) (i j1 j2 k : Tag) (t1 t2 : list Coord)
          (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
          (Hexit1 : exit_edge h q1 e)
          (Hexit2 : exit_edge h q2 e)
          (Hpath1 : TPath' ((e,i) :<: (q1, j1) :< t1))
          (Hpath2 : TPath' ((e,i) :<: (q2, j2) :< t2))
  : exists (qq qq' : Lab), (s,qq,qq') ∈ loop_splits h e.
Proof.
  eapply lc_disj_exit_lsplits';eauto.
Qed.

Theorem lc_disj_exits_lsplits' d : lc_disj_exits_lsplits_def d.
Proof.
  apply lc_disj_exit_to_exits_lsplits,lc_disj_exit_lsplits'.
Qed.      

Lemma exit_edge_dep_eq `{redCFG} h qe1 qe2 e1 e2
      (Hexit1 : exit_edge h qe1 e1)
      (Hexit2 : exit_edge h qe2 e2)
  : depth e1 = depth e2. 
Admitted.

Corollary lc_disj_exits_lsplits `{redCFG}
          (s e1 e2 q1 q2 h : Lab) (i j1 j2 k : Tag) (t1 t2 : list Coord)
          (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
          (Hexit1 : exit_edge h q1 e1)
          (Hexit2 : exit_edge h q2 e2)
          (Hpath1 : TPath' ((e1,i) :<: (q1,j1) :< t1))
          (Hpath2 : TPath' ((e2,i) :<: (q2,j2) :< t2))
  : exists (qq qq' : Lab), (s,qq,qq') ∈ (loop_splits h e1 ++ loop_splits h e2).
Proof.
  eapply lc_disj_exits_lsplits';eauto.
  replace (depth e2) with (depth e1);eauto using exit_edge_dep_eq.
Qed.

Theorem lc_join_split `{redCFG} t1 t2 (p q1 q2 s : Lab) (i j1 j2 k : Tag)
        (* it is important to cons qj's in front of the t's *)
        (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
        (Hneq : q1 <> q2 \/ j1 <> j2)
        (Hpath1 : TPath' ((p,i) :<: (q1,j1) :< t1))
        (Hpath2 : TPath' ((p,i) :<: (q2,j2) :< t2))
  : exists qq qq', (s,qq,qq') ∈ splits p.
Proof.
Admitted.



(*Lemma head_diff
        (Hneq : j1 <> j2)
    : exists h, *)

Definition sub_list {A : Type} (l l' : list A) : Prop :=
  exists l1 l2, Postfix (l1 ++ l') l /\ Prefix (l ++ l2) l.  

Lemma common_tag_prefix_head `{redCFG} h p q i j k t
      (Hloop__p : loop_contains h p) (* what if h is root ? *)
      (Hloop__q : loop_contains h q)
      (Hdom : Dom edge root q p)
      (Hpath : TPath (root,start_tag) (p,i) t)
      (Hprec__q : Precedes fst t (q,j))
      (Hprec__h : Precedes fst t (h,k))
  : Prefix k i /\ Prefix k j.
Admitted.

(* TODO: we need a variant of this lemma where we refer to (h,i) h dominating q *)   
Lemma common_tag_prefix_qq `{redCFG} p q (i j1 j2 : Tag) t1 t2
      (Hdeq : deq_loop q p)
      (Hdom : Dom edge root q p)
      (Hpath1 : TPath (root,start_tag) (p,i) t1)
      (Hpath2 : TPath (root,start_tag) (p,i) t2)
      (Hprec1 : Precedes fst t1 (q,j1))
      (Hprec2 : Precedes fst t2 (q,j2))
  : exists j, Prefix j j1 /\ Prefix j j2 /\ length j = depth p.
Admitted.

Lemma common_tag_prefix_pq `{redCFG} p q i j t
      (Hdeq : deq_loop q p)
      (Hdom : Dom edge root q p)
      (Hpath : TPath (root,start_tag) (p,i) t)
      (Hprec : Precedes fst t (q,j))
  : Prefix i j.
Admitted.

Lemma first_sync_exit `{redCFG} p q l1 l2 i j1 j2 r0 i0
      (Hneq : j1 <> j2)
      (Hdom : Dom edge r0 q p)
      (Hl1 : TPath (r0,i0) (p,i) l1) (* p is possibly the exit *)
      (Hl2 : TPath (r0,i0) (p,i) l2)
      (Hprec1 : Precedes fst l1 (q,j1))
      (Hprec2 : Precedes fst l2 (q,j2))
  : exists h qe1 qe2 e1 e2 j k1 k2,
    loop_contains h q /\ ~ loop_contains h p
    /\ exit_edge h qe1 e1 /\ exit_edge h qe2 e2
    /\ sub_list ((e1,j)::(qe1,k1)::nil) l1 /\ sub_list ((e2,j)::(qe2,k2)::nil) l2
    /\ Precedes fst l1 (qe1,k1) /\ Precedes fst l2 (qe2,k2) /\ k1 <> k2
    /\ Precedes fst l1 ( e1,j ) /\ Precedes fst l2 ( e2,j ).
Proof.
(* Because q dominates p, all loops containing q are exited only once after the last 
 * occurence of q is visited. This also implies that the suffices all the tags between q
 * and p are the same concerning the loops, in which both nodes are. Thus as soon as the
 * tags are equal they can only differ inside of loops which do not contain p. 
 * 
 * the head we're looking for is the head of q at depth given by the last position 
 * where the tags j1 & j2 are different.
 * there is exactly one exit on each trace afterwards, where the tags will be equal again.


   * don't use this idea:
   * induction on the size of the non-equal prefix of j1 & j2
   * base: j1 = js = j2 --> contradiction
   * step: assume j1 = j1' ++ js /\ j2 = j1' ++ js /\ len j1' = S n = len j2'.
   * *     and we have the result for len j1' = n = len j2'.
   * * collapse innermost loop of q. let h be the head. if h has now the same tag on
   * * both traces then h is the one. otherwise apply IH on this graph. 
   * * 
   *)    
Admitted.
