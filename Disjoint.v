Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Utils.
Require Import Coq.Logic.Classical.
Require Import List.
Require Import Nat.
Require Import Bool.Bool.
Require Import Coq.Logic.Eqdep_dec.

Require Import Tagged Evaluation.

Parameter path_splits : forall `{redCFG}, Lab -> list (Lab * Lab * Lab).

Parameter loop_splits : forall `{redCFG}, Lab -> Lab -> list (Lab * Lab * Lab).

(* remove branch from splits, we can use the assumed global branch function to get varsets back*)
Definition pl_split `{redCFG} (qh qe q1 q2 br : Lab) :=
  (exists π ϕ, CPath br qh (π :>: br)
          /\ CPath br qe (ϕ :>: br)
          /\ q1 = ne_back π
          /\ q2 = ne_back ϕ
          /\ q1 <> q2 (* if π = single or φ = single, then this is not implied by the next condition *)
          /\ Disjoint (tl π) (tl ϕ)).

Parameter path_splits_spec (* unused *): forall `{redCFG} p q1 q2 br,
    pl_split p p q1 q2 br <->
    (br, q1, q2) ∈ path_splits p.

Parameter loop_splits_spec (* unused *): forall `{redCFG} qh qe q1 q2 br,
    loop_contains qh br /\ (* otherwise some splits would be considered as loop splits *)
    exited qh qe /\
    pl_split qh qe q1 q2 br <->
    (br, q1, q2) ∈ loop_splits qh qe.

Parameter splits' : forall `{redCFG}, Lab -> Lab -> list (Lab * Lab * Lab).
Parameter splits  : forall `{redCFG}, Lab -> list (Lab * Lab * Lab).
Parameter rel_splits : forall `{redCFG}, Lab -> Lab -> list (Lab * Lab * Lab).

(*Lemma in_loop_CFG `{C : redCFG} (p h : Lab)
      (Hhead : loop_head h)
      (Hinner : get_innermost_loop p = h)
  : loop_nodes h p.
Proof.
  unfold loop_nodes. cbn. 
  rewrite get_innermost_loop_spec in Hinner.
  destruct (depth p) eqn:E;[|unfold innermost_loop;eauto].
  - unfold depth in E. 
  - unfold innermost_loop in Hinner. firstorder.
Admitted.
Set Printing All.
*)

(* TODO *)

(* proof sketch:
 * provide construction to get elem of type in opt_loop_CFG
 * this is the element to instantiate in the path_splits__imp definition. *)

(*
Lemma in_implode_CFG (* unused *)`{C : redCFG} (p : Lab)
      (Hdeq : deq_loop root p)
  : implode_nodes C p.
Admitted.
 *)

Arguments loop_head {_ _ _ _} _.
Arguments loop_head_dec {_ _ _ _} _.
Arguments get_innermost_loop_strict {_ _ _ _} _.

Definition loop_containsT_loop_head `(C : redCFG) (p : Lab)
           (H : {h : Lab | loop_contains h p})
  : {h : Lab | loop_head C h}.
Proof.
  destruct H;exists x. eapply loop_contains_loop_head;eauto.
Defined.

Open Scope prg.

Lemma loop_containsT_loop_head_same_h (* unused *)`(C : redCFG) (p : Lab)
      (H : {h : Lab | loop_contains h p})
  : (`H) = (` (loop_containsT_loop_head H)).
Proof.
  unfold loop_containsT_loop_head.
  destruct H. cbn. reflexivity.
Qed.

Local Arguments deq_loop {_ _ _ _} _.
Local Arguments depth {_ _ _ _} _.
Local Arguments exited {_ _ _ _} _.

Definition thrice (A B : Type) (f : A -> B) (xyz : A*A*A) : B*B*B
  := match xyz with (x,y,z) => (f x, f y, f z) end.


Definition get_innermost_loop' `{C : redCFG} p
  := match get_innermost_loop p with
     | Some (exist _ h _) => h
     | None => root
     end.

Lemma deq_loop_innermost' `{C : redCFG} (p : Lab)
  : deq_loop C (get_innermost_loop' p) p.
Proof.
  remember (get_innermost_loop' p) as h.
  specialize (get_innermost_loop_spec p) as Hspec.
  unfold get_innermost_loop' in Heqh.
  destruct (get_innermost_loop p).
  - destruct s. subst. unfold innermost_loop in Hspec. subst. destructH; auto.
  - subst. unfold deq_loop. intros. exfalso; eauto.
Qed.   
    

Program Definition path_splits__imp' `{C : redCFG} (p : Lab)
  := let D := (local_impl_CFG C (get_innermost_loop' p)) in
     (@path_splits _ _ _ _ D _).
Next Obligation.
  eapply implode_CFG_elem.
  left. eapply head_exits_deq_loop_inv1. 
  eapply deq_loop_innermost'. 
Defined.

Arguments exited {_ _ _ _ _} _.

Definition path_splits__imp `{C : redCFG} (p : Lab)
  := map (thrice (@proj1_sig Lab _)) (path_splits__imp' p).

Lemma exited_head (* unused *)`{C : redCFG} (h e : Lab)
      (H : exited h e)
  : loop_head C h.
Proof.
  unfold exited in H. destructH. unfold exit_edge in H. destructH. eapply loop_contains_loop_head;eauto.
Qed.

Program Definition loop_splits__imp' `{C : redCFG} (h e : Lab)
  := match decision (exited h e) with
     | left H => (@loop_splits _ _ _ _ (local_impl_CFG C h) _ _)
     | _ => nil
     end.
Next Obligation.
  eapply implode_CFG_elem.
  left. eapply head_exits_deq_loop_inv1.
  eapply deq_loop_refl.
Defined.
Next Obligation.
  eapply implode_CFG_elem.
  left. eapply head_exits_deq_loop_inv1.
  unfold exited in H. destructH.
  eapply deq_loop_exited';eauto.
Defined.


Definition loop_splits__imp `{C : redCFG} (h e : Lab)
  := let d := match decision (loop_head C h) with
              | left H => Some (exist _ h H)
              | right _ => None
              end in
     map (thrice (@proj1_sig Lab _)) (loop_splits__imp' h e).

Parameter splits'_spec (* unused *)
  : forall `{redCFG} h e sp, sp ∈ splits' h e
                        <-> sp ∈ loop_splits__imp h e
                          \/ exists br q q', (br,q,q') ∈ loop_splits__imp h e
                                       /\ exited br q /\ exited br q'
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
                                    /\ exited br q /\ exited br q'
                                    (* loop_split of splitting heads *)
                                    /\ (sp ∈ splits' br q
                                       \/ sp ∈ splits' br q').

Arguments loop_splits : default implicits.


Lemma loop_splits_loop_splits__imp (* unused *)`{C : redCFG}:
  forall (p br h : Lab) (Hspec : innermost_loop h br) (qq qq' : Lab) (Hsplits : (br, qq, qq') ∈ loop_splits C h p),
    (br,qq,qq') ∈ loop_splits__imp h p.
Proof.
  intros p br h Hspec qq qq' Hsplits.
Admitted.
Arguments loop_splits {_ _ _ _ _}.

Lemma neconc_nercons (A : Type) (l : ne_list A) (a : A)
  : l :+: ne_single a = l :>: a.
Proof.
  induction l;cbn;auto.
Qed.

Lemma lc_join_path_split_help1 (* unused *)(L : Type) (edge : L -> L -> bool) (x y : L) (l : ne_list L)
  : @Path L edge x y (y :<: l :>: x)
    -> exists z l', Path edge x y ((l' :>: z) :>: x)
              /\ z ∈ l /\ (tl l') ⊆ l.
Proof.
  intros.
  revert dependent x. revert y.
  induction l;cbn;eauto;intros.
  - exists a, (ne_single y). cbn.
    split_conj;[auto|left;reflexivity|firstorder].
  - inversion H;subst. rewrite neconc_nercons in H1.
    assert (b = a) by (inversion H1;subst;auto);subst.
    specialize (IHl a x). exploit IHl.
    destructH.
    exists z, (y :<: l'). cbn.
    split_conj;[cbn;econstructor;[repeat rewrite neconc_nercons;eauto|eauto]|right;auto|cbn].
    destruct l'.
    + cbn in IHl0. inversion IHl0;subst. clear. intros ? ? . cbn in H. left. firstorder.
    + intros ? ? . cbn in H0. destruct H0;[subst;cbn in IHl0;inversion IHl0;subst;left;auto|].
      cbn in IHl3. right. firstorder.
Qed.

Lemma disjoint2 (* unused *){A : Type} `{EqDec A} (l1 l2 : list A)
  : Disjoint l1 l2 <-> forall x y, x ∈ l1 -> y ∈ l2 -> x <> y.
Proof.
  split;unfold Disjoint;intros.
  - intro N. subst x. firstorder.
  - split;intros;intro N;eapply H0;eauto.
Qed.

Local Arguments deq_loop {_ _ _ _ _}.
Local Arguments depth {_ _ _ _ _}.
Arguments loop_head {_ _ _ _ _}.
Arguments loop_head_dec {_ _ _ _ _}.
Arguments get_innermost_loop_strict {_ _ _ _ _}. 

Fixpoint impl_list' `{redCFG} (r : Lab) (l : list Coord) :=
  match l with
  | nil => nil
  | (q,j) :: l => match decision (deq_loop r q) with
                 | left H => (impl_of_original' (h:=r) (p:=q) (or_introl H), j) :: impl_list' r l
                 | right H => match decision (exists e : Lab, exited q e /\ deq_loop r e) with
                             | left Q => (impl_of_original' (h:=r) (p:=q) (or_intror Q), tl j) :: impl_list' r l
                             | right Q => impl_list' r l
                             end
                 end
  end.

Definition innermost_loop' `{redCFG} (h p : Lab) := (loop_contains h p \/ h = root) /\ deq_loop h p.

Definition get_innermost_loop_strict' `{C : redCFG} p
  := match get_innermost_loop_strict p with
     | Some (exist _ h _) => h
     | None => root
     end.
(*
Lemma impl_list_cfg_tpath (* unused *)`{C : redCFG} l p i
      (Hin : forall q, q ∈ map fst l -> loop_contains (get_innermost_loop_strict' p) q)
      (Hpath : TPath' ((p,i) :< l))
      (D := local_impl_CFG C ((option_map (loop_containsT_loop_head (C:=C) (p:=p)) (get_innermost_loop_strict p))))
  : TPath' ((p,i) :< impl_list' p l).
Proof.
Admitted.
 *)

Lemma impl_disj_coord_impl_disj_lab `{redCFG} l1 l2 s p i
      (Hpath1 : TPath' ((p,i) :< l1 :>: (s,i)))
      (Hpath2 : TPath' ((p,i) :< l2 :>: (s,i)))
      (Hdisj : Disjoint (impl_list' p l1) (impl_list' p l2))
  : Disjoint (impl_list (get_innermost_loop_strict' p) (map fst l1))
             (impl_list (get_innermost_loop_strict' p) (map fst l2)).
Proof.
(* everything has tag i
 * thus they are disjoint, because of same tag *)
Admitted.

Lemma impl_disj_lab_disj_lab `{redCFG} l1 l2 s p i 
      (Hpath1 : TPath' ((p,i) :< l1 :>: (s,i)))
      (Hpath2 : TPath' ((p,i) :< l2 :>: (s,i)))
      (Hdisj : Disjoint (impl_list (get_innermost_loop_strict' p) (map fst l1))
                        (impl_list (get_innermost_loop_strict' p) (map fst l2)))
  : Disjoint (map fst l1) (map fst l2).
Proof.
  (* all new members of "map fst l" are hidden in loop-headers - which are disjoint *)
Admitted.

Lemma coord_disj_impl_coord `{redCFG} l1 l2 s p i 
      (Hpath1 : TPath' ((p,i) :< l1 :>: (s,i)))
      (Hpath2 : TPath' ((p,i) :< l2 :>: (s,i)))
      (Hdisj : Disjoint l1 l2)
  : Disjoint (impl_list' p l1) (impl_list' p l2).
Admitted.

(*Lemma filter_incl `{A : Type} (l : list A) (f : A -> bool) : filter f l ⊆ l.
Proof.
  induction l;cbn;unfold "⊆";eauto.
  intros. destruct (f a);unfold In in *;firstorder.
Qed.             *)

Lemma lc_join_path_split_help2 (* unused *)`{redCFG} (p s q1 q2 : Lab) (t1 t2 : ne_list (@Coord Lab)) l1 l2 i
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


Theorem lc_join_path_split (* unused *)`{redCFG} t1 t2 (p q1 q2 s : Lab) (i j1 j2 : Tag)                          
        (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,i))
        (Hneq : q1 <> q2 \/ j1 <> j2)
        (Hpath1 : TPath' ((p,i) :<: (q1,j1) :< t1))
        (Hpath2 : TPath' ((p,i) :<: (q2,j2) :< t2))
  : exists qq qq', (s,qq,qq') ∈ path_splits__imp p.
Proof. (*
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
  rewrite ne_map_nl_rcons in Hpath1, Hpath2. cbn in *. *)
(*  destruct l1';[eapply postfix_hd_eq in Hlc0; inversion Hlc0; subst q1; cbn in *|].
  all: destruct l2';[eapply postfix_hd_eq in Hlc2; inversion Hlc2; subst q2; cbn in *|].
  - contradiction.
  - unfold map in Hpath2. rewrite nlcons_to_list in Hpath2. fold (map fst l2') in Hpath2.
    rewrite <-nercons_nlrcons in Hpath2.
    eapply lc_join_path_split_help1 in Hpath2.
    destructH.
    exists s, z, nil.

    cbn in *. eapply postfix_hd_eq in Hlc0; eapply postfix_hd_eq in Hlc2.
    inversion Hlc0; inversion Hlc2; subst; contradiction.
  - cbn in *. eapply postfix_hd_eq in Hlc0; eapply postfix_hd_eq in Hlc2. *)
Admitted. (*
  let help := lc_join_path_split_help1 in eapply help in Hpath1;eauto; eapply help in Hpath2;eauto.
  destructH. destructH.
  exists z0, z, l'0, l'.
  eapply lc_join_path_split_help2 in Hlc1;eauto.
  - split_conj;eauto;[|eapply disjoint_subset;eauto]. eapply disjoint2;eauto.
  - admit.
  - admit.
Admitted. *)

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
  : exists (qq qq' : Lab), (s,qq,qq') ∈ (splits' h e1 ++ splits' h e2).
Proof.
Admitted.

Corollary lc_disj_exit_lsplits `{redCFG} (s e q1 q2 h : Lab) (i j1 j2 k : Tag) (t1 t2 : list Coord)
          (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
          (Hexit1 : exit_edge h q1 e)
          (Hexit2 : exit_edge h q2 e)
          (Hpath1 : TPath' ((e,i) :<: (q1, j1) :< t1))
          (Hpath2 : TPath' ((e,i) :<: (q2, j2) :< t2))
  : exists (qq qq' : Lab), (s,qq,qq') ∈ splits' h e.
Proof.
  eapply lc_disj_exits_lsplits in Hlc;eauto.
  destructH. eexists;eexists. eapply in_app_or in Hlc. destruct Hlc;eauto.
Qed.

Lemma impl_list'_tpath `{C:redCFG} p i h t
      (Hpath : TPath' ((p,i) :< t))
      (Hp : deq_loop h p)
  : TPath' (C:=local_impl_CFG C h) ((impl_of_original' (or_introl Hp),i) :< impl_list' h t).
Admitted.

Lemma lc_implode_in `{redCFG} p s i k t1 t2
      (Hpath1 : TPath' ((p,i) :< t1))
      (Hpath2 : TPath' ((p,i) :< t2))
      (Hlc : last_common t1 t2 (s,k))
      (Hdep : depth p < depth s) (*TODO*)
  : exists h', loop_contains (`h') s
          /\ last_common (impl_list' p t1) (impl_list' p t2) (h', i).
Admitted.

Lemma lc_implode_out `{redCFG} p s i k t1 t2
      (Hpath1 : TPath' ((p,i) :< t1))
      (Hpath2 : TPath' ((p,i) :< t2))
      (Hlc : last_common t1 t2 (s,k))
      (Hdeq : deq_loop p s)
  : exists s', (`s') = s /\ last_common (impl_list' p t1) (impl_list' p t2) (s',k).
Admitted.

Lemma lc_cut {A : Type} `{EqDec A eq} (l1 l2 : list A) (a : A)
      (Hlc : last_common l1 l2 a)
  : exists l1' l2', last_common (l1' :r: a) (l2' :r: a) a /\ Postfix (l1' :r: a) l1 /\ Postfix (l2' :r: a) l2.
Proof.
  unfold last_common in Hlc.
  destructH.
  exists l1', l2'. split;eauto.
  unfold last_common. exists l1', l2'. split_conj;auto.
  1,2: econstructor.
Qed.

Lemma lc_same_tags `{C:redCFG} s k l1 l2 t1 t2
      (Hpost1 : Postfix (l1 :r: (s, k)) t1)
      (Hpost2 : Postfix (l2 :r: (s, k)) t2)
      (Hdisj : Disjoint l1 l2)
      p i
      (Hpath1 : TPath' ((p, i) :< t1))
      (Hpath2 : TPath' ((p, i) :< t2))
      (Heq  : eq_loop p s)
      (Hdeq : forall q, deq_loop p q)
  : forall q j, (q,j) ∈ l1 -> j = k.
Admitted.

Lemma disj_fst {A B : Type} `{EqDec A eq} `{Q:EqDec B eq} (l1 l2 : list (A * B)) k
      (Hdisj : Disjoint l1 l2)
      (Hsame1 : forall q j, (q,j) ∈ l1 -> j = k)
      (Hsame2 : forall q j, (q,j) ∈ l2 -> j = k)
  : Disjoint (map fst l1) (map fst l2).
Proof.
  eapply disjoint2. intros.
  intro Hneq. 
  enough ((x,k) = (y,k)).
  {
    revert H2. eapply disjoint2.
    - eapply Hdisj.
    - eapply in_fst in H0. destructH. replace k with b by eauto. eauto.
    - eapply in_fst in H1. destructH. replace k with b by eauto. eauto.
  }
  f_equal. auto.
Qed.

Lemma path_splits_in_imp `{C:redCFG} (p : Lab) (s q q' : local_impl_CFG_type C p)
  : let D := local_impl_CFG C p in
    let p' := (impl_of_original' (C:=C) (or_introl (deq_loop_refl (C:=C) (l:=p)))) in
    (`s,`q,`q') ∈ path_splits__imp p
    <-> (s,q,q') ∈ @path_splits _ _ _ _ D p'.
Admitted.

Lemma ex_path_splits__imp `{C:redCFG} (p : Lab) (s : local_impl_CFG_type C p)
  : (exists q q', (s, q, q') ∈ @path_splits _ _ _ _ (local_impl_CFG C p)
                       (impl_of_original' (C:=C) (or_introl (deq_loop_refl (C:=C) (l:=p)))))
    -> exists q q', (`s, q, q') ∈ path_splits__imp p.
Proof.
  intros.
  destructH.
  exists (`q), (`q'). eapply path_splits_in_imp. auto.
Qed.

Lemma pred_ndeq_exit `{redCFG} (p q : Lab)
      (Hedge : edge q p = true)
      (Hndeq : ~ deq_loop p q)
  : exists h, exit_edge h q p.
Proof.
  do 2 simpl_dec' Hndeq. destructH.
  exists x. unfold exit_edge. split_conj;eauto.
Qed.

Theorem lc_join_split `{redCFG} t1 t2 (p q1 q2 s : Lab) (i j1 j2 k : Tag)
        (* it is important to cons qj's in front of the t's *)
        (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
        (Hneq : q1 <> q2 \/ j1 <> j2)
        (Hpath1 : TPath' ((p,i) :<: (q1,j1) :< t1))
        (Hpath2 : TPath' ((p,i) :<: (q2,j2) :< t2))
  : exists qq qq', (s,qq,qq') ∈ splits p.
Proof.
  decide (deq_loop s p) as [Hdeq|Hndeq].
  decide (deq_loop p s) as [Hdeq'|Hndeq'].
  - decide (exists h, exit_edge h q1 p /\ exit_edge h q2 p) as [e|Hnexit].
    {
      destructH.
      enough (exists qq qq', exited h p /\ (s,qq,qq') ∈ splits' h p).
      { destructH. eexists; eexists. eapply splits_spec. right. left. eauto. }
      eapply lc_disj_exits_lsplits in Hlc;eauto.
      destructH. do 2 eexists.
      eapply in_app_or in Hlc.
      unfold exited.
      destruct Hlc;eauto.
    }    
    enough (exists qq qq', (s, qq, qq') ∈ path_splits__imp p).
    { destructH. eexists; eexists. eapply splits_spec. left. eauto. }    
    eapply lc_implode_out in Hlc;eauto.
    destructH.
    unfold last_common in Hlc1. destructH.
    specialize (@lc_same_tags _ _ _ _ (local_impl_CFG H p) s' k l1' l2') as Hsame.
    fold (local_impl_CFG_type H p) in *.
    specialize (Hsame _ _ Hlc2 Hlc1 Hlc3).
    replace ((p,i) :<: (q1, j1) :< t1) with ((p,i) :< ((q1,j1) :: t1)) in Hpath1 by (cbn;auto).
    eapply impl_list'_tpath in Hpath1 as Hpath1'.
    replace ((p,i) :<: (q2, j2) :< t2) with ((p,i) :< ((q2,j2) :: t2)) in Hpath2 by (cbn;auto).
    eapply impl_list'_tpath in Hpath2 as Hpath2'.
    specialize (Hsame _ i Hpath1' Hpath2').
    Unshelve. 2: { eapply deq_loop_refl. }
    exploit' Hsame. admit.
    exploit' Hsame. admit.
    assert (forall q j, (q,j) ∈ l2' -> j = k) as Hsame' by admit.

    eapply disj_fst in Hlc3;eauto.
    rewrite <-Hlc0.
    eapply ex_path_splits__imp. fold (local_impl_CFG_type H p).
    set (p' := (impl_of_original' (or_introl (deq_loop_refl (l:=p))))) in *.
    exists (ne_back (p' :< map fst l1')).
    exists (ne_back (p' :< map fst l2')).
    eapply path_splits_spec.
    unfold pl_split.
    exists (p' :< (map fst l1')), (p' :< (map fst l2')).
    split_conj;eauto.
    + eapply path_postfix_path in Hpath1';cycle 1.
      * simpl_nl. eapply postfix_cons. eapply Hlc2.
      * simpl_nl' Hpath1'. clear - Hpath1'. admit. (* some path reasoning (easy) *)
    + admit. (* as above *)
    + do 2 simpl_dec' Hnexit.
      assert (p' ∉ map fst l1') as Hnin1 by admit.
      assert (p' ∉ map fst l2') as Hnin2 by admit.
      (* because then there would be the header of p (it may be p itself) in l'
       * thus on visiting this header the tag changes -> contradiction to Hsame *)
      enough (l1' <> nil \/ l2' <> nil).
      {
        destruct H0.
        - destruct l1';[congruence|]. cbn. cbn in Hlc3.
          destruct l2';cbn.
          + contradict Hnin1. rewrite <-Hnin1. unfold map at 2. fold (map fst l1').
            rewrite nlcons_to_list. eapply in_ne_back.
          + cbn in Hlc3. intro N.
            eapply Hlc3. 1,2:rewrite nlcons_to_list. eapply in_ne_back. rewrite <-N. eapply in_ne_back.
        - admit. (* analogous *)
      }
      cbn in Hlc2,Hlc1.
      decide (deq_loop p q1) as [Hdeq1|Hndeq1]; decide (deq_loop p q2) as [Hdeq2|Hndeq2].
      -- destruct l1'.
         ++ right. intro N. subst. cbn in Hlc2, Hlc1.
            eapply2 postfix_hd_eq Hlc2 Hlc1.
            rewrite Hlc2 in Hlc1.
            clear - Hneq Hlc1. inversion Hlc1. (* this may cause problems (shelved goals), no it's somewhere else *)
            destruct Hneq; contradiction.
         ++ left. congruence.
      -- exfalso.
         eapply pred_ndeq_exit in Hndeq2 as Hexit.
         ++ destructH. eapply exit_pred_loop in Hexit as Hloop.
            ** eapply Hdeq1 in Hloop.
               unfold exit_edge in Hexit. destructH. contradiction.
            ** eapply TPath_CPath in Hpath1. cbn in Hpath1. simpl_nl' Hpath1.
               inversion Hpath1. replace b with q1 in *. eauto. destruct t1;cbn in H1; inversion H1;eauto.
         ++ eapply TPath_CPath in Hpath2. cbn in Hpath2. simpl_nl' Hpath2.
            inversion Hpath2. replace b with q2 in *. eauto. destruct t2;cbn in H1; inversion H1;eauto.
      -- admit. (* analogous *)
      -- admit.
    (* Show that p is not in l1' & l2' (possibly difficult) *)
    + simpl_nl. cbn. auto. 
  (* this gives disjoint cpaths *)
    
    
      
    
    (* k = i, bc otherwise we would visit the head of p in both traces with the same tag,
     * which contradicts Hlc *)
    (* this is not true for p being a head. 
     * instead I need something that all tags from s to p (excluding p) are equal k to *)
  - enough (exists br q q' : Lab, (br, q, q') ∈ path_splits__imp p
                             /\ (exists qq qq', (s, qq, qq') ∈ splits' br q \/ (s, qq, qq') ∈ splits' br q')).
    { destructH. exists qq, qq'. eapply splits_spec. right. right. repeat eexists.
      all: admit. (* new goals because of modification to the splits_spec *)
    }
(*    eapply lc_implode_in in Htri;cycle 2;eauto.
    + instantiate (1:=h). admit.
    + destructH. cbn in Htri1.*)
    admit.
  - simpl_dec' Hndeq. simpl_dec' Hndeq. destructH.
    decide (x = p).
    + subst. decide (deq_loop p s) as [Hdeq'|Hndeq'].
      * admit. (* Attention! special case where loop_head p *)
      * admit. 
    + exfalso.
      (* the tag k is shorter than i
       * some head has to be visited from outside on the way from s to p
       * this head has the same tag on both traces 0 :: k, contradiction to last_common *)
      admit.
      
Admitted.


(*Lemma head_diff
        (Hneq : j1 <> j2)
    : exists h, *)

Definition sub_list {A : Type} (l l' : list A) : Prop :=
  exists l1 l2, Postfix (l1 ++ l') l /\ Prefix (l ++ l2) l.  

Lemma common_tag_prefix_head (* unused *)`{redCFG} h p q i j k t
      (Hloop__p : loop_contains h p) (* what if h is root ? *)
      (Hloop__q : loop_contains h q)
      (Hdom : Dom edge root q p)
      (Hpath : TPath (root,start_tag) (p,i) t)
      (Hprec__q : Precedes fst t (q,j))
      (Hprec__h : Precedes fst t (h,k))
  : Prefix k i /\ Prefix k j.
Admitted.

(* TODO: we need a variant of this lemma where we refer to (h,i) h dominating q *)   
Lemma common_tag_prefix_qq (* unused *)`{redCFG} p q (i j1 j2 : Tag) t1 t2
      (Hdeq : deq_loop q p)
      (Hdom : Dom edge root q p)
      (Hpath1 : TPath (root,start_tag) (p,i) t1)
      (Hpath2 : TPath (root,start_tag) (p,i) t2)
      (Hprec1 : Precedes fst t1 (q,j1))
      (Hprec2 : Precedes fst t2 (q,j2))
  : exists j, Prefix j j1 /\ Prefix j j2 /\ length j = depth p.
Admitted.

Lemma common_tag_prefix_pq (* unused *)`{redCFG} p q i j t
      (Hdeq : deq_loop q p)
      (Hdom : Dom edge root q p)
      (Hpath : TPath (root,start_tag) (p,i) t)
      (Hprec : Precedes fst t (q,j))
  : Prefix i j.
Admitted.

Lemma first_sync_exit (* unused *)`{redCFG} p q l1 l2 i j1 j2 r0 i0
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
