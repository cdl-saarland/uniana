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
Lemma in_implode_CFG `{C : redCFG} (p : Lab)
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

Parameter splits'_spec
  : forall `{redCFG} h e sp, sp ∈ splits' h e
                        <-> sp ∈ loop_splits__imp h e
                          \/ exists br q q', (br,q,q') ∈ loop_splits__imp h e
                                       /\ (sp ∈ splits' br q
                                          \/ sp ∈ splits' br q').

Parameter rel_splits_spec (* unused *)
  : forall `{redCFG} p q sp, sp ∈ rel_splits p q
                        <-> exists h e, e -a>* p (* acyclic, bc. otw. path could use back_edge of outer loop *)
                                 /\ loop_contains h q
                                 /\ sp ∈ loop_splits h e.
(* sp ∈ splits' h e. <--- deprecated *)

Parameter splits_spec
  : forall `{redCFG} p sp, sp ∈ splits p
                      <-> sp ∈ path_splits__imp p (* usual split *)
                        \/ (exists h, (* lsplits of exited loops: *)
                              sp ∈ splits' h p)
                        \/ exists br q q',(br,q,q') ∈ path_splits__imp p
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

Lemma disjoint2 {A : Type} `{EqDec A} (l1 l2 : list A)
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
                             | left Q => match j with
                                          (* we only want the first occurence of the head *)
                                        | O :: j'
                                          => (impl_of_original' (h:=r) (p:=q) (or_intror Q), tl j) :: impl_list' r l
                                        | _
                                          => impl_list' r l
                                        end
                             | right Q => impl_list' r l
                             end
                 end
  end.

Definition innermost_loop' (* unused *)`{redCFG} (h p : Lab) := (loop_contains h p \/ h = root) /\ deq_loop h p.

Definition get_innermost_loop_strict' `{C : redCFG} p
  := match get_innermost_loop_strict p with
     | Some (exist _ h _) => h
     | None => root
     end.
(*
Lemma impl_list_cfg_tpath `{C : redCFG} l p i
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


(*Theorem lc_join_path_split (* unused *)`{redCFG} t1 t2 (p q1 q2 s : Lab) (i j1 j2 : Tag)                          
        (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,i))
        (Hneq : q1 <> q2 \/ j1 <> j2)
        (Hpath1 : TPath' ((p,i) :<: (q1,j1) :< t1))
        (Hpath2 : TPath' ((p,i) :<: (q2,j2) :< t2))
  : exists qq qq', (s,qq,qq') ∈ path_splits__imp p.
Proof.*) (*
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
(*
  let help := lc_join_path_split_help1 in eapply help in Hpath1;eauto; eapply help in Hpath2;eauto.
  destructH. destructH.
  exists z0, z, l'0, l'.
  eapply lc_join_path_split_help2 in Hlc1;eauto.
  - split_conj;eauto;[|eapply disjoint_subset;eauto]. eapply disjoint2;eauto.
  - admit.
  - admit.
Admitted. *)

Lemma exit_edge_dep_eq (* unused *)`{redCFG} h qe1 qe2 e1 e2
      (Hexit1 : exit_edge h qe1 e1)
      (Hexit2 : exit_edge h qe2 e2)
  : depth e1 = depth e2. 
Admitted.


Definition root' (* unused *)`(C : redCFG) := root.

Lemma impl_list'_rcons (* unused *)`(C:redCFG) r q j t
  : impl_list' r (t :r: (q,j)) =
    match decision (deq_loop r q) with
      | left H0 => impl_list' r t :r: (impl_of_original' (or_introl H0), j) 
      | in_right =>
          match decision (exists e : Lab, exited q e /\ deq_loop r e) with
          | left Q =>
              match j with
              | 0 :: _ =>  impl_list' r t :r: (impl_of_original' (or_intror Q), tl j)
              | _ => impl_list' r t
              end
          | in_right => impl_list' r t
          end
    end.
Proof.
  induction t; cbn.
  - reflexivity.
  - unfold rcons in IHt. rewrite IHt.
    destruct a as [q0 j0]. decide (deq_loop r q).
    + decide (deq_loop r q0).
      * reflexivity.
      * decide (exists e, exited q0 e /\ deq_loop r e).
        -- destruct j0.
           ++ reflexivity.
           ++ destruct n0;reflexivity.
        -- reflexivity.
    + decide (exists e, exited q e /\ deq_loop r e).
      * destruct j.
        -- decide (deq_loop r q0).
           ++ reflexivity.
           ++ decide (exists e0, exited q0 e0 /\ deq_loop r e0);reflexivity.
        -- destruct n0.
           ++ decide (deq_loop r q0).
              ** reflexivity.
              ** decide (exists e0, exited q0 e0 /\ deq_loop r e0).
                 --- destruct j0.
                     +++ reflexivity.
                     +++ destruct n1;reflexivity.
                 --- reflexivity.
           ++ reflexivity.
      * reflexivity.
Qed.
  
Lemma impl_list'_tpath `{C:redCFG} p i h t
      (Hpath : TPath' ((p,i) :< t))
      (Hp : deq_loop h p)
  : TPath' (C:=local_impl_CFG C h) ((impl_of_original' (or_introl Hp),i) :< impl_list' h t).
Proof.
  Arguments TPath : default implicits.
  Arguments TPath' : default implicits.
  rinduction t.
  - admit.
  - destruct a as [q j]. exploit H.
    {
      setoid_rewrite rcons_nl_rcons in Hpath. simpl_nl' Hpath.
      rewrite nl_cons_lr_shift in Hpath.
      unfold TPath' in Hpath. cbn in Hpath. simpl_nl' Hpath. 
      eapply path_rcons_inv in Hpath. destructH. destruct p0. destruct l; cbn in *; eapply tpath_tpath';eauto.
    }
    rewrite impl_list'_rcons.
    decide (deq_loop h q).
    + admit. (* this is easier: the successor of q is in the imploded graph, thus also in the imploded path *)
    + decide (exists e, exited q e /\ deq_loop h e);auto.
      destruct j;auto.
      destruct n0;auto.
      setoid_rewrite rcons_nl_rcons. simpl_nl.
      rewrite nl_cons_lr_shift.
      (* use path_rcons *)
      admit. (* difficult *)
  

  Arguments TPath {_ _ _ _ _}.
  Arguments TPath' {_ _ _ _ _}.
Admitted.

Lemma lc_implode_out (* unused *)`{redCFG} p s k t1 t2
      (Hpath1 : TPath' t1)
      (Hpath2 : TPath' t2)
      (Hlc : last_common t1 t2 (s,k))
      (Hdeq : deq_loop p s)
  : exists s', (`s') = s /\ last_common (impl_list' p t1) (impl_list' p t2) (s',k).
Admitted.

Lemma lc_cut (* unused *){A : Type} `{EqDec A eq} (l1 l2 : list A) (a : A)
      (Hlc : last_common l1 l2 a)
  : exists l1' l2', last_common (l1' :r: a) (l2' :r: a) a /\ Postfix (l1' :r: a) l1 /\ Postfix (l2' :r: a) l2.
Proof.
  unfold last_common in Hlc.
  destructH.
  exists l1', l2'. split;eauto.
  unfold last_common. exists l1', l2'. split_conj;auto.
  1,2: econstructor.
Qed.

Lemma lc_same_tags (* unused *)`{C:redCFG} s k l1 l2 t1 t2
      (Hpost1 : Postfix (l1 :r: (s, k)) t1)
      (Hpost2 : Postfix (l2 :r: (s, k)) t2)
      (Hdisj : Disjoint l1 l2)
      p i
      (Hpath1 : TPath' ((p, i) :< t1))
      (Hpath2 : TPath' ((p, i) :< t2))
      (Hdeq : forall q, deq_loop p q)
  : forall q j, (q,j) ∈ l1 -> j = k.
  (* if there are no headers in t1 & t2 then there can be no exits, because p is deeper than every other node,
   * and even if p is a header itself and the loop p was exited, we would need another header in t1/t2 to reach
   * p again.
   * assume there is a head h in l1, w.l.o.g. pick the latest
   * * if h is not exited in l1, then it has to occur in l2 too with the same tag, because i = i.
   * * if h is exited, then it has to be revisited, because p is in h (since it is a global sink),
   *   revisiting requires another outer header that is not left, i.e. we have the first case again.
   * contradiction
   *)

Admitted.

Lemma disj_fst (* unused *){A B : Type} `{EqDec A eq} `{Q:EqDec B eq} (l1 l2 : list (A * B)) k
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

Lemma ex_path_splits__imp (* unused *)`{C:redCFG} (p : Lab) (s : local_impl_CFG_type C p)
  : (exists q q', (s, q, q') ∈ @path_splits _ _ _ _ (local_impl_CFG C p)
                       (impl_of_original' (C:=C) (or_introl (deq_loop_refl (C:=C) (l:=p)))))
    -> exists q q', (`s, q, q') ∈ path_splits__imp p.
Proof.
  intros.
  destructH.
  exists (`q), (`q'). eapply path_splits_in_imp. auto.
Qed.

Lemma pred_ndeq_exit (* unused *)`{redCFG} (p q : Lab)
      (Hedge : edge q p = true)
      (Hndeq : ~ deq_loop p q)
  : exists h, exit_edge h q p.
Proof.
  do 2 simpl_dec' Hndeq. destructH.
  exists x. unfold exit_edge. split_conj;eauto.
Qed.

Instance subtype_EqDec (A : eqType) (P : decPred A)
  : EqDec (@subtype _ P (@decide_pred A P)) eq.
Proof.
  intros x y.
  destruct x,y. decide (x = x0). 
  - subst x0. left. eapply subtype_extensionality. cbn. reflexivity.
  - right. intro N. inversion N. contradiction.
Qed.

Lemma tcfg_graph_edge `{redCFG} q p i j
      (Hedge : tcfg_edge (q,j) (p,i) = true)
  : edge q p = true.
Proof.
  unfold tcfg_edge,tcfg_edge' in Hedge. conv_bool. firstorder.
Qed.

Lemma head_precedes_tpath (* unused *)`{C : redCFG} p h i t
      (Hpath : TPath (root,start_tag) (p,i) t)
      (Hloop : loop_contains h p)
  : exists k, Precedes fst t (h,k).
Admitted.

Lemma ex_head_zero
      (Lab : finType) (edge : Lab -> Lab -> bool) (root : Lab) (a_edge : Lab -> Lab -> bool)
      (C : redCFG edge root a_edge) (q : Lab) (j : Tag) (h : Lab) (t : ne_list Coord)
      (Hpath : TPath (root, start_tag) (q, j) t)
      (Hexit : exiting h q)
  : (h, 0 :: tl j) ∈ t.
Proof.
  (*
   * the tpath is also a cpath, thus because of dominance there is h on t
   * going backwards from (q,j), as long as we haven't visited (h, 0:: tl j) the tail of j
   * cannot be altered, the only changes possible are consing and modifying something on top of j
   * or counting down the head of j by travelling backedges. 
   * we have to ultimatively reach (h,0::tl j) because root is not in h
   *)
Admitted.

Lemma loop_tag_not_nil `{redCFG} h t
      (Hloop : loop_head h)
      (Hpath : TPath (root,start_tag) (h,nil) t)
  : False.
Admitted.

Lemma tag_tpath_backedge_in `(C : redCFG)
      (q' : Lab) (j' : Tag) (h : Lab) (n0 : nat) (j : list nat) 
      (π : ne_list Coord)
      (Hpath : Path tcfg_edge (root, start_tag) (q', j') π)
      (Hloop : loop_head h)
      (Hedge : tcfg_edge (q', j') (h, S n0 :: j) = true)
  : loop_contains h q'.
  (*
   * because h is head and has non-zero head-tag in Hedge, the incoming edge must be a backedge,
   * thus its predecessor is inside the loop.
   *)
Admitted.

Lemma tag_tpath_backedge `(C : redCFG)
      (q' : Lab) (j' : Tag) (h : Lab) (n0 : nat) (j : list nat) 
      (π : ne_list Coord)
      (Hpath : Path tcfg_edge (root, start_tag) (q', j') π)
      (Hloop : loop_head h)
      (Hedge : tcfg_edge (q', j') (h, S n0 :: j) = true)
  : j' = n0 :: j.
Proof.
  (*
   * because h is head and has non-zero head-tag in Hedge, the incoming edge must be a backedge,
   * thus the tag is as it is
   *)
Admitted.

Lemma tpath_tag_prefix_head_prec `{redCFG} h q i j π
      (Hpath : TPath (root,start_tag) (q,j) π)
      (Hin : (h, 0 :: i) ∈ π)
      (Hpre : Prefix i j)
      (Hloop : loop_contains h q)
  : exists n, Precedes fst π (h, n :: i).
Proof.
  (*
   * we have (h, 0 :: i) ∈ π and we cannot leave the loop h between this and (q,j),
   * since i is a prefix of j, j ∈ h and leaving would imply taking an outer back_edge 
   * and thus irreversibly changing i.
   * Thus the last instance of h has to have tag (n :: i) for some n (actually n = hd j)
   *)
Admitted.

Lemma impl_list'_ndeq_eq `{C : redCFG} (p q : Lab) j (h : local_impl_CFG_type C p) t
      (Hexit : exit_edge (` h) q p)
      (Hpath : TPath (root,start_tag) (q,j) t)
  : exists t', impl_list' p t = (h, tl j) :: impl_list' p t'.
Proof.
  (*
  destruct h as [h Hh]. cbn in Hexit.
  specialize (prefix_nincl_prefix (h, O :: tl j) ((q,j) :: t)) as Hpre.
  exploit Hpre. 1: admit.
  remember ((q,j) :< t) as t0.
  setoid_rewrite nlcons_to_list in Hpre at 4 5.
  setoid_rewrite <-Heqt0 in Hpre.
  set (t' := prefix_nincl (h, O :: tl j) t0) in *. clear Heqt0.
  exists t'.
  decide (deq_loop p q).
  { unfold exit_edge in Hexit. destructH. eapply d in Hexit0. contradiction. }
  assert (exited h p) as Hexit'.
  { eexists; eapply Hexit. }
  assert (loop_contains h q) as Hloop.
  { unfold exit_edge in Hexit; destructH; eauto. }
  clear n Hexit. rename Hexit' into Hexit.
  revert dependent q. revert dependent j.
  induction t0; intros; inversion Hpath; subst.
  - inversion Hpre; subst. eapply prefix_nil_nil in H1. congruence.
  - replace (ne_to_list ((q,j) :<: t0)) with ((q,j) :: t0) in Hpre. 2: cbn;reflexivity.
    inversion Hpre;subst.
    + 
    
    
    
  
  dependent induction Hpre.
  - decide (exists e, exited q e /\ deq_loop p e).
    + destruct j;[congruence|]. destruct n;[|congruence].
      cbn. f_equal.
      * f_equal. eapply subtype_extensionality. cbn. reflexivity.
      * destruct (q == q) as [?|Habs]; [|exfalso; apply Habs; reflexivity].
        destruct (O::j == O::j) as [?|Habs]; [|exfalso; apply Habs]; reflexivity.
    + exfalso. do 2 simpl_dec' n. destruct (n p).
      * contradiction. 
      * eapply H. eapply deq_loop_refl.
  - specialize (IHHpre edge root a_edge C p ). q j h Hh).
                                                        *)
  (***************)
  
  destruct h as [h Hh]. cbn in Hexit.
  specialize (prefix_nincl_prefix (h, O :: tl j) t) as Hpre.
  exploit Hpre.
  1: eapply ex_head_zero;eauto;unfold exit_edge in Hexit;eexists;eauto.
  set (t' := prefix_nincl (h, O :: tl j) t) in *.
  exists t'.
  decide (deq_loop p q).
  { unfold exit_edge in Hexit. destructH. eapply d in Hexit0. contradiction. }
  assert (exited h p) as Hexit'.
  { eexists; eapply Hexit. }
  assert (loop_contains h q) as Hloop.
  { unfold exit_edge in Hexit; destructH; eauto. }
  assert (Prefix (tl j) j) as Htag.
  { destruct j; cbn; econstructor; econstructor. }
  remember (tl j) as i. clear Heqi.
  clear n Hexit. rename Hexit' into Hexit.
  dependent induction Hpath; intros.
  - exfalso. inversion Hpre. subst. inversion H1.
  - destruct b as [q' j'].
    specialize (IHHpath p q' j' h Hh). do 3 exploit' IHHpath.
    cbn.
    decide (deq_loop p q).
    {
      exfalso. destruct Hexit as [qe Hexit]. eapply exit_not_deq;eauto.
      eapply deq_loop_trans;eauto. eapply loop_contains_deq_loop; auto.
    }
    unfold ne_to_list in Hpre. fold (ne_to_list π) in Hpre.
    decide (exists e, exited q e /\ deq_loop p e).
    + assert (h = q) as Hheq.
      {
        destructH. destruct e1 as [qe e1].
        eapply exit_edge_unique_diff_head;eauto. intro N. eapply e2 in N.
        destruct Hexit as [qe' Hexit].
        eapply exit_not_deq in Hexit; eauto.
        eapply loop_contains_deq_loop;auto.
      }
      subst h.
      destruct j.
      {
        exfalso. clear - Hpath H Hloop.
        eapply PathCons in Hpath;eauto.
        eapply loop_tag_not_nil; eauto. eapply loop_contains_loop_head;eauto.
      }
      destruct n0.
      * inversion Hpre; subst.
        -- destruct (q == q);[|congruence].
           destruct (0 :: j == 0 :: j);[|congruence].
           f_equal. f_equal. eapply subtype_extensionality. cbn. reflexivity.
        -- exfalso.
           eapply PathCons in Hpath; eauto.
           assert (i = j) as Heqij.
           {
             eapply tpath_tag_len_eq_elem in Hpath;eauto;cycle 1.
             - cbn. left. reflexivity.
             - cbn. right. eapply prefix_incl; eauto.
             - eapply prefix_length.
               + inversion Htag;eauto. rewrite H1 in Hpath. cbn in Hpath. clear - Hpath. omega.
               + cbn in Hpath. inversion Hpath. reflexivity.
           } 
           subst j.
           clear - Hpath H2.
           eapply tpath_NoDup in Hpath.
           cbn in Hpath. inversion Hpath; subst.
           eapply H1. eapply prefix_incl;eauto.
      * rewrite IHHpath.
        -- f_equal. f_equal.
           destruct (q == q). 2: reflexivity.
           destruct (O :: i == S n0 :: j). 1: congruence.
           reflexivity.
        -- eapply prefix_nincl_prefix.
           inversion Hpre. subst.
           eapply prefix_incl;eauto.
        -- auto.
        -- eapply tag_tpath_backedge_in; eauto using loop_contains_loop_head.
        -- inversion Hpre; subst. inversion Htag;subst.
           ++ exfalso.
              eapply PathCons in Hpath;eauto.
              eapply tpath_tag_len_eq_elem in Hpath;eauto;cycle 1.
              ** left. reflexivity.
              ** right. eapply prefix_incl;eauto.
              ** clear - Hpath. cbn in Hpath. omega.
           ++ assert (j' = n0 :: j) as Heqj by (eapply tag_tpath_backedge; eauto using loop_contains_loop_head).
              subst j'.
              econstructor;eauto.
    + assert (h <> q) as Hneq.
      {
        contradict n0. subst h. exists p. split;eauto using deq_loop_refl.
      }
      assert (loop_contains h q') as Hloop'.
      { eapply preds_in_same_loop;eauto. eapply tcfg_graph_edge;eauto. }
      inversion Hpre; [contradiction|subst]. 
      rewrite IHHpath;auto.
      * f_equal. f_equal.
        destruct (h == q). 2: reflexivity.
        destruct (O :: i == j). 2: reflexivity.
        exfalso. eapply n0. exists p. rewrite <-e. split;eauto using deq_loop_refl.
      * eapply prefix_nincl_prefix. eapply prefix_incl;eauto.
      * clear - Hloop Hloop' H Hpath Htag H2 Hneq.
        assert (exists n, Precedes fst π (h, n :: i)).
        {
          eapply PathCons in Hpath; eauto. eapply tpath_tag_prefix_head_prec in Hpath;cycle 1;eauto.
          - right. eapply prefix_incl;eauto.
          - destructH. exists n. inversion Hpath;subst;[contradiction|eauto].
        }
        destructH.
        eapply tag_prefix_head in H0; eauto. eapply prefix_cons;eauto.
Qed.
  (*  
  induction l2'; intros.
  - unfold app in Hpre. inversion Hpre. subst h.
    decide (exists e, exited q e /\ deq_loop p e).
    + destruct j;[congruence|]. destruct n;[|congruence].
      cbn. f_equal.
      f_equal. eapply subtype_extensionality. cbn. reflexivity.
      (* destruct (q == q) as [?|Habs]; [|exfalso; apply Habs; reflexivity].
        destruct (O::j == O::j) as [?|Habs]; [|exfalso; apply Habs]; reflexivity.*)
    + exfalso. do 2 simpl_dec' n. destruct (n p).
      * contradiction. 
      * eapply H. eapply deq_loop_refl.
  - unfold app in Hpre. fold (l2' ++ (h, 0 :: tl j) :: t') in Hpre. inversion Hpre.
    subst a.
    specialize (IHl2' (tl t) j q).
    exploit IHl2'.
    { destruct t; cbn;[congruence'|].
      
    decide (exists e, exited q e /\ deq_loop p e).
    + destruct j;[admit|]. (* contradiction: q is a header with tag [] *)
      destruct n.
      * exfalso.
        assert (h = q) as Hheq.
        {
          destructH. destruct e1 as [qe e1].
          eapply exit_edge_unique_diff_head;eauto. intro N. eapply e2 in N.
          destruct Hexit as [qe' Hexit].
          eapply exit_not_deq in Hexit; eauto.
          eapply loop_contains_deq_loop;auto.
        }
        rewrite H1 in Hpath. unfold tl in Hpath.
        subst h. clear - Hpath.
        eapply tpath_NoDup in Hpath.
        simpl_nl' Hpath.
        replace ((q, 0 :: j) :: _) with (((q, 0 :: j) :: l2') ++ (q, 0 :: j) :: t') in Hpath.
        2: cbn; eauto.
        eapply NoDup_app in Hpath.
        -- eapply Hpath. left. auto.
        -- left. auto.
      * admit. (* header visited but not the first time: here we should use IH *)
    + admit. (* some other node visited: here we should use IH *)
Admitted.*)

Lemma postfix_impl_list' (* unused *)`{redCFG} p q s i j k t l
      (Hpath : TPath (root,start_tag) (p,i) ((p,i) :< ((q,j) :: t)))
      (Hpost : Postfix (l :r: (s,k)) (impl_list' p ((q,j) :: t)))
      (Hndeq : ~ deq_loop p q)
  : exists h, exit_edge (`h) q p /\ exists t', Postfix (l :r: (s,k)) ((h,tl j) :: impl_list' p t').
Proof.
  do 2 simpl_dec' Hndeq. destructH.
  cbn in Hpath. inversion Hpath.
  replace b with (q,j) in * by (destruct t; inversion H1; subst; eauto).
  enough (exit_edge x q p).
  {
    assert (implode_nodes (head_exits_CFG H p) p x).
    - right. exists p. split;[|eapply deq_loop_refl].
      eapply head_exits_exited_inv1. eexists;eauto.
    - cstr_subtype H6. set (h':=(↓ purify H6)) in *.
      exists h'. destruct h' as [h Hh]. split;[auto|].
      cbn in Hndeq0,Hndeq1.
      eapply (impl_list'_ndeq_eq) in H5. 2: cbn;eauto.
      destructH. exists t'. simpl_nl' H5. setoid_rewrite H5 in Hpost. eauto.
  }
  eapply tcfg_graph_edge in H4. unfold exit_edge. split_conj; eauto.
Qed.

Lemma impl_deq_loop (* unused *)`{C : redCFG} (p q r : Lab) (p' q' : local_impl_CFG_type C r)
      (Heqp : p = `p')
      (Heqq : q = `q')
      (Hdeq : deq_loop (C:=C) p q)
  : deq_loop (C:=local_impl_CFG C r) p' q'.
Proof.
  destruct p' as [p' Hp]; destruct q' as [q' Hq]. push_purify Hp;push_purify Hq. rename H into Hp;rename H0 into Hq.
  cbn in Heqp,Heqq, Hp, Hq. subst p' q'. intro. intro.
Admitted.

Lemma impl_deepest_node (* unused *)`{C : redCFG} p
      (p' q : local_impl_CFG_type C p)
      (Hdeqp : p = `p')
  : deq_loop (C:=local_impl_CFG C p) p' q.
Proof.
  destruct q as [q Q]. eapply pure_equiv in Q as Hq.
  destruct Hq.
  - eapply impl_deq_loop; eauto. cbn.
    eapply head_exits_deq_loop_inv2. eauto.
  - admit.
Admitted.

Lemma p_not_in (* unused *)`{C : redCFG} (p s : Lab) (i j k : Tag) (t l : list Coord)
      (Hpath1' : TPath' ((p, i) :< t))
      (Hpost : Postfix (l :r: (s, k)) t)
      (Hsame : forall q j, (q, j) ∈ l -> j = k)
      (Hdeq : eq_loop p s \/ loop_head p)
  : p ∉ map fst l.
  (* maybe not true *)
Admitted.

Lemma impl_list'_tpath1 (* unused *)`{C : redCFG} (p q : Lab) (i j : Tag) t
      (Hpath : TPath (root, start_tag) (p, i) ((p, i) :<: (q, j) :< t))
  : TPath' (C:=local_impl_CFG C p)
           ((impl_of_original' (or_introl (deq_loop_refl (l:=p))), i) :< impl_list' p ((q, j) :: t)).
Proof.
  replace ((p,i) :<: (q, j) :< t) with ((p,i) :< ((q,j) :: t)) in Hpath by (cbn;auto).
  eapply tpath_tpath' in Hpath.
  eapply impl_list'_tpath;eauto.
Qed.

Definition last_common' (A : Type) `{EqDec A eq} (l1 l2 l1' l2' : list A) (s : A)
  := Postfix (l1' :r: s) l1 /\ Postfix (l2' :r: s) l2 /\ Disjoint l1' l2' /\ s ∉ l1' /\ s ∉ l2'.

Lemma last_common'_iff (A : Type) `(EqDec A eq) l1 l2 (a : A)
  : last_common l1 l2 a <-> exists l1' l2', last_common' l1 l2 l1' l2' a.
Proof.
  unfold last_common, last_common' in *. firstorder.
Qed.

Ltac swap_names H Q :=
  let R := fresh "R" in
  rename H into R;
  rename Q into H;
  rename R into Q.

Lemma lc_join_path_split' `{H : redCFG}
      (t1 t2 : list (Lab * Tag))
      (p q1 q2 : Lab)
      (i j1 j2 k : Tag)
      (Hneq : q1 <> q2)
      (Hpath1 : TPath (root, start_tag) (p, i) ((p, i) :<: (q1, j1) :< t1))
      (Hpath2 : TPath (root, start_tag) (p, i) ((p, i) :<: (q2, j2) :< t2))
      (Hnexit : ~ (exists h : Lab, exit_edge h q1 p /\ exit_edge h q2 p))
      (s' : local_impl_CFG_type H p)
      (l1' l2' : list (local_impl_CFG_type H p * Tag))
      (Hlc : last_common' (impl_list' p ((q1, j1) :: t1)) (impl_list' p ((q2, j2) :: t2)) l1' l2' (s',k))
      (p' := (impl_of_original' (or_introl (deq_loop_refl (l:=p)))))
  : (` s', ` (ne_back (p' :< map fst l1')), ` (ne_back (p' :< map fst l2'))) ∈ path_splits__imp p.
Proof.
  specialize (@lc_same_tags _ _ _ _ (local_impl_CFG H p) s' k l1' l2') as Hsame.
  fold (local_impl_CFG_type H p) in *.
  unfold last_common' in Hlc. destructH. swap_names Hlc2 Hlc1.
  specialize (Hsame _ _ Hlc0 Hlc1 Hlc2).
  eapply impl_list'_tpath1 in Hpath1 as Hpath1'.
  eapply impl_list'_tpath1 in Hpath2 as Hpath2'.
  specialize (Hsame _ _ Hpath1' Hpath2').
  exploit' Hsame.
  {
    intros.
    eapply impl_deepest_node. cbn;eauto.
  }
  assert (forall q j, (q,j) ∈ l2' -> j = k) as Hsame' by admit. (* analogous *)
  eapply disj_fst in Hlc2;eauto.
  destruct s' as [s Hs].
  rewrite path_splits_in_imp.
  eapply path_splits_spec.
  unfold pl_split.
  exists (p' :< (map fst l1')), (p' :< (map fst l2')).
  set (s' := (↓ Hs)) in *.
  split_conj;eauto.
  + eapply path_postfix_path in Hpath1';cycle 1.
    * simpl_nl. eapply postfix_cons. eapply Hlc0.
    * simpl_nl' Hpath1'. clear - Hpath1' s'. simpl_nl' Hpath1'.
      replace (ne_back _) with (s',k) in Hpath1'.
      -- rewrite <-nl_cons_lr_shift. rewrite rcons_nl_rcons in Hpath1'. simpl_nl' Hpath1'.
         eapply TPath_CPath in Hpath1'. cbn in Hpath1'. rewrite ne_map_nl_rcons in Hpath1'.
         cbn in Hpath1'. exact Hpath1'.
      -- rewrite rcons_nl_rcons. simpl_nl. rewrite nl_cons_lr_shift. simpl_nl. reflexivity.
  + admit. (* analogous *)
  + do 2 simpl_dec' Hnexit.

          
    assert (p' ∉ map fst l1') as Hnin1 by admit.
(*    {
      eapply (p_not_in (C:=local_impl_CFG H p));cycle 2;eauto;left.
      split;cbn in Hdeq;eauto using impl_deq_loop,impl_deepest_node.
    }*)
    assert (p' ∉ map fst l2') as Hnin2 by admit.
(*    {
      eapply (p_not_in (C:=local_impl_CFG H p));cycle 2;eauto;left.
      split;cbn in Hdeq;eauto using impl_deq_loop,impl_deepest_node.
    } *)
    (* because then there would be the header of p (it may be p itself) in l'
     * thus on visiting this header the tag changes -> contradiction to Hsame *)
    enough (l1' <> nil \/ l2' <> nil).
    {
      destruct H0.
      - destruct l1';[congruence|]. cbn. cbn in Hlc3.
        destruct l2';cbn.
        + contradict Hnin1. rewrite <-Hnin1. unfold map at 2. fold (map fst l1').
          rewrite nlcons_to_list. eapply in_ne_back.
        + cbn in Hlc2. intro N.
          eapply Hlc2. 1,2:rewrite nlcons_to_list. eapply in_ne_back. rewrite <-N. eapply in_ne_back.
      - admit. (* analogous *)
        Unshelve. all: eauto;clear.
        1,2: intros x y; destruct x,y; decide (x = x0);
          [subst x0; left; eapply subtype_extensionality; cbn; reflexivity
          |right; intro N; inversion N; contradiction].
    }
    copy Hlc0 Hlc0'. copy Hlc1 Hlc1'.
    cbn in Hlc0,Hlc1.
    assert (edge q1 p = true) as Hedge1.
    {
      eapply TPath_CPath in Hpath1. cbn in Hpath1. simpl_nl' Hpath1.
      inversion Hpath1. replace b with q1 in *. eauto. destruct t1;cbn in H1; inversion H1;eauto.
    }
    assert (edge q2 p = true) as Hedge2.
    {
      eapply TPath_CPath in Hpath2. cbn in Hpath2. simpl_nl' Hpath2.
      inversion Hpath2. replace b with q2 in *. eauto. destruct t2;cbn in H1; inversion H1;eauto.
    }
    decide (deq_loop p q1) as [Hdeq1|Hndeq1]; decide (deq_loop p q2) as [Hdeq2|Hndeq2].
    -- destruct l1'.
       ++ right. intro N. subst. cbn in Hlc0, Hlc1.
          eapply2 postfix_hd_eq Hlc0 Hlc1.
          rewrite Hlc0 in Hlc1.
          clear - Hneq Hlc1. inversion Hlc1. 
          contradiction.
       ++ left. congruence.
    -- exfalso.
       eapply pred_ndeq_exit in Hndeq2 as Hexit;auto.
       destructH. eapply exit_pred_loop in Hexit as Hloop;[|eapply Hedge1].
       eapply Hdeq1 in Hloop.
       unfold exit_edge in Hexit. destructH. contradiction.
    -- admit. (* analogous *)
    -- (*assert (q1 <> q2) as Hneqq.
         {
           clear - Hndeq1 Hnexit Hedge1.
           intro N.
           subst q2. eapply pred_ndeq_exit in Hndeq1;eauto.
           destructH. destruct (Hnexit h);contradiction.
         }*)
      clear Hlc1 Hlc0.
      eapply postfix_impl_list' in Hlc0';eauto. 
      eapply postfix_impl_list' in Hlc1';eauto. 
      do 2 destructH.
      destruct l1'.
      ++ right. intro N. subst. cbn in Hlc0'1, Hlc1'1.
         eapply2 postfix_hd_eq Hlc0'1 Hlc1'1.
         rewrite Hlc0'1 in Hlc1'1.
         clear - Hneq Hlc1'1 Hlc1'0 Hlc0'0 Hnexit. inversion Hlc1'1.
         subst h0. destruct h as [h Hh]. cbn in Hlc1'0,Hlc0'0. destruct (Hnexit h);contradiction.
      ++ left. congruence.
  + simpl_nl. cbn. auto. 
Admitted.

Lemma lc_join_path_split (* unused *)`{H : redCFG}
      (t1 t2 : list (Lab * Tag))
      (p q1 q2 : Lab)
      (i j1 j2 k : Tag)
      (Hneq : q1 <> q2)
      (Hpath1 : TPath (root, start_tag) (p, i) ((p, i) :<: (q1, j1) :< t1))
      (Hpath2 : TPath (root, start_tag) (p, i) ((p, i) :<: (q2, j2) :< t2))
      (Hnexit : ~ (exists h : Lab, exit_edge h q1 p /\ exit_edge h q2 p))
      (s' : local_impl_CFG_type H p)
      (Hlc : last_common (impl_list' p ((q1, j1) :: t1)) (impl_list' p ((q2, j2) :: t2)) (s', k))
  :
    exists qq qq' : Lab, (` s', qq, qq') ∈ path_splits__imp p.
Proof.
  rewrite last_common'_iff in Hlc. destructH.
  eapply lc_join_path_split' in Hlc;eauto.
Qed.

Lemma lc_sub (* unused *){A : Type} `{EqDec A eq} (l1 l2 l1' l2' ll1 ll2 : list A) s
      (Hpost1 : Postfix (l1' :r: s) l1)
      (Hpost2 : Postfix (l2' :r: s) l2)
      (Hdisj : Disjoint l1' l2')
      (Hnin1 : s ∉ l1')
      (Hnin2 : s ∉ l2')
      (Hpre1 : Prefix ll1 l1')
      (Hpre2 : Prefix ll2 l2')
  : last_common (ll1 :r: s) (ll2 :r: s) s.
Proof.
  exists ll1, ll2. split_conj.
  1,2: econstructor.
  all: eapply prefix_incl in Hpre1; eapply prefix_incl in Hpre2.
  2,3: firstorder.
  1: eapply disjoint_subset;eauto.
Qed.

Lemma lc_continue (* unused *){A : Type} `{EqDec A eq} (l1 l2 l1' l2' : list A) s
      (Hpost1 : Postfix (l1' :r: s) l1)
      (Hpost2 : Postfix (l2' :r: s) l2)
      (Hlc : last_common (l1' :r: s) (l2' :r: s) s)
  : last_common l1 l2 s.
Proof.
  unfold last_common in Hlc.
  destructH.
  exists l1'0, l2'0. split_conj; eauto.
  1,2: eapply postfix_trans;eauto.
Qed.

Lemma lc_implode_in (* unused *)`{redCFG} p s qj1 qj2 k t1 t2
      (Hpath1 : TPath (root,start_tag) qj1 t1)
      (Hpath2 : TPath (root,start_tag) qj2 t2)
      (Hlc : last_common t1 t2 (s,k))
      (Hndeq : ~ deq_loop p s)
  : exists h' j, loop_contains (`h') s
          /\ last_common (impl_list' p t1) (impl_list' p t2) (h', j). (* j is the prefix of k of length |k| *)
Admitted.


Definition edge' `(C : redCFG) := edge.

Lemma head_exit_in_impl (* unused *)`{C : redCFG} (p q h : Lab) (h' q' : local_impl_CFG_type C p)
      (Hloop : loop_head h)
      (Hh : h = ` h')
      (Hq : q = ` q')
      (Hedge : edge' (local_impl_CFG C p) h' q' = true)
  : exited h q.
  
    (* h is a head in the original graph, and qq is a successor of h in the imploded graph, 
     * thus qq is a an exit of h in the original graph
     *)
Admitted.

Lemma ne_back_map_in (* unused *){A B : Type} `{EqDec A eq} (p : A) (i : B) l
      (q := ne_back (p :< map fst l) : A)
  : exists j, (q,j) ∈ ((p,i) :: l).
Proof.
  destruct l.
  - cbn. exists i. eauto.
  - cbn in q. assert (q ∈ map fst (p0 :: l)).
    + subst q.
      rewrite <-ne_map_nlcons.
      rewrite nlcons_to_list.
      rewrite to_list_ne_map.
      eapply in_ne_back.
    + eapply in_fst in H0. destructH. exists b.
      right. eauto.
Qed.

Lemma impl_list'_incl (* unused *)`{C : redCFG} p q j t
      (Hdeq : deq_loop p (` q))
      (Hin : (q,j) ∈ impl_list' p t)
  : (` q,j) ∈ t.
Admitted.

Lemma rcons_prefix (* unused *){A : Type} (l l' : list A) (a b : A)
      (Hpre : Prefix (l :r: a) (l' :r: b))
  : Prefix l l'.
Proof.
  eapply prefix_rev_postfix in Hpre.
  do 2 rewrite rev_rcons in Hpre. eapply cons_postfix in Hpre.
  eapply postfix_rev_prefix'. eauto.
Qed.

Lemma prefix_back_eq (* unused *){A : Type} (l l' : list A) (a b : A)
      (Hpre : Prefix (l :r: a) (l' :r: b))
  : a = b.
Proof.
  eapply postfix_hd_eq.
  eapply prefix_rev_postfix'.
  cbn. instantiate (1:=rev l'). instantiate (1:=rev l).
  do 2 rewrite rev_involutive. eauto.
Qed.

Lemma in_cons_succ_in_rcons (* unused *){A : Type} (a b c : A) l
      (Hin : c ∈ (b :: l))
  : exists d, c ≻ d | b :: l :r: a.
Proof.
  revert a.
  rinduction l.
  - cbn. exists a. exists nil, nil. cbn. inversion Hin; subst; [|contradiction]. reflexivity.
  - rewrite <-cons_rcons_assoc in Hin. eapply In_rcons in Hin. destruct Hin.
    + subst. exists a0. exists nil, (b :: l0). cbn. f_equal. clear. induction l0; cbn; eauto. f_equal. eauto.
    + exploit' H. specialize (H a). destructH. exists d. destruct H as [l2 [l1 H]].
      exists (l2 :r: a0), l1. rewrite <-cons_rcons_assoc. rewrite H. 
      clear.
      induction l1;cbn;eauto. f_equal. unfold rcons in IHl1. rewrite IHl1. reflexivity.
Qed.

Lemma path_nlrcons_edge (* unused *){A : Type} (a b c : A) l f
      (Hpath : Path f b c (l :>: a))
  : f a (ne_back l) = true.
Proof.
  revert dependent c.
  induction l; intros; inversion Hpath; subst; cbn in *.
  - inversion H3. subst b0 b a1. auto.
  - eauto.
Qed.

Lemma exits_eq_loop `{C:redCFG} q1 q2 h
      (Hexit1 : exited h q1)
      (Hexit2 : exited h q2)
  : eq_loop q1 q2.
Proof.
  revert q1 q2 h Hexit1 Hexit2.
  enough (forall q1 q2 h : Lab, exited h q1 -> exited h q2 -> deq_loop q1 q2).
  { intros. split; eauto. }
  intros.
  decide (deq_loop q1 q2);[auto|].
  exfalso.
  
Admitted.

Lemma exited_deq_p (* unused *)`{C:redCFG} p q (h : local_impl_CFG_type C p)
      (Hexit : exited (` h) q)
  : deq_loop p q.
Proof.
  destruct h.
  eapply pure_equiv in p0 as p0'.
  destruct p0'. destruct Hexit as [qe Hexit].
  - cbn in *. eapply deq_loop_exited' in Hexit.
    eapply head_exits_deq_loop_inv2 in H.
    eapply deq_loop_trans;eauto.
  - destructH. cbn in *.
    eapply exits_eq_loop in Hexit. 2: { eapply head_exits_exited_inv2. eauto. }
    eapply eq_loop2;eauto. eapply head_exits_deq_loop_inv2. eauto.
Qed.

Lemma postfix2_impl_list'_incl (* unused *)`{C:redCFG}
      (l : list Coord) (t : ne_list Coord) (p : Lab) (q : local_impl_CFG_type C p) j x
      (l' : list (local_impl_CFG_type C p * Tag))
      (x' : local_impl_CFG_type C p * Tag)
      (Hpath : TPath' t)
      (Hpost : Postfix (l :r: x) t)
      (Hpost' : Postfix (l' :r: x') (impl_list' p t))
      (Hdeq : deq_loop p (` q))
      (Hin : (q,j) ∈ l')
  : (` q,j) ∈ l.
Admitted.

Lemma post_prefix_cut (* unused *){A : Type} (l0 l1 l2 l3 : list A)
      (Hnd : NoDup l0)
      (Hpost : Postfix l1 l0)
      (Hpre : Prefix l2 l1)
      (Hpre' : Prefix l3 l0)
      (Heq : hd_error l2 = hd_error l3)
  : Postfix l2 l3.
Admitted.

Ltac nl_eapply H :=
  first [eapply H | rewrite !nlcons_to_list; eapply H | simpl_nl; eapply H].
Ltac nl_eapply' H Q :=
  first [eapply H in Q | rewrite !nlcons_to_list in Q; eapply H in Q | simpl_nl' Q; eapply H in Q].

Ltac subst_path_fb H :=
  match type of H with
  | Path _ _ ?b (?a :< ?t) =>
    replace b with a in *;
    [|destruct t; cbn in H; inversion H; subst; eauto]
  | Path _ ?b _ (?t >: ?b) =>
    idtac "not implemented"
  end.

Lemma deq_leq_depth (* unused *)`(redCFG) p q
      (Hdeq : deq_loop p q)
  : depth q <= depth p.
Admitted.

Lemma lc_in_loop (* unused *)`{C: redCFG} (q1 q2 s h : Lab) (j1 j2 k : Tag) (t1 t2 : list Coord)
      (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
      (Hloop1 : loop_contains h q1)
      (Hloop2 : loop_contains h q2)
  : loop_contains h s.
Proof.
Admitted.

Lemma depth_leq_deq (* unused *)`(H : redCFG) (s h : Lab)
      (Hloop : loop_contains h s)
      (Hdep : depth s <= depth h)
  : deq_loop h s.
Proof.
Admitted.

Fixpoint while' {A : Type} (P : decPred A) (l : list A) : list A
  := match l with
     | nil => nil
     | a :: l => if decision (P a) then a :: while' P l else nil
     end.

Definition while {A : Type} (P : decPred A) (l : list A) : list A
  := rev (while' P (rev l)).

Lemma while'_postfix {A : Type} (P : decPred A) (l l' : list A)
      (H : while' P l = l')
  : Postfix l' l.
Proof.
  revert dependent l'.
  induction l; intros; cbn in *; eauto.
  - subst. constructor.
  - decide (P a).
    + destruct l';[congruence|]. inversion H; subst.
      eapply postfix_cons. eapply IHl. reflexivity.
    + subst. eapply postfix_nil.
Qed.

Lemma while_prefix (* unused *){A : Type} (P : decPred A) (l l' : list A)
      (H : while P l = l')
  : Prefix l' l.
Proof.
  eapply postfix_rev_prefix'.
  unfold while in H. rewrite <-H.
  rewrite rev_involutive.
  eapply while'_postfix;eauto.
Qed.
  
Lemma while'_Forall {A : Type} (P : decPred A) (l : list A)
  : Forall P (while' P l).
Proof.
  induction l;cbn;eauto.
  decide (P a).
  - econstructor;eauto.
  - econstructor.
Qed.
  
Lemma while_Forall {A : Type} (P : decPred A) (l : list A)
  : Forall P (while P l).
Proof.
  unfold while. rewrite Forall_forall. setoid_rewrite <-in_rev. rewrite <-Forall_forall.
  eapply while'_Forall.
Qed.

Lemma while'_app {A : Type} (P : decPred A) (l l' : list A)
      (H : Forall P l)
  : while' P (l ++ l') = l ++ while' P l'.
Proof.
  induction l;cbn;auto.
  inversion H;subst. exploit IHl.
  decide (P a);[|contradiction]. rewrite IHl. auto.
Qed.

Lemma while'_max {A : Type} (P : decPred A) (l l' : list A) a
      (Hpost : Postfix (l' :r: a) l)
      (Hw : while' P l = l')
  : ~ P a.
Proof.
  rewrite postfix_eq in Hpost.
  destructH.
  rewrite Hpost in Hw.
  intro N. rewrite while'_app in Hw.
  - clear - Hw. induction l';cbn in Hw;[congruence|]. eapply IHl'. inversion Hw. rewrite H0 at 1. reflexivity.
  - rewrite Forall_forall. setoid_rewrite In_rcons. intros. destruct H;subst;auto.
    eapply Forall_forall in H;eauto. rewrite <-Hw.
    eapply while'_Forall.
Qed.
    
  
Lemma while_max (* unused *){A : Type} (P : decPred A) (l l' : list A) a
      (Hpre : Prefix (a :: l') l)
      (Hw : while P l = l')
  : ~ P a.
Proof.
  unfold while in Hw.
  rewrite <-rev_involutive in Hw. eapply rev_injective in Hw.
  eapply while'_max;eauto.
  rewrite <-rev_cons. eapply prefix_rev_postfix;eauto.
Qed.

Lemma exit_impl (* unused *)`{C : redCFG} {h qe e}
      (Hexit : exit_edge h qe e)
  : local_impl_CFG_type C h.
Proof.
  econstructor.
  Unshelve. 2: exact e.
  eapply purify.
  left. eapply head_exits_deq_loop_inv1. eapply deq_loop_exited';eauto.
Qed.

Lemma disj_path_loop_split (* unused *)`{C : redCFG} h q1 q2 e1 e2 i j1 j2 k t1 t2 s' l1' l2'
      (Hexit1 : exit_edge h q1 e1)
      (Hexit2 : exit_edge h q2 e2)
      (Hpath1 : TPath (root, start_tag) (e1, i) ((e1, i) :<: (q1, j1) :< t1))
      (Hpath2 : TPath (root, start_tag) (e2, i) ((e2, i) :<: (q2, j2) :< t2))
      (Hlc : last_common' (impl_list' h ((q1, j1) :: t1)) (impl_list' h ((q2, j2) :: t2)) l1' l2' (s', k))
      (Hsame1 : Forall (fun qj => snd qj = k) l1')
      (Hsame2 : Forall (fun qj => snd qj = k) l2')
  : exists qq qq' : Lab, (` s', qq, qq') ∈ loop_splits__imp h e1 \/ (` s', qq, qq') ∈ loop_splits__imp h e2.
Admitted.

Lemma while_Forall_eq (* unused *){A : Type} (P : decPred A) (l l' : list A)
      (Heq : while P l = l')
  : Forall (predicate P) l'.
Proof.
  specialize (while_Forall P l) as Hwf.
  rewrite Heq in Hwf; auto.
Qed.

Lemma while_first_nsat (* unused *){A : Type} (P : decPred A) (l : list A) (b : A)
      (l' := while P (b :: l))
      (Hpre : Prefix l' l)
  : exists a, Prefix (a :: l') (b :: l) /\ ~ P a.
Admitted.

Lemma disj_exits_loop_split (* unused *)`{C : redCFG}
      h h' q1 q2 e1 e2 j j1 j2 i k t1 t2 (l1' l2' l2'' : list (local_impl_CFG_type C h * Tag))
      (Hexit1 : exit_edge h q1 e1)
      (Hpath1 : TPath (root, start_tag) (e1, i) ((e1, i) :<: (q1, j1) :< t1))
      (Hpath2 : TPath (root, start_tag) (e2, i) ((e2, i) :<: (q2, j2) :< t2))
      (s' : local_impl_CFG_type C h)
      (Hlc : last_common' (impl_list' h ((q1, j1) :: t1)) (impl_list' h ((q2, j2) :: t2)) l1' l2' (s', k))
      (k_tagged := DecPred (fun qj : local_impl_CFG_type C h * Tag => snd qj = k)
                   : decPred (local_impl_CFG_type C h * Tag))
      (Hpre : Prefix ((h',j) :: l2'') l2')
      (Hneq : j <> k)
      (H0 : Forall k_tagged l1')
      (H1 : Forall k_tagged l2'')
  : exists qq qq' : Lab, (` s', qq, qq') ∈ loop_splits__imp h e1 \/ (` s', qq, qq') ∈ loop_splits__imp h e2.
Admitted.

Lemma Disjoint_sym {A : Type} (l l' : list A)
      (Hdisj : Disjoint l l')
  : Disjoint l' l.
Proof.
  unfold Disjoint in *.
  firstorder.
Qed.

Lemma last_common'_sym (* unused *){A : Type} `{EqDec A eq} (l1 l2 l1' l2' : list A) (a : A)
      (Hlc : last_common' l1' l2' l1 l2 a)
  : last_common' l2' l1' l2 l1 a.
Proof.
  unfold last_common' in *. destructH.
  split_conj;eauto.
  eapply Disjoint_sym. auto.
Qed.

Lemma lc_disj_exits_lsplits_base (* unused *)`{C : redCFG}
      (k : Tag) (e1 e2 q1 q2 h : Lab) (i j1 j2 : Tag) (t1 t2 : list Coord)
      (Hexit1 : exit_edge h q1 e1)
      (Hexit2 : exit_edge h q2 e2)
      (Hpath1 : TPath (root, start_tag) (e1, i) ((e1, i) :<: (q1, j1) :< t1))
      (Hpath2 : TPath (root, start_tag) (e2, i) ((e2, i) :<: (q2, j2) :< t2))
      (s' : local_impl_CFG_type C h)
      (l1' l2' : list (local_impl_CFG_type C h * Tag))
      (Hlc : last_common' (impl_list' h ((q1, j1) :: t1)) (impl_list' h ((q2, j2) :: t2)) l1' l2' (s', k))
  : 
    exists qq qq' : Lab, (` s', qq, qq') ∈ loop_splits__imp h e1 \/ (` s', qq, qq') ∈ loop_splits__imp h e2.
(* we need the information that qq ≻ sk in (q1,j1)::t1 etc *)
Proof.
  pose (k_tagged := DecPred (fun qj : local_impl_CFG_type C h * Tag => snd qj = k)).
  assert (Prefix (while k_tagged l1') l1') as Hlk1 by (eapply while_prefix;eauto).
  assert (Prefix (while k_tagged l2') l2') as Hlk2 by (eapply while_prefix;eauto).
  inversion Hlk1; subst l; inversion Hlk2; subst l.
  - eapply disj_path_loop_split;eauto.
    all: eapply while_Forall_eq in H0; eapply while_Forall_eq in H1;auto. (* two exit paths *)
  - eapply while_Forall_eq in H0.
    eapply while_first_nsat in H. destructH. destruct a0.
    cbn in H3. 
    eapply disj_exits_loop_split. 5: eapply H1. all:eauto. 1: rewrite H2;eauto.
    eapply while_Forall. (* one exit & one ledge *)
  - eapply while_Forall_eq in H2.
    eapply while_first_nsat in H. destructH. destruct a0.
    cbn in H3.
    enough (exists qq qq' : Lab, (` s', qq, qq') ∈ loop_splits__imp h e2 \/ (` s', qq, qq') ∈ loop_splits__imp h e1) as Q.
    { clear - Q. destructH. exists qq, qq'. destruct Q; [right|left]; auto. }   
    eapply disj_exits_loop_split. 5: eapply H0. 4:rewrite H1;eapply last_common'_sym;eauto. all:eauto.
    eapply while_Forall.
  - exfalso. admit. (* contradiction: h is in both traces ! *)
        
  (*
   * l1' & l2' ⊂ h.
   * show that either l1' or l2' (wlog l1') is equally tagged and let ll2 be the equally tagged prefix of l2.
   * the last node in ll2 must be in h, for the tag change there are three possible cases:
     - visiting an inner loop -> not possible, because there are none (implosion)
     - visiting h again: now we have ll2 is a path to the ledge, while l1' is a path to the exit, they're l-disjoint
     - exiting h: now we have to l-disjoint paths to exits. They both have a path to the ledge (l1'' l2''.
       assume l1'' ∩ l2' and l1' ∩ l2'' are non-empty: then there is an undeclared loop -> contradiction.
       thcus wlog l1'' ++ l1' is disjoint to l2', one is an path to the ledge the other to an exit. 
   *)
Admitted.

Notation "t 'is' x -->ᵀ y" := (TPath x y t) (at level 70).

(*Lemma head_zero_in_tpath `{redCFG} t h p i
      (Hpath : TPath (root,start_tag) (p,i) t)
      (Hloop : innermost_loop h p)
  : (h,0 :: tl i) ∈ t.
*)

Lemma eq_loop_innermost `{redCFG} h p q
      (Heq : eq_loop p q)
      (Hinner : innermost_loop h p)
  : innermost_loop h q.
Proof.
  unfold innermost_loop in *.
  destructH.
  split;[eapply Heq in Hinner0;auto|]. 
  unfold eq_loop in Heq. destructH.
  eapply deq_loop_trans;eauto.
Qed.

Lemma lc_succ_rt1 {A : Type} `{EqDec A eq} l1 l2 l1' l2' (x y : A)
      (Hlc : last_common' l1 l2 l1' l2' x)
      (Hin : y ∈ l1')
  : y ≻* x | l1.
Proof.
  unfold last_common' in Hlc. destructH.
  eapply splinter_postfix;eauto.
  eapply splinter_rev. cbn. rewrite rev_rcons. econstructor. econstructor.
  eapply splinter_single. rewrite <-In_rev. auto.
Qed.

Lemma lc_nil1 {A : Type} `{EqDec A eq} l1 l2 l2' (x : A)
      (Hlc : last_common' l1 l2 [] l2' x)
  : Some x = hd_error l1.
Proof.
  unfold last_common' in Hlc. destructH.
  cbn in *.
  destruct l1;[inversion Hlc0;congruence'|].
  cbn.
  f_equal.
  eapply postfix_hd_eq;eauto.
Qed.

Lemma lc_cons1 {A : Type} `{EqDec A eq} l1 l2 l1' l2' (x y : A)
      (Hlc : last_common' l1 l2 (x :: l1') l2' y)
  : Some x = hd_error l1.
Proof.
  unfold last_common' in Hlc. destructH.
  destruct l1;[inversion Hlc0;congruence'|].
  cbn.
  rewrite cons_rcons_assoc in Hlc0.
  f_equal.
  eapply postfix_hd_eq;eauto.
Qed.

Lemma lc_succ_rt_eq_lc {A : Type} `{EqDec A eq} l1 l2 l1' l2' (x y : A)
      (Hlc : last_common' l1 l2 l1' l2' x)
      (Hsucc1 : y ≻* x | l1)
      (Hsucc2 : y ≻* x | l2)
      (Hnd1 : NoDup l1)
      (Hnd2 : NoDup l2)
  : x = y.
Proof.
  unfold last_common' in Hlc. destructH.
  dependent induction Hsucc1.
  - clear IHHsucc1.
    destruct l1';cbn in Hlc0; eapply postfix_hd_eq in Hlc0; eauto.
    subst a.
    dependent induction Hsucc2.
    + destruct l2';cbn in Hlc2; eapply postfix_hd_eq in Hlc2; eauto. subst.
      exfalso. eapply Hlc1;left; reflexivity.
    + destruct l2';cbn in Hlc2; eapply postfix_hd_eq in Hlc2 as Heq; eauto.
      * subst a.
        eapply splinter_cons in Hsucc2. exfalso. eapply splinter_in in Hsucc2. inversion Hnd2. auto.
      * eapply IHHsucc2 with (l2':=l2') ; eauto.
        -- eapply cons_postfix;eauto.
        -- clear - Hlc1. eapply disjoint_cons2 in Hlc1. firstorder.
        -- inversion Hnd2. auto.
  - destruct l1';cbn in Hlc0; eapply postfix_hd_eq in Hlc0 as Heq; eauto.
    + subst a.
      eapply splinter_cons in Hsucc1. eapply splinter_in in Hsucc1. inversion Hnd1. subst. contradiction.
    + eapply IHHsucc1 with (l1':=l1');eauto.
      * eapply cons_postfix;eauto.
      * eapply disjoint_cons1 in Hlc1. firstorder.
      * inversion Hnd1. auto.
Qed.

(*Lemma succ_rt_antisym (A : Type) (a b : A) (l : list A)
      (Hnd : NoDup l)
  : a ≻* b | l -> b ≻* a | l -> a = b.
*)

Lemma hd_error_ne_front {A : Type} (l : ne_list A)
  : hd_error l = Some (ne_front l).
Proof.
  induction l;cbn;auto.
Qed.

Section disj.
  Context `{C : redCFG}.
  
(*  Lemma lc_common_element_nin {A : Type}(l1 l2 l1' l2' : list (Lab * Tag)) x y
        (Hlc : last_common' l1 l2 l1' l2' x)
        (Hin1 : y ∈ l1)
        (Hin2 : y ∈ l2)
    : y ∉ l1' /\ y ∉ l2'.
  Proof.
    revert dependent y. revert l1 l2 l1' l2' x Hlc.
    enough (forall (l1 l2 l1' l2' : list (Lab * Tag)) (x : Lab * Tag),
               last_common' l1 l2 l1' l2' x -> forall y, y ∈ l1 -> y ∈ l2 -> y ∉ l1').
    { split;[|eapply last_common'_sym in Hlc];eapply H;eauto. }
    intros ? ? ? ? ? Hlc y Hin1 Hin2. 
    unfold last_common' in Hlc. destructH.*)

  Lemma ex_entry (h p q : Lab) (i j : Tag) t
        (Hin : innermost_loop h q)
        (Hnin : ~ loop_contains h p)
        (Hpath : TPath' t)
        (Hord : (q,j) ≻* (p,i) | t)
    : (q,j) ≻* (h,0 :: tl j) ≻* (p,i) | t.
  Proof.
    (*
     * by dominance there must be an h in map fst t
     * define t' as the maximal suffix of t with tag dim >= |j|.
     * then t' ⊆ h
     * by definition t = t' or the maximal suffix starts with a loop enter
       * if t = t', contradiction bc. p ∈ t = t', and p ∈ h
       * else, ne_back t' = (h,0 :: tl j) and p ∉ t'
     *)
  Admitted.

  Variable (t1 t2 : ne_list (Lab * Tag)) (r1 r2 : list (Lab * Tag)) (q1 q2 s : Lab) (j1 j2 k : Tag).
  Hypotheses (Hpath1 : TPath (root,start_tag) (q1,j1) t1)
             (Hpath2 : TPath (root,start_tag) (q2,j2) t2)
             (Hlc : last_common' t1 t2 r1 r2 (s,k))
             (Hneq : r1 <> r2) (* <-> r1 <> nil \/ r2 <> nil *)
             (Hloop : eq_loop q1 q2)
             (Htag : tl j1 = tl j2)
             (Htagleq : hd 0 j1 <= hd 0 j2).

  Lemma s_deq_q : deq_loop s q1.
  Proof.
    intros h Hh.
    eapply loop_contains_innermost in Hh as Hinner. destructH.
    eapply eq_loop_innermost in Hinner as Hinner'; eauto.
    eapply innermost_loop_deq_loop;eauto. 2:eapply Hloop in Hh;auto.
    eapply path_front in Hpath1 as Hfront1.
    eapply path_front in Hpath2 as Hfront2.
    destruct r1, r2.
    - contradiction.
    - eapply lc_nil1 in Hlc.
      rewrite hd_error_ne_front in Hlc. setoid_rewrite Hfront1 in Hlc. inversion Hlc. subst s k.
      unfold innermost_loop in Hinner. destructH; auto.
    - eapply last_common'_sym in Hlc. eapply lc_nil1 in Hlc.
      rewrite hd_error_ne_front in Hlc. setoid_rewrite Hfront2 in Hlc. inversion Hlc. subst s k.
      unfold innermost_loop in Hinner'. destructH; auto.
    - decide (loop_contains h' s);[auto|exfalso].
      assert (p = (q1,j1)); [|subst p].
      { eapply lc_cons1 in Hlc;rewrite hd_error_ne_front in Hlc;setoid_rewrite Hfront1 in Hlc. inversion Hlc;auto. }
      assert (p0 = (q2,j2)); [|subst p0].
      { eapply last_common'_sym in Hlc.
        eapply lc_cons1 in Hlc;rewrite hd_error_ne_front in Hlc;setoid_rewrite Hfront2 in Hlc. inversion Hlc;auto. }
      copy Hinner Hinner''.
      eapply ex_entry in Hinner;eauto.
      eapply ex_entry in Hinner';eauto.
      3: eapply last_common'_sym in Hlc.
      3,5: eapply lc_succ_rt1;eauto.
      2,3: spot_path.
      rewrite Htag in Hinner.
      eapply splinter_cons in Hinner. eapply splinter_cons in Hinner'.
      eapply lc_succ_rt_eq_lc in Hlc;eauto.
      2,3: eapply tpath_NoDup;eauto.
      eapply n. inversion Hlc. eapply loop_contains_self. unfold innermost_loop in Hinner''. destructH.
      eapply loop_contains_loop_head;eauto.
  Qed.
    
  Lemma dep_eq_impl_head_eq (* unused *): depth s = depth q1 -> get_innermost_loop' s = get_innermost_loop' q1.
  Admitted.

  Lemma r1_in_head_q (* unused *): forall x, x ∈ r1 -> deq_loop (fst x) q1.
  Admitted.
  Lemma r2_in_head_q (* unused *): forall x, x ∈ r2 -> deq_loop (fst x) q2.
  Admitted.

  Lemma no_back_edge (* unused *): forall x, (get_innermost_loop' q1) ≻ x | (map fst r1) :r: s -> False.
  Admitted.

  Lemma lc_eq_disj
        (Hdep : depth s = depth q1)
        (Hjeq : j1 = j2)
    : Disjoint (map fst r1) (map fst r2).
  Admitted.
  
  Lemma lc_neq_disj
        (Hdep : depth s = depth q1)
        (Hjneq : j1 <> j2)
    : exists r', Prefix ((get_innermost_loop' q1) :: r') (map fst r2)
            /\ Disjoint (map fst r1) r'.
  Admitted.
  (* This section is now similar to the one in the paper *)
    
End disj.


(*Lemma lc_disj_exits_lsplits' `{redCFG}
          (s e1 e2 q1 q2 h : Lab) (i j1 j2 k : Tag) (t1 t2 : list Coord) qq1 qq2 h'
          (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
          (Hexit1 : exit_edge h q1 e1)
          (Hexit2 : exit_edge h q2 e2)
          (Hpath1 : TPath (root,start_tag) (e1,i) ((e1,i) :<: (q1,j1) :< t1))
          (Hpath2 : TPath (root,start_tag) (e2,i) ((e2,i) :<: (q2,j2) :< t2))
          (Hqq1 : exists jj1, (qq1,jj1) ≻ (h',j1) | impl_list' h ((q1,j1) :: t1))
          (Hqq2 : exists jj2, (qq1,jj2) ≻ (h',j1) | impl_list' h ((q2,j2) :: t2))
  : (s,`qq1,`qq2) ∈ splits' h e1 \/ (s,`qq1,`qq2) ∈ splits' h e2.*)
  
  
Theorem lc_disj_exits_lsplits `{redCFG}
          (s e1 e2 q1 q2 h : Lab) (i j1 j2 k : Tag) (t1 t2 : list Coord)
          (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
          (Hexit1 : exit_edge h q1 e1)
          (Hexit2 : exit_edge h q2 e2)
          (Hpath1 : TPath (root,start_tag) (e1,i) ((e1,i) :<: (q1,j1) :< t1))
          (Hpath2 : TPath (root,start_tag) (e2,i) ((e2,i) :<: (q2,j2) :< t2))
  : exists (qq qq' : Lab), (s,qq,qq') ∈ splits' h e1 \/ (s,qq,qq') ∈ splits' h e2.
Proof.
  remember (depth s - depth h) as n.
  revert e1 e2 q1 q2 h i j1 j2 t1 t2 Hlc Hexit1 Hexit2 Hpath1 Hpath2 Heqn.
  induction n; intros.
  - nl_eapply' lc_implode_out Hlc.
    2: { eapply tpath_tpath'. inversion Hpath1;subst. subst_path_fb H1. eauto. }
    2: { eapply tpath_tpath'. inversion Hpath2;subst. subst_path_fb H1. eauto. }
    2: { simpl_nl' Hlc. eapply lc_in_loop in Hlc. 2,3: unfold exit_edge in Hexit1,Hexit2; do 2 destructH; eauto.
         assert (depth s <= depth h) by omega.
         eapply depth_leq_deq;eauto. }
(*    enough ((exists qq qq' : Lab, (s, qq, qq') ∈ splits' h e1) \/ exists qq qq', (s, qq, qq') ∈ splits' h e2)
      by (clear - H0;firstorder).*)
    enough (exists qq qq' : Lab, (s, qq, qq') ∈ loop_splits__imp h e1 \/ (s, qq, qq') ∈ loop_splits__imp h e2).
    { setoid_rewrite splits'_spec. clear - H0. destructH. exists qq, qq'.
      destruct H0;[left|right];left;auto. }
    destructH. subst s. simpl_nl' Hlc1.
    rewrite last_common'_iff in Hlc1.
    destructH.
    eapply lc_disj_exits_lsplits_base;eauto.
  - intros.
    copy Hlc Hlc'.
    nl_eapply' lc_implode_in Hlc.
    2: { inversion Hpath1;subst. subst_path_fb H1. eauto. }
    2: { inversion Hpath2;subst. subst_path_fb H1. eauto. }
    2: { assert (~ depth s <= depth h) by omega. contradict H0. eapply deq_leq_depth; eauto. }
    destructH.
    enough ((exists br q q' : Lab, ((br, q, q') ∈ loop_splits__imp h e1 \/ (br, q, q') ∈ loop_splits__imp h e2)
                              /\ exists qq qq', ((s,qq,qq') ∈ splits' br q \/ (s,qq,qq') ∈ splits' br q'))).
    { clear - H0. destructH. exists qq, qq'.
      destruct H1;[left|right];eapply splits'_spec;right;exists br,q,q';split;eauto. }
    rewrite last_common'_iff in Hlc1.
    destructH. simpl_nl' Hlc1.
    eapply lc_disj_exits_lsplits_base in Hlc1;eauto.
    destructH.
    do 3 eexists. split;[eauto|].
    rewrite last_common'_iff in Hlc'. destructH.
    (* wish list:
       * find constrained header in tpath
       * (find successor of instance in tpath)
       * confirm existence of instance of tpath in imploded tpath
       * find predecessor of instance in tpath
       *)
    
    eapply IHn. all:admit.
(*      Lemma lc_prefix {A : Type} `{EqDec A eq} (l1 l2 l1' l2' l1'' l2'' : list A) (s : A)
            (Hlc : last_common' l1 l2 l1' l2' s)
            (Hpre1 : Prefix l1'' l1')
            (Hpre2 : Prefix l2'' l2')
      : last_common l1'' l2'' s.
      Admitted.*)
      
Admitted.

  

Corollary lc_disj_exit_lsplits `{redCFG} (s e q1 q2 h : Lab) (i j1 j2 k : Tag) (t1 t2 : list Coord)
          (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
          (Hexit1 : exit_edge h q1 e)
          (Hexit2 : exit_edge h q2 e)
          (Hpath1 : TPath (root,start_tag) (e,i) ((e,i) :<: (q1, j1) :< t1))
          (Hpath2 : TPath (root,start_tag) (e,i) ((e,i) :<: (q2, j2) :< t2))
  : exists (qq qq' : Lab), (s,qq,qq') ∈ splits' h e.
Proof.
  eapply lc_disj_exits_lsplits in Hlc;eauto.
  destructH. eexists;eexists. destruct Hlc;eauto.
Qed.

Theorem lc_join_split `{redCFG} t1 t2 (p q1 q2 s : Lab) (i j1 j2 k : Tag)
        (* it is important to cons qj's in front of the t's *)
        (Hlc : last_common ((q1,j1) :: t1) ((q2,j2) :: t2) (s,k))
        (Hneq : q1 <> q2)
        (Hpath1 : TPath (root,start_tag) (p,i) ((p,i) :<: (q1,j1) :< t1))
        (Hpath2 : TPath (root,start_tag) (p,i) ((p,i) :<: (q2,j2) :< t2))
  : exists qq qq', (s,qq,qq') ∈ splits p.
Proof.
  decide (exists h, exit_edge h q1 p /\ exit_edge h q2 p) as [e|Hnexit].
  {
      destructH.
      enough (exists qq qq', exited h p /\ (s,qq,qq') ∈ splits' h p).
      { destructH. eexists; eexists. eapply splits_spec. right. left. eauto. }
      eapply lc_disj_exits_lsplits in Hlc;eauto.
      destructH. do 2 eexists.
      unfold exited.
      destruct Hlc;eauto.
  }
(*  decide (deq_loop s p) as [Hdeq|Hndeq].*)
  decide (deq_loop p s) as [Hdeq'|Hndeq'].
  - enough (exists qq qq', (s, qq, qq') ∈ path_splits__imp p).
    { destructH. eexists; eexists. eapply splits_spec. left. eauto. }
    nl_eapply' lc_implode_out Hlc;eauto. 2,3: spot_path.
    2: { inversion Hpath1; subst. subst_path_fb H1. eauto. }
    2: { inversion Hpath2; subst. subst_path_fb H1. eauto. }
    destructH.
    subst s. clear Hdeq'. simpl_nl' Hlc1.
    eapply lc_join_path_split;eauto.
  - enough (exists br q q' : Lab, (br, q, q') ∈ path_splits__imp p
                             /\ (exists qq qq', (s, qq, qq') ∈ splits' br q \/ (s, qq, qq') ∈ splits' br q')).
    { destructH. exists qq, qq'. eapply splits_spec. right. right. do 3 eexists. split_conj;eauto. }
    copy Hlc Hlc'.
    nl_eapply' lc_implode_in Hlc';eauto.
    2: { inversion Hpath1; subst. subst_path_fb H1. eauto. }
    2: { inversion Hpath2; subst. subst_path_fb H1. eauto. } 
    destructH.
    rewrite last_common'_iff in Hlc'1. destructH. 
    simpl_nl' Hlc'1.
    eapply lc_join_path_split' in Hlc'1 as Hlc'3;eauto.
    unfold last_common' in Hlc'1. destructH.
    set (p' := impl_of_original' (or_introl (deq_loop_refl (l:=p)))) in *.
    set (qq := (ne_back (p' :< map fst l1'))) in *.
    set (qq' := (ne_back (p' :< map fst l2'))) in *.
    do 3 eexists. split;[eapply Hlc'3|].
    unfold last_common in Hlc. destructH.
    (* Show that qq is an exit *)
    assert (exited (` h') (` qq)) as Hexit1.
    {
      eapply loop_contains_loop_head in Hlc'0. eapply head_exit_in_impl in Hlc'0;cycle 1.
      - reflexivity.
      - instantiate (1:=qq). reflexivity.
      - clear - Hlc'2 Hpath1.
        simpl_nl' Hlc'2. 
        eapply impl_list'_tpath1 in Hpath1.        
        destruct (impl_list' p ((q1,j1) :: t1)) eqn:E.
        + setoid_rewrite E in Hlc'2. destruct l1'; cbn in Hlc'2; inversion Hlc'2; congruence'.
        + unfold nlcons in Hpath1. fold (nlcons p0 l) in Hpath1.
          unfold TPath' in Hpath1. inversion Hpath1.
          setoid_rewrite E in Hlc'2.
          eapply postfix_path in H1.
          2 : simpl_nl;eauto.
          eapply PathCons in H1;eauto.
          clear - H1.
          eapply TPath_CPath in H1. cbn in H1.
          destruct l1'.
          * cbn in *. inversion H1. unfold edge'. subst p'. inversion H2; subst. eauto.
          * rewrite ne_map_nl_rcons in H1. cbn in *.
            rewrite nl_cons_lr_shift in H1.
            inversion H1.
            eapply path_nlrcons_edge in H2. eauto.
      - auto.
    }
    assert (exited (` h') (` qq')) as Hexit2 by admit. (* analogous *)
    destruct Hexit1 as [qe1' Hexit1].
    destruct Hexit2 as [qe2' Hexit2].
    (* find the tag of qq *)
    assert (exists jj, (` qq, jj) ∈ ((p, i) :: l1'0)) as [jj Hqq].
    {
      specialize (ne_back_map_in p' i l1') as Htag. cbn in Htag. destructH.
      exists j0. simpl_nl.
      destruct Htag.
      - left. subst qq. inversion H0. setoid_rewrite <-H2. f_equal.
      - right. simpl_nl. clear Hlc'1.
        eapply postfix2_impl_list'_incl ;eauto.
        + inversion Hpath1. 
          subst_path_fb H2.
          eapply tpath_tpath'.
          eauto. 
        + rewrite nlcons_to_list in Hlc0. eapply Hlc0.
        + nl_eapply Hlc'2.
        + eapply exited_deq_p.
          eexists;eauto.
    }
    assert (exists jj', (` qq', jj') ∈ ((p,i) :: l2'0)) as [jj' Hqq'] by admit. (* analogous *)
    (* find the corresponding exiting node *)
    eapply in_cons_succ_in_rcons in Hqq;eauto. Unshelve. 2: exact (s,k). destructH. destruct d as [qe1 j1'].
    eapply in_succ_in2 in Hqq as Hin1.
    assert (tcfg_edge (qe1,j1') (` qq, jj) = true) as Hedge1.
    {
      eapply postfix_cons with (a:=(p,i)) in Hlc0.
      eapply postfix_path in Hpath1;[|cbn;simpl_nl;rewrite <-cons_rcons_assoc in Hlc0; eauto].
      rewrite <-cons_rcons_assoc in Hqq. rewrite rcons_nl_rcons in Hqq.
      eapply succ_in_path_edge in Hqq; eauto.
    }
    eapply in_cons_succ_in_rcons in Hqq'. Unshelve. 2: exact (s,k). destructH. destruct d as [qe2 j2'].
    eapply in_succ_in2 in Hqq' as Hin2.
    assert (tcfg_edge (qe2,j2') (` qq', jj') = true) as Hedge2 by admit. (* analogous *)
    assert (TPath (s,k) (q1,j1) (l1'0 >: (s,k))) as Hpath1'.
    {
      clear - Hlc0 Hpath1.
      inversion Hpath1. subst. replace b with (q1,j1) in *. 2: destruct t1;cbn in *;inversion H1;subst;eauto.
      eapply postfix_path in H1. eauto. simpl_nl. eauto.
    }
    assert (TPath (s,k) (q2,j2) (l2'0 >: (s,k))) as Hpath2' by admit. (* analogous *)
    eapply path_to_elem with (r:=(qe1,j1')) in Hpath1';eauto.
    2: { simpl_nl. eauto. }
    eapply path_to_elem with (r:=(qe2,j2')) in Hpath2';eauto.
    2: { simpl_nl. eauto. }
    do 2 destructH. simpl_nl' Hpath1'1. simpl_nl' Hpath2'1.
    destr_r ϕ. simpl_nl' Hpath2'1.
    destr_r ϕ0. simpl_nl' Hpath1'1. subst ϕ ϕ0.
    eapply path_to_elem with (r:=(qe1,j1')) in Hpath1 as H1ϕ.
    2: { right. eapply postfix_incl. simpl_nl. all:eauto. }
    eapply path_to_elem with (r:=(qe2,j2')) in Hpath2 as H2ϕ.
    2: { right. eapply postfix_incl. simpl_nl. all:eauto. }
    do 2 destructH.
    assert (exit_edge (` h') qe1 (` qq)) as Hexit1'.
    { eapply exit_edge_pred_exiting; [exact Hexit1|].
      unfold tcfg_edge,tcfg_edge' in Hedge1. conv_bool. destructH;eauto.
    }
    assert (exit_edge (` h') qe2 (` qq')) as Hexit2'.
    { eapply exit_edge_pred_exiting; [exact Hexit2|].
      unfold tcfg_edge,tcfg_edge' in Hedge2. conv_bool. destruct Hedge2 ;eauto.
    }
    eapply lc_disj_exits_lsplits;auto;cycle 1.
    + eauto.
    + eauto.
    + econstructor;eauto. cbn. instantiate (1:=tl ϕ0). instantiate (1:= j1'). clear - H1ϕ0.
      destruct H1ϕ0; cbn in *.
      * econstructor.
      * simpl_nl. cbn. econstructor;eauto. 
    + admit. (* analogous *)
    + eapply lc_continue;cycle 2.
      * eapply lc_sub. 3: eauto. all: eauto.
        -- eapply rcons_prefix;eauto.
        -- eapply rcons_prefix;eauto.
      * 
        rewrite nlcons_to_list.
        replace a0 with (s,k) in * by admit.
        replace a with (s,k) in * by admit.
        eapply post_prefix_cut.
        -- eapply tpath_NoDup.
           inversion Hpath1.
           replace b with (q1,j1) in * by (clear - H1; destruct t1; inversion H1; subst;  eauto).
           eapply H1.
        -- simpl_nl. eapply Hlc0.
        -- eauto.
        -- replace ϕ0 with ((qe1,j1') :< tl ϕ0) in H1ϕ0,H1ϕ1 by admit.
          inversion H1ϕ1.
          { exfalso.
            clear - Hin1 H2 Hpath1 Hlc0.
            eapply tpath_NoDup in Hpath1.
            cbn in Hpath1. inversion Hpath1.
            eapply H3.
            simpl_nl' H2. inversion H2. subst qe1. subst j1'.
            eapply postfix_incl;eauto. simpl_nl. eauto.
          }
          eapply H2.
        -- simpl_nl. cbn.
           clear - Hpath1'0. destruct l0; inversion Hpath1'0; cbn in *;eauto.
      * admit. (* analogous *)
Admitted.

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


(* FIXME: give intuition for unfinished proofs *)
