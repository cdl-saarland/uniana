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
Require Import Omega.

Require Util Graph Evaluation Unchanged Disjoint.

Module Uniana.
  Import Util Evaluation.Evaluation Disjoint.Disjoint Unchanged.Unchanged.

  Section uniana.

    Context `(C : redCFG).
    
  Parameter branch: Lab -> option Var.

  Definition is_branch br x := branch br = Some x.

  Parameter val_true : Val -> bool.

  Parameter branch_spec :
    forall p, match branch p with
         | Some x => exists q q' s r r', q <> q'
                                   /\ if val_true (s x)
                                     then eff' (p,s) = Some (q, r)
                                     else eff' (p,s) = Some (q',r')                                
         | None => forall q q', p --> q -> p --> q' -> q = q'
         end.

  Parameter root_no_pred' : forall p, p --> root -> False.
    
  Parameter init_uni : Var -> Prop.

  Definition UniState := Var -> bool.
         
  Parameter abs_uni_eff : UniState -> UniState.

  Definition uni_state_concr (uni : UniState) : State -> State -> Prop :=
    fun s => fun s' => forall x, uni x = true -> s x = s' x.

  Parameter local_uni_corr : forall uni p i q j s s' qs qs', 
      uni_state_concr uni s s' ->
      eff (p, i, s) = Some (q, j, qs) ->
      eff (p, i, s') = Some (q, j, qs') ->
      uni_state_concr (abs_uni_eff uni) qs qs'.

  Definition Uni := Lab -> Var -> bool.

  Definition uni_concr (u : Uni) : Hyper :=
    fun ts => forall t t', ts t -> ts t' ->
                   forall x p i s s', In (p, i, s) (`t) ->
                                 In (p, i, s') (`t') ->
                                 u p x = true -> s x = s' x.

  Definition uni_branch (uni : Uni) :=
    (fun spq : Lab * Lab * Lab
     => let s := fst (fst spq) in
       match (branch s) with
       | Some x => uni s x
       | None => false
       end
    ).
  
  Definition uni_trans (uni : Uni) (unch : Unch) : Uni :=
    fun p
    => if p == root then uni root
      else fun x => (join_andb (map (uni_branch uni) (splits p)))
                 (* the predecessor is only included in split set if p is an exit *)
                   && (join_andb (map (fun q => abs_uni_eff (uni q) x) (preds p)))
                 || join_orb (map (fun q => (q <>b p)
                                          && uni q x
                                          && join_andb (map (uni_branch uni) (rel_splits p q)))
                                 (unch_trans unch p x)).

  Lemma uni_trans_root_inv :
    forall uni unch x, uni_trans uni unch root x = uni root x.
  Proof.
    intros.
    unfold uni_trans.
    destruct (equiv_dec root root).
    reflexivity.
    exfalso. apply c. reflexivity.
  Qed.
  
  (*  
    Lemma branch_eff_eq br s1 s2 x i k k':
    is_branch br x
    -> s1 x = s2 x
    -> eff (br,i,s1) = Some k
    -> eff (br,i,s2) = Some k'
    -> fst k = fst k'.
  Proof.
    intros Hbr Heq Heff1 Heff2. unfold is_branch in Hbr. specialize (branch_spec br) as Hb.
    destruct Hbr as [tt [ff [xb Hbr]]].
    rewrite Hbr in Hb.
    destruct k as [[q j] r]. destruct k' as [[q' j'] r'].
    cbn.
    enough (q = q' /\ j = j') as [qeq jeq].
    {subst q j. reflexivity. }
    destruct Hb as [_ Hb]. apply Hb in Heff1 as Heff1'; apply Hb in Heff2 as Heff2'.
    cbn in Heff1',Heff2'. rewrite Heq in Heff1'. rewrite <-Heff2' in Heff1'. split;[assumption|].
    destruct Heff1'. clear Heff2'.
    eapply ivec_det; eauto.
  Qed.
   *)
        
  (*
  Lemma splits_is_branch br x p :
    In (br,x) (splits p) -> is_branch br x.
  Proof.
    intro HSsplit.
    eapply splits_spec in HSsplit. unfold DisjointBranch in HSsplit. firstorder.
  Qed.
   *)

  (*
  Lemma loop_splits_is_branch :
    forall (br : Lab) (x : Var) (p s : Lab), In (br, x) (loop_splits p s) -> is_branch br x.
  Proof.
    intros. eapply loop_splits_spec in H. firstorder.
  Qed.
   *)

  (*
  Ltac eff_some_k :=
    lazymatch goal with
    | [Htr : Tr ?tq,
             Hpost : Postfix (?l :r: ?K) (ne_to_list ?tq)
       |- exists k, eff ?K = Some k]                      
      => eapply postfix_incl in Hpost as Hpost_incl;
        eapply Tr_EPath in Htr as Htr';
        [destruct Htr' as [s0 Htr']|subst tq;simpl_nl;reflexivity];
        xeapply path_postfix_path Hpost; eauto;
        eapply front_eff_ex_succ;[eapply Htr| | |];
        eauto; [|subst tq; simpl_nl;eauto];
        eapply Hpost_incl,In_rcons; tauto
    end.
   *)
  
  Definition sub_traces (ts ts' : Traces) : Prop := forall t, ts t -> exists t', ts' t' /\ Prefix (`t) (`t').

  Lemma uni_concr_sub_traces ts ts' uni
        (Hsub : sub_traces ts ts')
        (Huni : uni_concr uni ts')
    : uni_concr uni ts.
  Proof.
    unfold uni_concr in *. unfold sub_traces in Hsub.
    intros. specialize (Hsub t H) as Hsub1. specialize (Hsub t' H0) as Hsub2. destructH. destructH.
    eapply (Huni t'1 t'0); eauto.
    - eapply in_prefix_in;eauto.
    - eapply in_prefix_in;eauto.
  Qed.

  Lemma tr_lc_lt' p i s1 s2 l1 l2
        (Htr1 : Tr ((p, i, s1) :<: l1))
        (Htr2 : Tr ((p, i, s2) :<: l2))
    : exists brk,
      last_common (ne_map fst l1) (ne_map fst l2) (brk).
  Proof.
    eapply ne_last_common. repeat rewrite ne_back_map.
    eapply ne_back_trace in Htr1 as [s1' Htr1]. cbn in Htr1.
    eapply ne_back_trace in Htr2 as [s2' Htr2]. cbn in Htr2.
    setoid_rewrite Htr1. setoid_rewrite Htr2. cbn;eauto.
  Qed.

  Lemma tr_lc_lt p i s1 s2 q1 q2 j1 j2 r1 r2 l1 l2
        (Htr1 : Tr ((p, i, s1) :<: (q1, j1, r1) :< l1))
        (Htr2 : Tr ((p, i, s2) :<: (q2, j2, r2) :< l2))
    : exists br k,
      last_common ((q1, j1) :: map fst l1) ((q2, j2) :: map fst l2) (br,k).
  Proof.
    enough (exists brk,
               last_common (ne_map fst ((q1, j1, r1) :< l1)) (ne_map fst ((q2, j2, r2) :< l2)) brk).
    { (simpl_nl' H;cbn in H;destruct H as [[br k] H];eauto). }
    eapply tr_lc_lt';eauto.
  Qed.

  Lemma tr_tpath p i s q j r l
        (Htr : Tr ((p,i,s) :<: (q,j,r) :< l))
    : TPath' ((p, i) :<: (q, j) :< map fst l).
  Proof.
    eapply Tr_EPath in Htr as Htr; cbn;eauto. destruct Htr as [s01 Htr].
    eapply EPath_TPath in Htr.
    cbn in *. unfold TPath'. simpl_nl' Htr. cbn in *.
    eapply path_back in Htr as Hback. cbn in Hback. unfold Coord in *. rewrite Hback;eauto.
  Qed.


  Lemma uni_branch_uni_succ p br q1 q2 qq qq' i k j1 j2 uni l1 l2
        (Hsucc1 : ((p,i) :: map fst l1) ⊢ (q1,j1) ≻ (br,k))
        (Hsucc2 : ((p,i) :: map fst l2) ⊢ (q2,j2) ≻ (br,k))
        (Hunibr : uni_branch uni (br, qq, qq') = true)
        (HCuni : forall (x : Var) (p : Lab) (i : Tag) (s s' : State),
            (p, i, s) ∈ l1 -> (p, i, s') ∈ l2 -> uni p x = true -> s x = s' x)
    : q1 = q2.
  Admitted. 

  Ltac copy H Q :=
    eapply id in H as Q.

  
  Ltac eapply2 H H1 H2 :=
    eapply H in H2; only 1: eapply H in H1.
  
  Ltac eapply2' H H1 H2 Q1 Q2 :=
    eapply H in H2 as Q2; only 1: eapply H in H1 as Q1.

  Lemma last_common_singleton1 {A : Type} `{EqDec A eq} (s a : A) l
        (Hlc : last_common (a :: nil) l s)
    : a = s.
  Proof.
    unfold last_common in Hlc. destructH. eapply postfix_rcons_nil_eq in Hlc0. firstorder.
  Qed.
  Lemma last_common_singleton2 {A : Type} `{EqDec A eq} (s a : A) l
        (Hlc : last_common l (a :: nil) s)
    : a = s.
  Proof.
    unfold last_common in Hlc. destructH. eapply postfix_rcons_nil_eq in Hlc2. firstorder.
  Qed.
  
  Lemma postfix_succ_in {A : Type} (a b : A) l l'
        (Hpost : Postfix l l')
        (Hsucc : l ⊢ a ≻ b)
    : l' ⊢ a ≻ b.
  Proof.
    induction Hpost;eauto.
    eapply IHHpost in Hsucc.
    unfold succ_in in Hsucc. destructH. exists (l1 :r: a0), l2. rewrite Hsucc.
    rewrite <-cons_rcons_assoc. unfold rcons. rewrite <-app_assoc.
    rewrite app_comm_cons. reflexivity.
  Qed.
  
  Lemma succ_in_rcons2 {A : Type} (a b : A) l
    : l :r: a :r: b ⊢ a ≻ b.
  Proof.
    exists nil, l. unfold rcons. rewrite <-app_assoc. rewrite <-app_comm_cons. cbn. reflexivity.
  Qed.
  
  Lemma succ_in_tpath_eff_tag p q i j t
        (Hpath : TPath' t)
        (Hsucc : t ⊢ (p,i) ≻ (q,j))
    : eff_tag q p j = i.
  Proof.
  Admitted.

  
  Lemma succ_in_cons_cons {A : Type} (a b : A) l
    : a :: b :: l ⊢ a ≻ b.
  Proof.
    exists l, nil. cbn. reflexivity.
  Qed.

  
  Lemma succ_cons {A : Type} `{EqDec A eq} (a b c : A) l
        (Hsucc : l ⊢ b ≻ c)
    : a :: l ⊢ b ≻ c.
  Proof.
    revert a;destruct l;intros a0.
    - unfold succ_in in *;cbn in *;eauto. destructH. destruct l2;cbn in *;congruence.
    - unfold succ_in in Hsucc. destructH. unfold succ_in. exists l1, (a0 :: l2).  cbn.
      rewrite Hsucc. reflexivity.
  Qed.

  Lemma uni_branch_succ_p p q br qq qq' i j k r r' l1 l2 l2' uni
        (Htr1 : TPath' ((p, i) :<: (q, j) :< map fst l1))
        (Htr2 : TPath' ((p, i) :<: (br, k) :< map fst l2))
        (Hsplit : uni_branch uni (br, qq, qq') = true)
        (HCuni : forall (x : Var) (p : Lab) (i : Tag) (s s' : State),
            (p, i, s) ∈ ((q, j, r) :: l1) ->
            (p, i, s') ∈ ((br, k, r') :: l2) -> uni p x = true -> s x = s' x)
        (Hpost : Postfix (((q, j) :: l2') :r: (br, k)) ((q, j) :: map fst l1))
    : q = br.
  Proof.
    destruct (hd (q, j) (rev ((q, j) :: l2'))) eqn:E.
    assert (((q, j) :: map fst l1) ⊢ (l, t) ≻ (br, k)) as Hsucc1.
    {
      eapply postfix_succ_in;eauto.
      rewrite cons_rcons'.
      fold (rcons (rev (tl (rev ((q, j) :: l2'))) :r: hd (q, j) (rev ((q, j) :: l2')))
                  (br, k)).
      rewrite E.
      eapply succ_in_rcons2.
    } 
    eapply uni_branch_uni_succ with (q1:=l) (q2:=p) in HCuni;eauto.
    * subst l.
      enough (t = i);[subst|].
      -- decide' (q == br);[eauto|exfalso].
         eapply tpath_NoDup in Htr1.
         inversion  Htr1. eapply H1. simpl_nl. eapply postfix_incl;eauto. fold (rcons l2' (br,k)).
         eapply In_rcons. right.
         rewrite cons_rcons'. eapply In_rcons. left. eauto.
      -- eapply eff_tag_det.
         2: eapply succ_in_tpath_eff_tag;clear Htr1;eauto;cbn;simpl_nl;
           eauto using succ_in_cons_cons.
         eapply succ_in_tpath_eff_tag;clear Htr2;eauto;cbn;simpl_nl;eauto.
         eapply succ_cons. eauto. 
    * eapply succ_cons. eauto.
    * cbn. eapply succ_in_cons_cons.
      Unshelve. eauto.
  Qed.

  
  
  Ltac subst' :=
    repeat
      match goal with
      | [H:(_,_) = (_,_) |- _] => inversion H; subst; clear H
      end.
  
  Lemma uni_same_tag p q i j1 j2 s1 s2 r1 r2 uni l1 l2
        (Htr1 : Tr ((p,i,s1) :<: (q,j1,r1) :< l1))
        (Htr2 : Tr ((p,i,s2) :<: (q,j2,r2) :< l2))
        (Hsplit : (join_andb (map (uni_branch uni) (splits p))) = true)
        (HCuni : forall (x : Var) (p : Lab) (i : Tag) (s s' : State),
            (p, i, s) ∈ ((q,j1,r1)::l1) -> (p, i, s') ∈ ((q,j2,r2)::l2) -> uni p x = true -> s x = s' x)
    : j2 = j1.
  Proof.
    decide' (j1 == j2);[reflexivity|exfalso].
    assert (forall s j r l (Htr : Tr ((p, i, s) :<: (q, j, r) :< l)),
                 tcfg_edge (q, j) (p, i) = true) as Htcfg.
    {
      clear. intros. 
      eapply Tr_EPath in Htr;[|cbn;eauto]. destructH. eapply EPath_TPath in Htr. cbn in Htr.
      inversion Htr. cbn in H.
      inversion H0;subst; [simpl_nl' H7;destruct l;cbn in H7;[|congruence]|].
      + inversion H7;subst;eauto.
      + simpl_nl' H4; cbn in H4. destruct l; cbn in H4;[congruence|]. inversion H4;subst;eauto.
    }
    copy c Hneq.
    eapply (tag_eq_loop_exit p q i) in c. 2,3: eapply Htcfg;eauto. clear Htcfg.
    eapply tr_lc_lt with (j1:=j1) (j2:=j2) in Htr1 as Hlc;eauto;destructH' Hlc.
    eapply lc_disj_exit_lsplits in c as Hsplits;eauto; cycle 1.
    - eapply tr_tpath;eauto. 
    - eapply tr_tpath;eauto.
    - destructH.
      unfold last_common in Hlc. destructH.
      destruct l1',l2'.
      + cbn in *. eapply2 postfix_hd_eq Hlc0 Hlc2.
        subst'. congruence. 
      + eapply2 tr_tpath Htr1 Htr2. cbn in Hlc0.
        destruct p0.
        eapply2' postfix_hd_eq Hlc0 Hlc2 Hlc0' Hlc2'. symmetry in Hlc0'. subst'.
        clear Hlc0 Hlc1 Hlc3 Hlc5.
        eapply join_andb_true_iff in Hsplit;eauto.
        
        admit.
        (* as *) admit. 
      + (* in *) admit.
      + (* uni_same_lab *) admit.
  Admitted.
  
  Lemma unch_dom u p x unch (* TODO: this will need a unch_concr assumption *)
        (Hunch : u ∈ unch_trans unch p x)
    : Dom edge root u p.
    unfold unch_trans,unch_trans_ptw in Hunch. unfold unch_trans_local in Hunch.
  Admitted.

  Lemma prec_lab_prec_fst p i s l
        (Hprec : Precedes lab_of l (p,i,s))
    : Precedes fst (map fst l) (p,i).
  Proof.
    induction l; inversion Hprec;subst;cbn in *.
    - econstructor.
    - econstructor;eauto.
      destruct a as [[a1 a2] a]; cbn in *;eauto.
  Qed.

  Lemma prec_tpath_pre_tpath p i q j l
        (Hneq : p <> q)
        (Htr : TPath (root,start_tag) (p,i) ((p, i) :< l))
        (Hprec : Precedes fst l (q, j))
    : exists l', TPath (root,start_tag) (q,j) ((q,j) :< l') /\ Prefix ((q,j) :: l') ((p,i) :: l).
  Proof.
    eapply path_to_elem with (r:= (q,j)) in Htr.
    - destructH. exists (tl ϕ).
      assert (ϕ = (q,j) :< tl ϕ) as ϕeq.
      { inversion Htr0;subst;cbn;simpl_nl;eauto. }
      split;eauto.
      + rewrite ϕeq in Htr0;eauto.        
      + rewrite ϕeq in Htr1;simpl_nl' Htr1;eauto.
    - eapply precedes_implies_in_pred. simpl_nl. econstructor;eauto;cbn;eauto.
  Qed.
  
  Lemma prec_tpath_tpath p i q j l
        (Htr : TPath (root,start_tag) (p,i) ((p, i) :< l))
        (Hprec : Precedes fst ((p,i) :: l) (q, j))
    : exists l', TPath (root,start_tag) (q,j) ((q,j) :< l').
  Proof.
    inversion Hprec;subst.
    - firstorder.
    - eapply prec_tpath_pre_tpath in Htr;eauto. destructH. eauto.
  Qed.

  (*
  Lemma top_level_tag_nil p i t
        (Hdep : depth p = 0)
a        (Htr : TPath (root,start_tag) (p,i) ((p,i) :< t))
    : i = nil.
  Admitted.
   *)

  (*
  Lemma get_innermost_loop_is_head p
        (Hdep : 0 < depth p)
    : loop_head (get_innermost_loop p).
  Admitted.
   *)

  (*
  Lemma dom_prec_tag h p q i j l
        (Hloop : loop_contains h q)
        (Hdeq : deq_loop p q)
        (Hdom : Dom edge h q p)
        (Hpath : TPath (root,start_tag) (p,i) l)
        (Hprec : Precedes fst l (q,j))
    : exists j', i = j' ++ j.
  Admitted.
   *)

  (*
  Lemma loop_contains_get_innermost p
        (Hdep : 0 < depth p)
    : loop_contains (get_innermost_loop p) p.
  Admitted.
  *)

  (*
  Lemma app_eq_length_eq_eq2 {A : Type} (l1 l2 l1' l2' : list A)
        (Hlen : length l2 = length l2')
        (Heq : l1 ++ l2 = l1' ++ l2')
    : l2 = l2'.
  Admitted.
   *)

  Lemma tpath_tag_len_eq p j1 j2 l1 l2
        (Hpath1 : TPath (root, start_tag) (p, j1) l1)
        (Hpath2 : TPath (root, start_tag) (p, j2) l2)
    : length j1 = length j2.
  Admitted.
  
  Lemma tpath_tag_len_eq_elem p q i1 i2 j1 j2 l1 l2
        (Hpath1 : TPath (root, start_tag) (p, i1) l1)
        (Hpath2 : TPath (root, start_tag) (p, i2) l2)
        (Hin1 : (q,j1) ∈ l1)
        (Hin2 : (q,j2) ∈ l2)
    : length j1 = length j2.
  Admitted.
  
  Hint Unfold Coord.

  Definition ancestor a p q :=
    loop_contains a p /\ loop_contains a q \/ a = root .

  Definition near_ancestor  a p q :=
    ancestor a p q /\ forall a', ancestor a p q -> deq_loop a a'.

  Lemma ex_near_ancestor p q
    : exists a, near_ancestor a p q.
    (* choose either a common head or root if there is no such head *)
  Admitted.
  
  Lemma ancestor_dom1 a p q
    : ancestor a p q -> Dom edge root a p.
  Admitted.

  Lemma ancestor_sym a p q
    : ancestor a p q -> ancestor a q p.
  Proof.
    unfold ancestor;firstorder 0.
  Qed.
  
  Lemma ancestor_dom2 a p q
    : ancestor a p q -> Dom edge root a q.
  Proof.
    eauto using ancestor_dom1, ancestor_sym.
  Qed.

  
  Lemma dom_tpath_prec p q i l
        (Hdom : Dom edge root q p)
        (Hpath : TPath (root,start_tag) (p,i) l)
    : exists j, Precedes fst l (q,j).
  Admitted.
  
  Lemma tag_prefix_head h p i j l 
        (Hloop : loop_contains h p)
        (Hpath : TPath (root, start_tag) (p,i) l)
        (Hprec : Precedes fst l (h,j))
    : Prefix j i.
  Admitted.

  Lemma root_tag_nil p i j l
        (HPath : TPath (root,start_tag) (p,i) l)
        (Hin : (root,j) ∈ l)
    : j = nil.
  Admitted.
  
  Lemma tag_prefix_ancestor a p q i j l
        (Hanc : ancestor a p q)
        (Hpath : TPath (root, start_tag) (p,i) l)
        (Hprec : Precedes fst l (a,j))
    : Prefix j i.
  Proof.
    unfold ancestor in Hanc.
    destruct Hanc as [[Hanc _]|Hanc]; [eapply tag_prefix_head|subst a];eauto.
    replace j with (@nil nat);[eapply prefix_nil|].
    symmetry; eapply root_tag_nil;eauto using precedes_implies_in_pred.
  Qed.

  Lemma tag_prefix_ancestor_elem a p q r i j k l
        (Hanc : ancestor a p q)
        (Hpath : TPath (root,start_tag) (r,k) ((r,k) :< l))
        (Hprec : Precedes fst ((r,k) :: l) (a,j))
        (Hib : (r,k) :: l ⊢ (a,j) ≺* (p,i))
    : Prefix j i.
  Proof.

    (* 
    eapply prec_tpath_pre_tpath in Hpath
    destruct Htr1' as [l1' [Hpath1 Hpre1]].
    destruct Htr2' as [l2' [Hpath2 Hpre2]].*)

    (*
    eapply dom_tpath_prec in Htr1 as Hanc11;eauto. destruct Hanc11 as [j1' Hanc11].
    eapply dom_tpath_prec in Htr2 as Hanc12;eauto. destruct Hanc12 as [j2' Hanc12].
    assert (j1' = j /\ j2' = j) as Heq;[|destruct Heq;subst j1' j2'].
    {
      simpl_nl' Hanc21. simpl_nl' Hanc22. simpl_nl' Hanc11. simpl_nl' Hanc12.
      split;eapply prec_prec_eq;eauto.
      (*
            |eapply prefix_prec_prec_eq with (l':=l2')];eauto.
      1,3: rewrite nlcons_to_list;eapply tpath_NoDup;eauto.
      1,2: eapply ancestor_in_before_dominating;eauto;
        econstructor;cbn;eauto.        *)
    }*)
    
  Admitted.

  (*
  Lemma in_tpath_tag_length_eq l r0 p q i0 i j1 j2
        (Htr : TPath (r0,i0) (p,i) l)
        (Hin1 : (q,j1) ∈ l)
        (Hin2 : (q,j2) ∈ l)
    : length j1 = length j2.
  Admitted.
   *)

  Lemma prefix_length_eq {A : Type} (l1 l2 l : list A)
        (Hlen : length l1 = length l2)
        (Hpre1 : Prefix l1 l)
        (Hpre2 : Prefix l2 l)
    : l1 = l2.
  Admitted.
  
  Lemma first_diff {A : Type} (l1 l2 : list A)
        (Hneq : l1 <> l2)
        (Hnnil1 : l1 <> nil)
        (Hnnil2 : l2 <> nil)
    : exists a1 a2 l' l1' l2', a1 <> a2 /\ l1 = l1' ++ a1 :: l' /\ l2 = l2' ++ a2 :: l'.
  Proof.
  Admitted.

  (*
  Fixpoint common_prefix' {A:Type} `{EqDec A eq} (la l1 l2 : list A) :=
    match l1,l2 with
    | a1 :: l1, a2 :: l2 => if a1 == a2
                           then common_prefix' (la :r: a1) l1 l2 
                           else common_prefix' nil l1 l2
    | nil,nil => la
    | _,_ => nil
    end.

  Definition common_prefix'' := common_prefix' nil.

  Definition common_prefix {A : Type} `{EqDec A eq} (l1 l2 : list A)
    := fold_left (fun s (ab : A * A) => let (a,b) := ab in
                                     if a == b then s ++ a :: nil else nil
                  ) (combine l1 l2) nil.

  Compute (combine (1 :: 2 :: 3 :: nil) (3 :: 2 :: 3 :: nil)).
  Compute (common_prefix (1 :: 2 :: 3 :: nil) (1 :: 2 :: 3 :: nil)).
  Compute (common_prefix (1 :: 2 :: 3 :: nil) (1 :: 1 :: 3 :: nil)).
  Compute (common_prefix (2 :: 2 :: 3 :: nil) (1 :: 2 :: 3 :: nil)).
  Compute (common_prefix (2 :: 3 :: nil) (2 :: 3 :: 5 :: nil)).
  *)

  Lemma first_occ_tag j j1 j2 p t
        (Htag : j = j1 ++ j2)
        (Hpath : TPath (root,start_tag) (p,j) t)
    : exists h, loop_contains h p /\ Precedes fst t (h,j2).
  Admitted.
  
  Lemma first_occ_tag_elem i j j1 j2 p q t
        (Htag : j = j1 ++ j2)
        (Hpath : TPath (root,start_tag) (p,i) t)
        (Hin : (q,j) ∈ t)
    : exists h, loop_contains h q /\ Precedes fst t (h,j2) /\ t ⊢ (h,j2) ≺* (q,j).
  Admitted.

  Lemma prec_prec_eq l (q : Lab) (j j' : Tag)
        (Hprec1 : Precedes fst l (q,j))
        (Hprec2 : Precedes fst l (q,j'))
    : j = j'.
  Admitted.
  
  Lemma prefix_prec_prec_eq l l' (p q : Lab) (i j j' : Tag)
        (Hpre : Prefix ((p,i) :: l') l)
        (Hprec1 : Precedes fst l (q,j))
        (Hprec2 : Precedes fst ((p,i) :: l') (q,j'))
        (Hnd : NoDup l)
        (Hib : in_before l (q,j) (p,i))
    : j' = j.
  Admitted.

  Lemma ancestor_in_before_dominating a p q (i j k : Tag) l
        (Hdom : Dom edge root q p)
        (Hanc : ancestor a q p) 
        (Hprec__a: Precedes fst ((p,i) :: l) (a,k))
        (Hprec__q: Precedes fst ((p,i) :: l) (q,j))
    : in_before ((p,i) :: l) (a,k) (q,j).
  Admitted. 

  Lemma prefix_eq:
    forall (A : Type) (l1 l2 : list A), Prefix l1 l2 <-> (exists l2' : list A, l2 = l2' ++ l1).
  Admitted.
  
  Lemma tag_prefix_same_head p h1 h2 i1 i2 j1 j2 t1 t2
        (Hpath1 : TPath (root,start_tag) (p,i1) t1)
        (Hpath2 : TPath (root,start_tag) (p,i2) t2)
        (Hloop1 : loop_contains h1 p)
        (Hloop2 : loop_contains h2 p)
        (Hprec1 : Precedes fst t1 (h1,j1))
        (Hprec2 : Precedes fst t2 (h2,j2))
        (Hlen : length j1 = length j2)
    : h1 = h2.
  Admitted.
  
  Lemma tag_prefix_same_head_elem p q h1 h2 i1 i2 j1 j2 k1 k2 t1 t2
        (Hpath1 : TPath (root,start_tag) (p,i1) t1)
        (Hpath2 : TPath (root,start_tag) (p,i2) t2)
        (Hloop1 : loop_contains h1 q)
        (Hloop2 : loop_contains h2 q)
        (Hin1 : (q,j1) ∈ t1)
        (Hin2 : (q,j2) ∈ t2)
        (Hprec1 : Precedes fst t1 (h1,k1))
        (Hprec2 : Precedes fst t2 (h2,k2))
        (Hlen : length j1 = length j2)
    : h1 = h2.
  Admitted.
  
  Lemma ancestor_level_connector p q a i j k t
        (Hpath : TPath (root,start_tag) (p,i) t)
        (Hin : (q,j) ∈ t)
        (Hanc  : near_ancestor a p q)
        (Hprec : Precedes fst t (a,k))
        (Hib : t ⊢ (a,k) ≺* (q,j))
    : exists a', Precedes fst t (a',k) /\ t ⊢ (q,j) ≺* (a',k) ≺* (p,i).
  Admitted.

  (*
  Lemma find_loop_exit h p i j n l
        (Hpath : TPath (root,start_tag) (p,i) l)
        (Hpre : Prefix i j)
        (Hprec : Precedes fst l (h, n :: j))
    : exists qe e, Precedes snd l (qe,n :: j) /\ l ⊢ (e,j) ≻ (qe,n :: j) /\ exit_edge h qe e.
  Admitted.
  *)

  Lemma find_loop_exit h a p i j k n l
        (Hpath : TPath (root,start_tag) (p,i) l)
        (Hpre : Prefix k j)
        (Hib : l ⊢ (h, n :: j) ≺* (a,k))
        (Hprec : Precedes fst l (h, n :: j))
    : exists qe e, l ⊢ (h, n :: j) ≺* (qe,n :: j) ≺* (a,k) /\ l ⊢ (e,j) ≻ (qe,n :: j) /\ exit_edge h qe e.
  Admitted.

    
  Lemma tpath_tpath' r i0 p i t
        (Hpath : TPath (r,i0) (p,i) t)
    : TPath' t.
  Proof.
    unfold TPath'. eapply path_back in Hpath as Hback. eapply path_front in Hpath as Hfront.
    rewrite Hfront,Hback. assumption.
  Qed.

  Hint Resolve tpath_tpath'.
  Hint Resolve precedes_implies_in_pred.
  
  Lemma dom_dom_in_between p q r i j k l
        (Hdom1 : Dom edge root r q)
        (Hdom2 : Dom edge root q p)
        (Hpath : TPath' l)
        (Hnd : NoDup l)
    : l ⊢ (r,k) ≺* (q,j) ≺* (p,i).
  Admitted.

  Lemma find_divergent_branch u p l1 l2 i j1 j2 
        (Hunch : Dom edge root u p)
        (Hprec1 : Precedes fst l1 (u, j1))
        (Hprec2 : Precedes fst l2 (u, j2))
        (Htr1 : TPath (root, start_tag) (p, i) ((p, i) :< l1))
        (Htr2 : TPath (root, start_tag) (p, i) ((p, i) :< l2))
        (Hneq : p <> u)
        (Hjneq : j1 =/= j2)
    : exists br qq qq' : Lab,
      (br, qq, qq') ∈ rel_splits p u /\
      (exists (k k' : Tag) (q1 q2 : Lab),
          l1 ⊢ (q1, k') ≻ (br, k) /\ l2 ⊢ (q2, k') ≻ (br, k) /\ q1 <> q2).
  Proof.
    specialize (ex_near_ancestor u p) as [a [Hanc Ha_near]].

    
    eapply ancestor_dom1 in Hanc as Hanc1. eapply ancestor_dom2 in Hanc as Hanc2.
    eapply dom_tpath_prec with (l:=(p,i) :< l1) in Hanc2 as Hanc21;eauto. destructH' Hanc21.
    eapply dom_tpath_prec with (l:=(p,i) :< l2) in Hanc2 as Hanc22;eauto. destructH' Hanc22.
        
    assert (j0 = j); [|subst j0].
    {
      eapply ancestor_sym in Hanc;eapply tag_prefix_ancestor in Hanc21 as Ha_pre1;eauto.
      eapply tag_prefix_ancestor in Hanc22 as Ha_pre2; eauto.
      simpl_nl' Hanc21. simpl_nl' Hanc22.
      eapply prec_tpath_tpath in Hanc21;eauto. destructH.
      eapply prec_tpath_tpath in Hanc22;eauto. destructH.
      eapply prefix_length_eq;eauto;eapply tpath_tag_len_eq;eauto.
    }

    enough ((p,i) :: l1 ⊢ (a,j) ≺* (u,j1)) as Hib1.
    enough ((p,i) :: l2 ⊢ (a,j) ≺* (u,j2)) as Hib2.
    2: eapply dom_dom_in_between with (l:= (p,i) :< l2) in Hunch;eauto.
    4: eapply dom_dom_in_between with (l:= (p,i) :< l1) in Hunch;eauto.
    2,4: simpl_nl' Hunch;destruct Hunch;eauto.
    2,3: eapply tpath_NoDup;eauto. 

    assert (Prefix j i) as Hprei by (eapply tag_prefix_ancestor;[eapply ancestor_sym| |];eauto).
    assert (Prefix j j1) as Hprej1
        by (simpl_nl' Hanc21;eapply tag_prefix_ancestor_elem with (l:=l1);eauto).
    assert (Prefix j j2) as Hprej2
        by (simpl_nl' Hanc22;eapply tag_prefix_ancestor_elem with (l:=l2);eauto).

    assert (exists j1', j1 = j1' ++ j) as [j1' Hj1] by (eapply prefix_eq;eauto).
    assert (exists j2', j2 = j2' ++ j) as [j2' Hj2] by (eapply prefix_eq;eauto).

    assert (j1' <> j2') as c'.
    {
      subst j1 j2. intro c'. rewrite c' in Hjneq. eapply Hjneq. reflexivity.
    } 

    eapply Pr_cont with (c:=(p,i)) in Hprec1;[|cbn;eauto].
    eapply Pr_cont with (c:=(p,i)) in Hprec2;[|cbn;eauto].
    (* find the first difference in the tag suffices *)
    eapply first_diff in c'. 
    2,3: intro N; eapply c'; subst;
      eapply precedes_implies_in_pred in Hprec1;eapply precedes_implies_in_pred in Hprec2;
    rewrite nlcons_to_list in Hprec1; rewrite nlcons_to_list in Hprec2;
      eapply tpath_tag_len_eq_elem in Hprec1;eauto;simpl_nl;
        do 2 rewrite app_length in Hprec1;exfalso.
    3:destruct j1';cbn in Hprec1; [congruence|omega]. 
    2:destruct j2';cbn in Hprec1;[congruence|omega].
    rename c' into Htag. destructH.
    subst j1' j2'. rewrite <-app_assoc in Hj1,Hj2. rewrite <-app_comm_cons in Hj1,Hj2.
    (* find the head of the divergent loop *)
    eapply first_occ_tag_elem with (t:=(p,i) :< l1) in Hj1 as Hocc1;eauto;
      simpl_nl;eauto using precedes_implies_in_pred.
    eapply first_occ_tag_elem in Hj2 as Hocc2;eauto;
      simpl_nl;eauto using precedes_implies_in_pred.
    do 2 destructH.
    (* show that it is the same head in both traces *)
    assert (h0 = h);[eapply tag_prefix_same_head_elem with (h1:=h0) (t1:=(p,i):<l1) (j1:=j1) (j2:=j2);
                     eauto;simpl_nl;eauto|subst h0].
    1: eapply tpath_tag_len_eq_elem with (l1:=(p,i):<l1);eauto;simpl_nl;eauto.
    (* find node on ancestor-depth that is between u & p *)


    (*
    copy Htr1 Hϕ1; copy Htr2 Hϕ2.
    eapply2 path_from_elem Hϕ1 Hϕ2;eauto.
    2,3: simpl_nl;eapply prefix_incl;eauto;left;eauto.
    do 2 destructH.*)
    eapply2 ancestor_level_connector Hanc21 Hanc22.
    4,8: split;[eapply ancestor_sym|];eauto. all: simpl_nl;eauto.
    destruct Hanc21 as [a1' [Hanc21 Hanc11]]. destruct Hanc22 as [a2' [Hanc22 Hanc12]].
    assert (Prefix j (l' ++ j)) as Hexit1.
    { eapply prefix_eq. eexists;reflexivity. }
    copy Hexit1 Hexit2.
    (*
    copy Htr1 Hπ1. copy Htr2 Hπ2.
    
    eapply path_to_elem with (r:=(a1',j)) in Hπ1. destruct Hπ1 as [π1 [Hπ10 Hπ11]].
    eapply path_to_elem with (r:=(a2',j)) in Hπ2. destruct Hπ2 as [π2 [Hπ20 Hπ21]].
    2,3: eapply postfix_incl;eauto;eapply precedes_implies_in_pred;eauto.*)
    eapply find_loop_exit with (a:=a1') (n:=a1) (h:=h) (l:= (p,i):<l1) in Hexit1;eauto.
    eapply find_loop_exit with (a:=a2') (n:=a2) in Hexit2;eauto.
    2,3: eapply in_before_trans;[eapply tpath_NoDup;eauto|eauto|
                                 unfold in_between in Hanc11,Hanc12; destruct Hanc11,Hanc12;eauto].
    (*
    2:eapply Hπ10. 3: eapply Hπ20. all:cycle 1.
    {

      instantiate (1:=a1). instantiate (1:=h).

      Lemma precedes_prefix_extend p u i j l l'
            (Hpath : TPath (root,start_tag) (p,i) l)
            (Hprec : Precedes fst l' (u,j))
            (Hpre : Prefix l' l)
            (Hnin : forall k, in_between l (u,j) (u,k) (p,i) -> j = k)
        : Precedes fst l (u,j).
      Admitted.

      Lemma precedes_prefix_shrink p u i j l l'
            (Hpath : TPath (root,start_tag) (p,i) l)
            (Hprec : Precedes fst l (u,j))
            (Hnin : forall k, ~ in_between l (ne_front l') (u,k) (p,i))
            (Hpre : Prefix l' l)
        : Precedes fst l' (u,j).
      Admitted.

      eapply precedes_prefix_extend;eauto.
      - admit.
      - admit. 
      
      (* complicated! 
         if u is preceding in l1, and h preceding in l1', then h preceding in l1. *)
      
    }
    {
      instantiate (1:= a2).
      (* the same *)
      admit.
    }
                                                       *)
    
    destruct Hexit1 as [qe1 [e1 [Hexit__seq1 [Hexit__succ1 Hexit__edge1]]]].
    destruct Hexit2 as [qe2 [e2 [Hexit__seq2 [Hexit__succ2 Hexit__edge2]]]].
    (*enough (π1 = (a1',j) :< tl π1) as πeq1.
    enough (π2 = (a2',j) :< tl π2) as πeq2.
    2,3: let f := fun Q => clear - Q; inversion Q;subst;cbn;simpl_nl;eauto in
         only 2:f Hπ10; f Hπ20.
    let f := fun Q Q1 Q2 => (rewrite Q in Q1, Q2) in f πeq1 Hexiting1 Hπ10; f πeq2 Hexiting2 Hπ20.
    simpl_nl' Hexiting1.*)


    eapply in_between_in2 in Hexit__seq1 as Hin1.
    eapply in_between_in2 in Hexit__seq2 as Hin2.
    eapply2 path_to_elem Hin1 Hin2; eauto.
    destruct Hin1 as [η1 [Hη1 Hpreη1]]. destruct Hin2 as [η2 [Hη2 Hprenη2]].
    assert (exists brk, last_common η1 η2 brk) as Hlc.
    {
      eapply ne_last_common. clear - Hη1 Hη2. eapply2 path_back Hη1 Hη2. rewrite Hη1,Hη2. reflexivity.
    }
    destruct Hlc as [[br k] Hlc].
    enough (η1 = (qe1, a1 :: l' ++ j) :< tl η1) as ηeq1.
    enough (η2 = (qe2, a2 :: l' ++ j) :< tl η2) as ηeq2.
    rewrite ηeq1 in Hlc; rewrite ηeq2 in Hlc.
    2,3: let f := fun Q => clear - Q; inversion Q;subst;cbn;simpl_nl;eauto in
         only 2:f Hη1; f Hη2.
    simpl_nl' Hlc.
    eapply lc_disj_exits_lsplits with (h0:=h) (e3:=e1) (e4:=e2) (i0:=l'++j) in Hlc as Hsplit;eauto.
    all: cycle 1.
    {
      clear - ηeq1 Hη1 Hexit__edge1 Hexit__succ1 Htr1. unfold TPath'. econstructor. cbn.
      + rewrite ηeq1 in Hη1. replace (ne_back (_ :< tl η1)) with (root,start_tag);eauto.
        symmetry. eapply path_back;eauto.
      + eapply succ_in_path_edge;cycle 4;eauto.
    } 
    {
      clear - ηeq2 Hη2 Hexit__edge2 Hexit__succ2 Htr2. unfold TPath'. econstructor. cbn.
      + rewrite ηeq2 in Hη2. replace (ne_back (_ :< tl η2)) with (root,start_tag);eauto.
        symmetry. eapply path_back;eauto.
      + eapply succ_in_path_edge;cycle 4;eauto.
    } 
    destructH.
    exists br, qq, qq';split.
    - eapply rel_splits_spec. exists h.
      eapply in_app_or in Hsplit. destruct Hsplit as [Hsplit|Hsplit].
      + exists e1. split_conj;eauto.
        1,2: unfold exited;eauto.
        * 

          
      Lemma exit_cascade u p i j t 
            (Hdom : Dom edge root u p)
            (Hprec : Precedes fst t (u,j))
            (Hpath : TPath (root,start_tag) (p,i) ((p,i) :< t))
      : forall h, loop_contains h u -> forall k, ~ in_between t (u,j) (h,k) (p,i).
        (* otw. there would be a path through this q to p without visiting u *)
        (* this could even be generalized to CPaths *)
      Admitted.

      assert (deq_loop u e1) as Hdeq by admit.

      Lemma loop_cutting q p t
            (Hpath : CPath q p t)
            (Hnoh : forall h, loop_contains h q -> h ∉ t)
        : exists t', Path a_edge q p t'.
      Admitted.

      Lemma loop_cutting_elem q p π
            (Hpath : CPath' π)
            (Hib : π ⊢ q ≺* p)
            (Hnoh : forall h, loop_contains h q -> ~ π ⊢ q ≺* h ≺* p)
        : exists t', Path a_edge q p t'.
      Admitted.
      eapply loop_cutting_elem. admit.
      
      
          (* idea: path from (u,j1) to (a1',j) is acyclic 
             and then cut cycles from a1' until first p*) admit. admit.
        * (*Lemma not_in_loop
                (Hanc : ancestor a u p)
                ( *)
          (* something with ancestors *) admit.
      + exists e2. split_conj;eauto.
        1,2: unfold exited;eauto.
        * (* same as *) admit.
        * (*  above  *) admit.           
    - exists k, (l' ++ j).
      destruct η1,η2;cbn in *.
      + cbn in Hlc.
        eapply last_common_singleton1 in Hlc as Hleft.
        eapply last_common_singleton2 in Hlc as Hright.
        inversion Hleft; inversion Hright; subst. congruence.
      + exists e1. (* br = qe1, thus successor is e1, the successor in l2 is in inside the loop,
                 thus they are unequal *) admit.
      + (* analogous to the one above *) admit. 
      + (* because successors are inside the last_common *) admit.

  
  Admitted.

  
  
  Lemma unch_same_tag p u i s1 s2 j1 j2 r1 r2 l1 l2 x uni unch
        (Hunibr : join_andb (map (uni_branch uni) (rel_splits p u)) = true)
        (Hunch : u ∈ unch_trans unch p x)
        (Hprec1 : Precedes lab_of l1 (u, j1, r1))
        (Hprec2 : Precedes lab_of l2 (u, j2, r2))
        (HCuni : forall (x : Var) (p : Lab) (i : Tag) (s s' : State),
            (p, i, s) ∈ l1 -> (p, i, s') ∈ l2 -> uni p x = true -> s x = s' x)
        (Htr1 : Tr ((p, i, s1) :< l1))
        (Htr2 : Tr ((p, i, s2) :< l2))
        (Hneq : p <> u)
    : j1 = j2.
  Proof.
    assert (forall p i s l (Htr : Tr ((p, i, s) :< l)),
               TPath (root, start_tag) (p, i) ((p, i) :< map fst l)) as Htr_path.
    {
      clear;intros.
      eapply Tr_EPath in Htr;[|simpl_nl;reflexivity]. destructH.
      eapply EPath_TPath' in Htr;simpl_nl;cbn. 2-4: reflexivity. assumption.
    }
    decide' (j1 == j2);[eauto|exfalso].
    eapply find_divergent_branch with (l1:=map fst l1) in c as Hwit;eauto.
    - destructH.
      (*eapply succ_cons in Hwit1. eapply succ_cons in Hwit2.*)
      eapply join_andb_true_iff in Hunibr;eauto. (*rewrite nlcons_to_list in Hwit1,Hwit2.*)
      eapply uni_branch_uni_succ 
        with (q1:=q1) (q2:=q2) (uni:=uni) in HCuni;eauto.
      1,2: eapply succ_cons;eauto.      
    - eapply unch_dom;eauto.
    - eapply prec_lab_prec_fst;eauto.
    - eapply prec_lab_prec_fst;eauto.
      Unshelve. all:eauto.      
  Qed.
    
  Lemma precedes_fst_same_tag {A B : Type} `{EqDec B} (p : A) (i j : B) l
        (Hprec1 : Precedes fst l (p,i))
        (Hprec2 : Precedes fst l (p,j))
    : i = j.
  Proof.
    clear all_lab edge root a_edge C.
    dependent induction Hprec1.
    - inversion Hprec2;subst;[reflexivity|]. cbn in H2; contradiction.
    - inversion Hprec2;subst.
      + cbn in H0;contradiction.
      + eapply IHHprec1;eauto.
  Qed.

    (* find Precedes fst ((u, j2) :< l') (a, j') in the same way and show that j & j'
       both are prefixes of i and both of same length, thus j = j'.
       then show that j is a prefix of j1 & j2. *)
    
    (*
    
    Lemma tag_prefix_anc `{redCFG} p i j l 
          (Hpath : TPath (root, start_tag) (p,i) l)
          (Hprec : Precedes fst l (h,j))
      : Prefix j i.
    Admitted.*)
    

    (* this proof is deprecated: *)
    (*
    destruct (destruct_deq_loop p u).
    - (* if p is in the innermost loop of u, u must have been visited (because of dominance)
       * in the same iteration where p is visited, thus the tag of the last ocurrence of u 
       * is a suffix of i. Since tags at the same lab have equal length, j1 = j2 *)
      clear - Hprec1 Hprec2 Htr1 Htr2 Htr_path Hunch Hneq H.
      eapply prec_lab_prec_fst in Hprec1;eapply prec_lab_prec_fst in Hprec2.
      eapply id in Hprec1 as Hprec1';eapply id in Hprec2 as Hprec2'.
      eapply prec_tr_tr in Hprec1. 2: eapply Htr_path;eauto.
      eapply prec_tr_tr in Hprec2. 2: eapply Htr_path;eauto.
      do 2 destructH.
      destruct (depth u) eqn:E.
      + (* if p and u are top-level all the tags are nil, thus j1 = j2 *)
        eapply top_level_tag_nil in Hprec1;eauto.
        eapply top_level_tag_nil in Hprec2;eauto. subst j1 j2;eauto.
      + assert (loop_head (get_innermost_loop u)) as Hhead.
        (eapply get_innermost_loop_is_head;clear - E;omega).
        assert (Hcon := loop_contains_get_innermost u). exploit' Hcon;[omega|].
        eapply dom_loop in Hcon as Hcon'.
        eapply dom_trans in Hunch;eauto;cycle 1.
        {
          eapply TPath_CPath in Hprec1;simpl_nl' Hprec1;cbn in Hprec1.
          eapply path_to_elem in Hprec1;eauto. destructH. eauto.
        }
        eapply Htr_path in Htr1; eapply Htr_path in Htr2.
        eapply dom_prec_tag in Htr1;eauto. 2:simpl_nl; econstructor;cbn;eauto.
        eapply dom_prec_tag in Htr2;eauto. 2:simpl_nl; econstructor;cbn;eauto.
        destructH. destructH.
        eapply app_eq_length_eq_eq2;[|subst i;eauto].
        eapply tpath_tag_len_eq;eauto.
    - decide' (j1==j2);[reflexivity|exfalso].
      eapply first_sync_exit with (l3:=(p,i) :< map fst l1) in c as Hexit;eauto.
      2,3: simpl_nl;econstructor;cbn;eauto;eapply prec_lab_prec_fst;eauto.
      simpl_nl' Hexit. destructH.

      Lemma sub_prec_prec_path r0 p qe e i0 i k j l 
            (Hsub : sub_list ((e, j) :: (qe, k) :: nil) ((p, i) :: l))
            (Hprec_qe : Precedes fst ((p, i) :: l) (qe, k))
            (Hprec_e  : Precedes fst ((p, i) :: l) ( e, j))
            (Hpath : TPath (r0, i0) (p, i) ((p, i) :< l))
        : exists l', TPath (r0,i0) (e,j) ((e,j) :<: (qe,k) :< l').
      Admitted.

      eapply sub_prec_prec_path in Hexit4;eauto. eapply sub_prec_prec_path in Hexit5;eauto.
      do 2 destructH.
      (* apply last common on the exit determined by first_exit_sync, 
       * then apply lc_disj_exits_lsplits on that,
       * then show that the lc-instance is in rel_splits
       * and derive a contradiction from the fact that rel_splits are uniform.*)
      
      
(*      eapply lc_disj_exits_lsplits in Hexit1. exploit Hexit1.
      1,2,4,5: admit.
      2: do 2 rewrite nlcons_to_list. eapply ne_last_common.
      + 
      eapply  in Hexit1;eauto. exploit' Hexit1;eauto.
      
        
                                                             


      destruct l1;[inversion Hprec1|];destruct l2;[inversion Hprec2|].
      rewrite nlcons_to_list in Htr1,Htr2,Hpre1,Hpre2,Hprec1,Hprec2.
      set (l1':=c:<l1) in *. set (l2':=c0:<l2) in *.
      (*cbn in Htr1,Htr2. destruct c as [[qq1 jj1] ss1]. destruct c0 as [[qq2 jj2] ss2].*)
      rewrite <-nlcons_necons in Htr1,Htr2.
      eapply tr_lc_lt' with (l1:=l1') (l2:=l2') in Htr1 as Hlc;eauto;destructH.*)
     *)
  

  Lemma lc_in_list1 {A : Type} `{EqDec A eq} (b : A) l l'
        (Hlc : last_common l l' b)
    : b ∈ l.
  Proof.
    unfold last_common in Hlc. destructH. eapply postfix_incl;eauto.
    eapply In_rcons;eauto.
  Qed.
  
  Lemma lc_in_list2 {A : Type} `{EqDec A eq} (b : A) l l'
        (Hlc : last_common l l' b)
    : b ∈ l'.
  Proof.
    unfold last_common in Hlc. destructH. eapply postfix_incl;eauto.
    eapply In_rcons;eauto.
  Qed.

  
  Ltac lc_infer :=
    lazymatch goal with
    | [ Hlc : last_common _ _ _ |- _ ] =>
      let Hleft := fresh "Hleft" in
      let Hright := fresh "Hright" in
      try (eapply last_common_singleton1 in Hlc as Hleft; inversion Hleft);
      try (eapply last_common_singleton2 in Hlc as Hright; inversion Hright);
      subst; try clear Hleft; try clear Hright; try congruence;
      let Hlc_in1 := fresh "Hlc_in1" in
      let Hlc_in2 := fresh "Hlc_in2" in
      eapply lc_in_list1 in Hlc as Hlc_in1;
      eapply lc_in_list2 in Hlc as Hlc_in2
    end.
  
  Lemma last_common_sym {A : Type} `{EqDec A eq} (l l' : list A) a
        (Hlc : last_common l l' a)
    : last_common l' l a.
  Proof.
    unfold last_common in *; firstorder.
  Qed.

  
  
  Lemma uni_same_lab p q1 q2 i j1 j2 s1 s2 r1 r2 uni l1 l2
        (Htr1 : Tr ((p,i,s1) :<: (q1,j1,r1) :< l1))
        (Htr2 : Tr ((p,i,s2) :<: (q2,j2,r2) :< l2))
        (Hsplit : (join_andb (map (uni_branch uni) (splits p))) = true)
        (HCuni : forall (x : Var) (p : Lab) (i : Tag) (s s' : State),
            (p, i, s) ∈ ((q1,j1,r1)::l1) -> (p, i, s') ∈ ((q2,j2,r2)::l2) -> uni p x = true -> s x = s' x)
    : q2 = q1.
  Proof.
    eapply tr_lc_lt in Htr1 as LC_lt;eauto. destructH' LC_lt.
    destruct (q2 == q1) as [ Heq | Hneq ]; [ eauto | exfalso ].
    symmetry in Hneq.
    eapply lc_join_split in LC_lt as LC_join;eauto.
    Unshelve. all:cycle 3. exact p. exact i.
    - destructH.
      unfold last_common in LC_lt; destructH.
      destruct l1',l2'.
      (* we have l1 = nil -> (br,k) = (q1,j1). but:  l1' = nil <-> (br,k) = (q1,j1) *)
      + cbn in *. eapply2 postfix_hd_eq LC_lt0 LC_lt2.
        subst'. congruence.
      + (* since (br,k) = (q1,j1) & uniform, we have that (p,i) succeeds (br,k) thus
         (p,i) ∈ l2, thus double occurence of the same instance in t2 --> contradiction *)
        eapply2 tr_tpath Htr1 Htr2. cbn in LC_lt0.
        destruct p0.
        eapply2' postfix_hd_eq LC_lt0 LC_lt2 LC_lt0' LC_lt2'. symmetry in LC_lt0'. subst'.
        clear LC_lt0 LC_lt1 LC_lt3 LC_lt5.
        eapply join_andb_true_iff in Hsplit;eauto.
        eapply Hneq.
        eapply uni_branch_succ_p;eauto.      
      + (* since (br,k) = (q2,j2) & uniform, we have that (p,i) succeeds (br,k) thus
         (p,i) ∈ l1, thus double occurence of the same instance in t1 --> contradiction *)
        eapply2 tr_tpath Htr1 Htr2. cbn in LC_lt0.
        destruct p0.
        eapply2' postfix_hd_eq LC_lt0 LC_lt2 LC_lt0' LC_lt2'. symmetry in LC_lt2'. subst'.
        clear LC_lt2 LC_lt1 LC_lt3 LC_lt5.
        eapply join_andb_true_iff in Hsplit;eauto.
        eapply Hneq. symmetry.
        eapply (uni_branch_succ_p p q2 br qq qq' i j2 k r2 r1);eauto.
        intros. symmetry. eapply HCuni;eauto.
      + (* successor of br is the same because of uniformity and in l1' & l2', 
           thus l1' & l2' are not disjoint --> contradiction *) admit.
  - eapply tr_tpath;eauto. 
  - eapply tr_tpath;eauto.
  Admitted.

  Ltac reduce_uni_concr HCuni Hpre1 Hpre2 :=
    clear - HCuni Hpre1 Hpre2; eapply2 prefix_incl Hpre1 Hpre2; intros; eapply HCuni;eauto.

  
  Lemma uni_correct :
    forall uni unch ts,
      sem_hyper (red_prod (uni_concr uni) (lift (unch_concr unch))) ts ->
      uni_concr (uni_trans uni unch) ts.
  Proof.
    intros uni unch ts Hred.
    unfold sem_hyper in Hred.
    destruct Hred as [ts' [Hconcr Hstep]].
    unfold uni_concr.
    intros t t' Hsem Hsem' x p i s s' HIn HIn' Htrans.

(*    assert (upi_concr (upi_trans upi uni) ts) as HCupi. {
      apply upi_correct. 
      destruct Hconcr as [[_ Hhom] _].
      exists ts'; auto.
    }*)

    assert (unch_concr (unch_trans unch) t) as HCunch. {
      destruct Hconcr as [_ Hunch].
      unfold lift in *; subst.
      apply unch_correct; [eapply root_no_pred'|]. assumption.
    } 
    
    assert (unch_concr (unch_trans unch) t') as HCunch'. {
      destruct Hconcr as [ _ Hunch].
      unfold lift in *; subst.
      apply unch_correct; [eapply root_no_pred'|]. assumption.
    }

    destruct Hconcr as [HCuni  _].

    subst.
    unfold uni_trans in Htrans. 
    assert (X := Hsem). destruct X as [t1 [k1 [Hts1 Hteq1]]].
    (*destruct X as [l [ltr [lstep [Hts Hlstep]]]]; subst.*)
    assert (X := Hsem'). destruct X as [t2 [k2 [Hts2 Hteq2]]].
    (*destruct X as [l' [ltr' [lstep' [Hts' Hlstep']]]]; subst.*)
    destruct (p == root); [ subst | ].
    - rewrite e in *; clear e. 
      (*destruct t as [t tr]. destruct t; cbn in HIn; inversion HIn.*)
      eapply HCuni; [eapply Hts1|apply Hts2| | | apply Htrans].
      + specialize (root_prefix t1) as [s0 rp]. apply root_start_tag in HIn as rst. subst i.
        eapply prefix_cons_in in rp as rp'.
        assert (Prefix (`t1) (`t)) as pre_t.
        { rewrite Hteq1. cbn. econstructor. econstructor. }
        eapply prefix_trans with (l2:=`t1) (l3:=`t) in rp; eauto. 2:eapply root_no_pred'.
        apply prefix_cons_in in rp. eapply tag_inj in HIn; [| apply rp].
        subst s0. eauto.
      + specialize (root_prefix t2) as [s0 rp]. apply root_start_tag in HIn as rst. subst i.
        eapply prefix_cons_in in rp as rp'.
        assert (Prefix (`t2) (`t')) as pre_t.
        { rewrite Hteq2. cbn. econstructor. econstructor. }
        eapply prefix_trans with (l2:=`t2) (l3:=`t') in rp; eauto.
        apply prefix_cons_in in rp. eapply tag_inj in HIn'; [| apply rp].
        subst s0. eauto. eapply root_no_pred'.
    - conv_bool.
      destruct Htrans as [[Htrans Hpred] | Hunch].
      (* The uni/hom case *)
      + rewrite Hteq1 in HIn. rewrite Hteq2 in HIn'.
        eapply in_pred_exists in HIn; try eassumption; [|setoid_rewrite <-Hteq1; exact (proj2_sig t)].
        eapply in_pred_exists in HIn'; try eassumption;[|setoid_rewrite <-Hteq2; exact (proj2_sig t')].
        destruct HIn as [q [j [r [HIn Hstep]]]].
        destruct HIn' as [q' [j' [r' [HIn' Hstep']]]].
        assert (q ∈ (preds p)) as Hqpred
            by (eapply in_preds;eauto using step_conf_implies_edge,root_no_pred').

        eapply prefix_in_list in HIn as Hpre1. destruct Hpre1 as [l1 Hpre1].
        eapply prefix_in_list in HIn' as Hpre2. destruct Hpre2 as  [l2 Hpre2].
        
        rewrite nlcons_to_list in Hpre1.
        eapply prefix_trace in Hpre1 as Htr1 ; [|destruct t1; eauto].

        rewrite nlcons_to_list in Hpre2.
        eapply prefix_trace in Hpre2 as Htr2; [|destruct t2;eauto].
        simpl_nl' Hpre1. simpl_nl' Hpre2.
        specialize (HCuni t1 t2 Hts1 Hts2).          
        cut (q' = q); intros; subst.
        * cut (j' = j); intros; subst.
          -- eapply (local_uni_corr (uni q) q j p i r r' s s'); try eassumption.
             ** unfold uni_state_concr. intros.
                unfold uni_concr in HCuni .
                eapply (HCuni x0 q j); eassumption.
             ** eapply join_andb_true_iff in Hpred; try eassumption.
          -- eapply uni_same_tag;eauto.
             1,2: econstructor;eauto;simpl_nl;eauto.
             reduce_uni_concr HCuni Hpre1 Hpre2.  
        * clear HCunch HCunch'.
          eapply uni_same_lab ; eauto.
          1,2: econstructor;eauto;simpl_nl;eauto. cbn in HCuni.
          reduce_uni_concr HCuni Hpre1 Hpre2.
      (* The unch case *)
      + rename Hunch into H.
        eapply join_orb_true_iff in H.
        destruct H as [u H].
        conv_bool.
        destruct H as [Hunch [[Hneq' Huni] Hunibr]].
        specialize (HCunch p i s u x HIn Hunch).
        specialize (HCunch' p i s' u x HIn' Hunch).
        destruct HCunch as [j [r [Hprec Heq]]]; try eassumption.
        destruct HCunch' as [j' [r' [Hprec' Heq']]]; try eassumption.
        (* TODO: we'll need HCunch' for unch_dom *)
        rewrite <- Heq. rewrite <- Heq'.
        cut (j = j'); intros.
        * subst j'. eapply HCuni. eapply Hts1. eapply Hts2. 3: eauto.
          all: eapply precedes_step_inv.
          -- rewrite <-nlcons_to_list. setoid_rewrite Hteq1 in Hprec. apply Hprec.
          -- rewrite <-nlcons_necons, <-Hteq1. destruct t; eauto.
          -- cbn. eauto.
          -- rewrite <-nlcons_to_list. setoid_rewrite Hteq2 in Hprec'. apply Hprec'.
          -- rewrite <-nlcons_necons, <-Hteq2. destruct t'; eauto.
          -- cbn;eauto.
        * unfold Precedes' in Hprec,Hprec'. destructH' Hprec. destructH' Hprec'.
          rewrite nlcons_to_list in Hprec0.
          eapply prefix_trace in Hprec0 as Htr1 ; [|destruct t; eauto].
          rewrite nlcons_to_list in Hprec'0.
          eapply prefix_trace in Hprec'0 as Htr2; [|destruct t';eauto].
          rewrite Hteq1 in Hprec0. simpl_nl' Hprec0. cbn in Hprec0. eapply prefix_cons_cons in Hprec0. 
          rewrite Hteq2 in Hprec'0. simpl_nl' Hprec'0. cbn in Hprec'0. eapply prefix_cons_cons in Hprec'0.
          eapply unch_same_tag with (l1:=l').
          1,2,6-8: eauto.
          -- inversion Hprec1;subst;eauto;congruence.
          -- inversion Hprec'1;subst;eauto;congruence.
          -- specialize (HCuni t1 t2 Hts1 Hts2).
             reduce_uni_concr HCuni Hprec0 Hprec'0.  
  Qed.
  
  Lemma incl_cons_hd (A : Type) (a : A) l l'
        (Hincl : (a :: l) ⊆ l')
    : a ∈ l'.
  Proof.
    induction l;cbn in *;unfold incl in Hincl;eauto;firstorder.
  Qed.
  
  End uniana.

End Uniana.
