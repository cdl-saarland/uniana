Require Export ImplodeCFG Precedes CFGancestor Tagle.

Section tagged.
  
  Context `{C : redCFG}.

  Program Instance Tag_dec : EqDec Tag eq.
  Next Obligation.
    apply list_eqdec, nat_eq_eqdec.
  Qed.

  Definition start_tag : Tag := nil.

  Definition Coord : Type := (Lab * Tag).
  Hint Resolve Tag_dec.

  Program Instance Coord_dec : EqDec Coord eq.
  Next Obligation.
    eapply prod_eqdec;eauto.
  Qed.

  Hint Resolve Coord_dec.

  Definition tcfg_edge' (tag : Lab -> Lab -> Tag -> Tag) :=
    (fun c c' : Coord => let (p,i) := c  in
                      let (q,j) := c' in
                      edge p q && ( (tag p q i) ==b j)).

  Definition eff_tag `{redCFG} p q i : Tag
    := if decision (p ↪ q)
       then match i with
            | nil => nil
            | n :: l => (S n) :: l
            end
       else
         if decision (exists h, exit_edge h p q) then
           tl i
         else
           if decision (loop_head q) then
             O :: i
           else
             i.

  Definition tcfg_edge := tcfg_edge' eff_tag.

  Hint Unfold Coord tcfg_edge tcfg_edge'.

  Notation "pi -t> qj" := (tcfg_edge pi qj = true) (at level 50).
  (*Notation "pi -t> qj" := ((fun `(redCFG) => tcfg_edge pi qj = true) _ _ _ _ _)
                          (at level 50).*)

  Lemma tcfg_edge_spec (p q : Lab) i j
    : (p,i) -t> (q,j) <-> edge p q = true /\ eff_tag p q i = j.
  Proof.
    unfold tcfg_edge,tcfg_edge'.
    conv_bool. split;split;destructH;auto.
  Qed.

  Hint Resolve tcfg_edge_spec.


  Section eff_tag_facts.
    Variables (p q : Lab) (i j : Tag).
    Hypothesis (Hpq : (p,i) -t> (q,j)).

    Lemma tag_exit_iff
      : j = tl i <-> match get_innermost_loop p with
                   | Some h => exit_edge h p q
                   | None => False
                   end.
    Proof.
      unfold tcfg_edge,tcfg_edge' in Hpq. conv_bool. destructH.
      unfold eff_tag in Hpq.
    Admitted.
  
    Lemma tag_exit_iff'
      : j = tl i <-> exists h, exit_edge h p q.
    Proof.
      split;intro H.
      - eapply tag_exit_iff in H.
        destruct (get_innermost_loop p);[|contradiction]. eexists; eauto.
      - eapply tag_exit_iff. specialize (get_innermost_loop_spec p) as E. destruct (get_innermost_loop p).
        + destructH. 
          split;eauto. 1: unfold innermost_loop in E; destructH; auto. split;eauto. 2: eapply tcfg_edge_spec;eauto.
          unfold exit_edge in H. destructH. intro Hl.
          eapply innermost_loop_deq_loop in E;eauto.
        + destructH. eapply E. unfold exit_edge in H; destructH. eauto.
    Qed.

    Lemma tag_exit_lt
          (Hgt : |j| < |i|)
      : j = tl i.
    Admitted.

    Lemma tag_entry_lt
          (Hlt : |i| < |j|)
      : j = O :: i.
    Admitted.

    Lemma tag_normal_iff
      : j = i <-> eq_loop p q.
    Admitted.
    
    Lemma tag_entry_iff
      : j = O :: i <-> entry_edge p q.
    Admitted.

    Lemma tag_back_edge_iff
      : match hd_error i with
        | Some n => S n :: tl i = j
        | None => False
        end <-> p ↪ q.
    Admitted.

    Lemma tag_deq_le
      : |i| <= |j| <-> deq_loop q p.
    Admitted.

    Lemma tag_deq_ge
      : |i| >= |j| <-> deq_loop p q.
    Admitted.
    
    Lemma tag_deq_total
      : deq_loop p q \/ deq_loop q p.
    Proof.
      specialize (Nat.le_ge_cases (|i|) (|j|)) as Hcases.
      destruct Hcases;[right|left].
      - eapply tag_deq_le;auto.
      - eapply tag_deq_ge;auto.
    Qed.

    Lemma tag_deq_or_entry
      : deq_loop p q \/ entry_edge p q.
    Admitted.

    Lemma tcfg_edge_destruct
      : i = j (* normal *)
        \/ j = O :: i (* entry *)
        \/ match hd_error i with Some n => S n :: tl i = j | None => False end (* back *)
        \/ j = tl i. (* exit *)
    Admitted.
    
  End eff_tag_facts.

  
  Definition TPath := Path tcfg_edge.

  Lemma tag_depth (* unused *)`{redCFG} p i q j t
        (Hpath : TPath (root,start_tag) (p,i) t)
        (Hin : (q,j) ∈ t)
    : length j = depth q.
  Admitted.  

Lemma tag_eq_loop_exit `{redCFG} p q i j j'
      (Htag : (q,j ) -t> (p,i))
      (Htag': (q,j') -t> (p,i))
      (Hneq : j <> j')
  : match (get_innermost_loop q) with
    | Some h => exit_edge h q p
    | None => False
    end.
Proof.
  
  eapply tcfg_edge_destruct in Htag.
  eapply tcfg_edge_destruct in Htag'.
  
  destruct Htag as [Q|[Q|[Q|Q]]].
    destruct Htag' as [R|[R|[R|R]]].
Admitted. (* FIXME *)
(*
  unfold exit_edge. set (h := get_innermost_loop q).
  assert (get_innermost_loop q = h) as Heq by (subst;reflexivity).
  rewrite get_innermost_loop_spec in Heq. destructH.
  repeat split; eauto.
  - contradict Hneq. unfold deq_loop in Heq1.
    unfold tcfg_edge in *.
    unfold tcfg_edge' in *.
    conv_bool. destructH. destructH. unfold eff_tag in *.
    induction all_lab. destruct (back_edge_b p q). *)


Lemma TPath_CPath `{redCFG} c c' π :
  TPath c c' π -> CPath (fst c) (fst c') (ne_map fst π).
Proof.
  intros Q. dependent induction Q; [|destruct b,c]; econstructor; cbn in *.
  - apply IHQ. 
  - conv_bool. firstorder. 
Qed.            

Definition TPath' π := TPath (ne_back π) (ne_front π) π.


Parameter eff_tag_fresh : forall `{redCFG} p q q0 i j j0 l,
    TPath (q0,j0) (q,j) l -> eff_tag q p j = i -> forall i', In (p, i') l -> i' <> i.

Parameter eff_tag_det : forall `{redCFG} q j p i i',
    eff_tag q p j = i ->
    eff_tag q p j = i' ->
    i = i'.

Lemma tpath_succ_eff_tag (* unused *)`{redCFG} p q r i j s t
      (Hpath : TPath' ((r,s) :< t))
      (Hsucc : (q,j) ≻ (p,i) | (r,s) :: t)
  : eff_tag p q i = j.
Proof.
  unfold succ_in in Hsucc. destructH.
  assert ((r,s) :< t = l2 >: (q,j) :>: (p,i) :+ l1) as Hsucc'.
  {
    rewrite nlcons_to_list in Hsucc. eapply ne_to_list_inj. rewrite Hsucc.
    simpl_nl.
    repeat rewrite app_cons_assoc. reflexivity.
  }
  rewrite Hsucc' in Hpath.
  unfold TPath' in Hpath.
  eapply postfix_path with (l:=l2 :r: (q,j)) (p:=(p,i)) in Hpath.
  - eapply path_prefix_path with (ϕ:= (q,j) :<: ne_single (p,i)) in Hpath.
    + inversion Hpath;subst;eauto. unfold tcfg_edge,tcfg_edge' in H4. cbn in H4. destruct b. conv_bool.
      inversion H1;subst. destruct H4. eauto.
    + cbn; simpl_nl. clear. induction l2; cbn; econstructor; eauto.
  - cbn; simpl_nl. clear. induction l2; cbn; destruct l1; cbn; simpl_nl; eauto using postfix_cons.
    1,2: repeat (eapply postfix_cons; try econstructor). eapply postfix_nil.
Qed.

Lemma tpath_NoDup `{redCFG} p q t
      (Hpath : TPath p q t)
  : NoDup t.
Proof.
  induction Hpath.
  - econstructor; eauto. econstructor.
  - cbn. econstructor;eauto.
   destruct c. intro HIn. unfold tcfg_edge,tcfg_edge' in H0. destruct a, b. conv_bool. destruct H0.
   eapply eff_tag_fresh in HIn;eauto.
Qed.

Lemma exit_edge_tcfg_edge (h p q : Lab) (j : Tag)
      (Hexit : exit_edge h q p)
  : tcfg_edge (q,j) (p,tl j) = true.
Proof.
  cbn. conv_bool.
  unfold eff_tag. 
  decide (q ↪ p).
  - exfalso. eapply no_exit_head;eauto. exists q. auto.
  - unfold exit_edge in Hexit. destructH. split;[auto|].
    decide (exists h0, exit_edge h0 q p).
    + reflexivity.
    + exfalso. eapply n0. exists h. unfold exit_edge. eauto.
Qed.

Lemma exit_succ_exiting (p q h e : Lab) (k i j : Tag) r
      (Hpath : TPath (p,k) (q,j) (r >: (p,k)))
      (Hexit : exited h e)
      (Hel : (e,i) ∈ r)
  : exists qe n, exit_edge h qe e /\ (e,i) ≻ (qe,n :: i) | r :r: (p,k).
Admitted. (* FIXME *)
(*Section tagged.
  
  Context `{C : redCFG}.*)

  Lemma prec_tpath_pre_tpath p i q j l
        (Hneq : p <> q)
        (Htr : TPath (root,start_tag) (p,i) ((p, i) :< l))
        (Hprec : Precedes fst l (q, j))
    : exists l', TPath (root,start_tag) (q,j) ((q,j) :< l') /\ Prefix ((q,j) :: l') ((p,i) :: l).
  Proof.
    eapply path_to_elem with (r:= (q,j)) in Htr.
    - destructH. exists (tl ϕ).
      assert (ϕ = (q,j) :< tl ϕ) as ϕeq.
      { inversion Htr0;subst a;cbn;simpl_nl;eauto. }
      split;eauto.
      + rewrite ϕeq in Htr0;eauto.        
      + rewrite ϕeq in Htr1;simpl_nl' Htr1;eauto.
    - eapply precedes_in. simpl_nl. econstructor;eauto;cbn;eauto.
  Qed.
  
  Lemma prec_tpath_tpath (* unused *)p i q j l
        (Htr : TPath (root,start_tag) (p,i) ((p, i) :< l))
        (Hprec : Precedes fst ((p,i) :: l) (q, j))
    : exists l', TPath (root,start_tag) (q,j) ((q,j) :< l').
  Proof.
    inversion Hprec;subst.
    - firstorder.
    - eapply prec_tpath_pre_tpath in Htr;eauto. destructH. eauto.
  Qed.

  Lemma precedes_fst_same_tag (* unused *){A B : Type} `{EqDec B} (p : A) (i j : B) l
        (Hprec1 : Precedes fst l (p,i))
        (Hprec2 : Precedes fst l (p,j))
    : i = j.
  Proof.
    clear edge root a_edge C.
    dependent induction Hprec1.
    - inversion Hprec2;subst;[reflexivity|]. cbn in H2; contradiction.
    - inversion Hprec2;subst.
      + cbn in H0;contradiction.
      + eapply IHHprec1;eauto.
  Qed.

  Lemma tpath_tag_len_eq (* unused *)p j1 j2 l1 l2
        (Hpath1 : TPath (root, start_tag) (p, j1) l1)
        (Hpath2 : TPath (root, start_tag) (p, j2) l2)
    : length j1 = length j2.
  Proof.
    revert dependent l2. revert dependent p. revert j1 j2.
    induction l1;intros;inversion Hpath1.
    - inversion Hpath2.
      + reflexivity.
      + exfalso. subst a1 a0 p j1 a c. destruct b. eapply tcfg_edge_spec in H4.
        eapply root_no_pred. eapply H4.
    - destruct b. subst c a0 a π.
      eapply tcfg_edge_destruct in H4.
      destruct H4 as [Hedge|[Hedge|[Hedge|Hedge]]].
      + subst t.
          
  Admitted. (* FIXME *)
  
  Lemma tpath_tag_len_eq_elem p q i1 i2 j1 j2 l1 l2
        (Hpath1 : TPath (root, start_tag) (p, i1) l1)
        (Hpath2 : TPath (root, start_tag) (p, i2) l2)
        (Hin1 : (q,j1) ∈ l1)
        (Hin2 : (q,j2) ∈ l2)
    : length j1 = length j2.
  Proof.
    eapply path_to_elem in Hin1;eauto.
    eapply path_to_elem in Hin2;eauto.
    do 2 destructH.
    eapply tpath_tag_len_eq in Hin0;eauto.
  Qed.

  Lemma dom_tpath_prec (* unused *)p q i l
        (Hdom : Dom edge root q p)
        (Hpath : TPath (root,start_tag) (p,i) l)
    : exists j, Precedes fst l (q,j).
  Admitted.
  
  Lemma tag_prefix_head h p i j l 
        (Hloop : loop_contains h p)
        (Hpath : TPath (root, start_tag) (p,i) l)
        (Hprec : Precedes fst l (h,j))
    : Prefix j i.
  Proof.
  Admitted. (* FIXME *)

  Lemma root_tag_nil p i j l
        (HPath : TPath (root,start_tag) (p,i) l)
        (Hin : (root,j) ∈ l)
    : j = nil.
  Proof.
    revert dependent p. revert i.
    induction l;intros.
    - inversion HPath. subst a0 p i a. cbn in Hin. destruct Hin;[|contradiction].
      inversion H;subst. eauto.
    - destruct a. cbn in Hin.
      destruct Hin.
      + exfalso. inversion H. subst. inversion HPath. subst. destruct b.
        eapply root_no_pred. eapply tcfg_edge_spec; eauto.
      + inversion HPath. subst. destruct b. eapply IHl;eauto.
  Qed.
  
  Lemma tag_prefix_ancestor (* unused *)a p q i j l
        (Hanc : ancestor a p q)
        (Hpath : TPath (root, start_tag) (p,i) l)
        (Hprec : Precedes fst l (a,j))
    : Prefix j i.
  Proof.
    unfold ancestor in Hanc.
    destruct Hanc as [[Hanc _]|Hanc]; [eapply tag_prefix_head|subst a];eauto.
    replace j with (@nil nat);[eapply prefix_nil|].
    symmetry; eapply root_tag_nil;eauto using precedes_in.
  Qed.

  Hint Unfold Coord.

  Lemma tag_prefix_ancestor_elem (* unused *)a p q r i j k l
        (Hanc : ancestor a p q)
        (Hpath : TPath (root,start_tag) (r,k) ((r,k) :< l))
        (Hprec : Precedes fst ((r,k) :: l) (a,j))
        (Hib : (p,i) ≻* (a,j) | (r,k) :: l)
    : Prefix j i.
  Proof.
    eapply splinter_in in Hib as Hin. rewrite nlcons_to_list in Hin.
    eapply path_to_elem in Hin;eauto. destructH.
    decide (i = j).
    { subst. reflexivity. }
    eapply tag_prefix_ancestor;eauto.
    eapply path_contains_front in Hin0 as Hfront.
    eapply tpath_NoDup in Hin0. simpl_nl' Hin0.
    eapply tpath_NoDup in Hpath. simpl_nl' Hpath.
    clear - Hprec Hib Hin1 Hpath Hin0 n Hfront. simpl_nl' Hin1. set (l' := (r,k) :: l) in *.
    eapply prefix_eq in Hin1. destructH.
    revert dependent l'. revert dependent ϕ. induction l2';intros.
    - cbn in Hin1. rewrite Hin1 in Hprec. eauto.
    - destruct l'. 1: inversion Hprec.
      inversion Hin1.
      eapply IHl2'. 6:eauto. 1,2:eauto.
      + inversion Hpath. subst. eauto.
      + inversion Hprec;subst.
        * exfalso.
          inversion Hib; subst. 1: contradiction.
          inversion Hpath. subst.
          eapply splinter_cons in H1. eapply splinter_in in H1. contradiction.
        * eauto.
      + subst. clear Hin1. inversion Hib;subst.
        * exfalso.
          inversion Hpath;subst.
          eapply H2.
          eapply in_or_app. right;auto.
        * eauto.
  Qed.

  Lemma first_occ_tag (* unused *)j j1 j2 p t
        (Htag : j = j1 ++ j2)
        (Hpath : TPath (root,start_tag) (p,j) t)
    : exists h, loop_contains h p /\ Precedes fst t (h,j2).
  Admitted.
  
  Lemma first_occ_tag_elem (* unused *)i j j1 j2 p q t
        (Htag : j = j1 ++ j2)
        (Hpath : TPath (root,start_tag) (p,i) t)
        (Hin : (q,j) ∈ t)
    : exists h, loop_contains h q /\ Precedes fst t (h,j2) /\ (q,j) ≻* (h, j2) | t.
  Admitted.

  Lemma prec_prec_eq (* unused *)l (q : Lab) (j j' : Tag)
        (Hprec1 : Precedes fst l (q,j))
        (Hprec2 : Precedes fst l (q,j'))
    : j = j'.
  Admitted.
  
  Lemma prefix_prec_prec_eq (* unused *)l l' (p q : Lab) (i j j' : Tag)
        (Hpre : Prefix ((p,i) :: l') l)
        (Hprec1 : Precedes fst l (q,j))
        (Hprec2 : Precedes fst ((p,i) :: l') (q,j'))
        (Hnd : NoDup l)
        (Hib : (p,i) ≻* (q,j) | l)
    : j' = j.
  Admitted.

  Lemma ancestor_in_before_dominating (* unused *)a p q (i j k : Tag) l
        (Hdom : Dom edge root q p)
        (Hanc : ancestor a q p) 
        (Hprec__a: Precedes fst ((p,i) :: l) (a,k))
        (Hprec__q: Precedes fst ((p,i) :: l) (q,j))
    : (q,j) ≻* (a,k) | (p,i) :: l.
  Admitted. 
    
  Lemma ancestor_level_connector (* unused *)p q a i j k t
        (Hpath : TPath (root,start_tag) (p,i) t)
        (Hin : (q,j) ∈ t)
        (Hanc  : near_ancestor a p q)
        (Hprec : Precedes fst t (a,k))
        (Hib : (q,j) ≻* (a,k) | t)
    : exists a', Precedes fst t (a',k) /\ (p,i) ≻* (a',k) ≻* (q,j) | t.
  Admitted.

  Lemma find_loop_exit (* unused *)h a p i j k n l
        (Hpath : TPath (root,start_tag) (p,i) l)
        (Hpre : Prefix k j)
        (Hib : (a,k) ≻* (h, n :: j) | l)
        (Hprec : Precedes fst l (h, n :: j))
    : exists qe e, (a,k) ≻* (e,j) ≻* (qe,n :: j) ≻* (h, n :: j) | l /\ (e,j) ≻ (qe,n :: j) | l /\ exit_edge h qe e.
  Admitted.
  
  Lemma tpath_deq_loop_prefix (* unused *)p q i j t
        (Hdeq : deq_loop p q)
        (Hpath : TPath' t)
        (Hpre : Prefix j i)
    : (q,j) ≻* (p,i) | t.
  Admitted. (* FIXME *)
  
  Lemma tpath_tpath' r i0 p i t
        (Hpath : TPath (r,i0) (p,i) t)
    : TPath' t.
  Proof.
    unfold TPath'. eapply path_back in Hpath as Hback. eapply path_front in Hpath as Hfront.
    rewrite Hfront,Hback. assumption.
  Qed.

  Hint Resolve tpath_tpath'.
  Hint Resolve precedes_in.
  
  Lemma dom_dom_in_between (* unused *) (p q r : Lab) (i j k : Tag) l
        (Hdom1 : Dom edge root r q)
        (Hdom2 : Dom edge root q p)
        (Hprec : Precedes fst ((p,i) :< l) (q,j))
        (Hin : (r,k) ∈ ((p,i) :: l))
        (Hpath : TPath (root,start_tag) (p,i) ((p,i) :< l))
    : (q,j) ≻* (r,k) | (p,i) :: l.
    
  Admitted.
  
  Lemma loop_cutting (* unused *)q p t
        (Hpath : CPath q p t)
        (Hnoh : forall h, loop_contains h q -> h ∉ t)
    : exists t', Path a_edge q p t'.
  Admitted.

  Lemma tpath_exit_nin (* unused *)h q e n j t
        (Hpath : TPath (root, start_tag) (q,n :: j) t)
        (Hloop : loop_contains h q)
        (Hexit : exited h e)
    : (e,j) ∉ t.
  Proof.
    intro N.
    eapply PathCons in Hpath;cycle 1.
    - unfold exited in Hexit. destructH.
      eapply exit_pred_loop in Hexit.
  Admitted. (* FIXME *)
  
  Lemma loop_cutting_elem (* unused *)q p t i j
        (Hpath : TPath' ((p,i) :< t))
        (Hib : (p,i) ≻* (q,j) | (p,i) :: t)
        (Hnoh : forall h k, loop_contains h q -> ~ (p,i) ≻* (h,k) ≻* (q,j) | (p,i) :: t)
    : exists t', Path a_edge q p t'.
  Admitted.

  Lemma exit_cascade (* unused *)u p t i j k
        (Hdom : Dom edge root u p)
        (Hprec : Precedes fst ((p,i) :: t) (u,j))
        (Hpath : TPath' ((p,i) :< t))
    : forall h, loop_contains h u -> ~ (p,i) ≻* (h,k) ≻* (u,j) | (p,i) :: t.
    (* otw. there would be a path through this q to p without visiting u *)
    (* this could even be generalized to CPaths *)
    (* TODO: lift on tpaths, on cpaths we might have duplicates, thus it doesn't work there *)
  Admitted.
  
  
  Lemma tpath_depth_eq (p q : Lab) (i j : Tag) pi qj t
        (Hpath : TPath pi qj t)
        (Hel1 : (p,i) ∈ t)
        (Hel2 : (q,j) ∈ t)
        (Heq : |i| = |j|)
    : depth p = depth q.
  Admitted.
  Lemma tpath_depth_lt (p q : Lab) (i j : Tag) pi qj t
        (Hpath : TPath pi qj t)
        (Hel1 : (p,i) ∈ t)
        (Hel2 : (q,j) ∈ t)
        (Hlt : |i| < |j|)
    : depth p < depth q.
  Admitted.
  
  Lemma loop_tag_dom (h p : Lab) (i j : Tag) t
    (Hloop : loop_contains h p)
    (Hpath : TPath (root,start_tag) (p,i) t)
    (Htagle : j ⊴ i)
    (Hdep : |j| = depth h)
    : (h,j) ∈ t.
  Admitted.
  
  Lemma deq_loop_le p i j q t t'
        (Hdeq : deq_loop p q)
        (Hpath : TPath (root,start_tag) (p,i) t)
        (Hpath' : TPath (root,start_tag) (q,j) t')
    : |j| <= |i|.
  Proof.
    eapply tag_depth in Hpath as Hdep'. 2: eapply path_contains_front;eauto.
    eapply tag_depth in Hpath' as Hdep. 2: eapply path_contains_front;eauto.
    rewrite Hdep, Hdep'.
    eapply deq_loop_depth;auto.
  Qed.

  Lemma tagle_monotone p q i j t
    (Hpath : TPath (root,start_tag) (p,i) t)
    (Hel : (q,j) ∈ t)
    (Hlen : |j| <= |i|)
    : j ⊴ i.
  Admitted.
  
End tagged.

