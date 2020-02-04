Require Export ImplodeCFG Precedes CFGancestor Tagle.

Require Import PropExtensionality.
  

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

  Inductive Edge (p q : Lab) : Type :=
  | Enormal : eq_loop p q -> a_edge__P p q -> Edge p q
  | Eback : back_edge p q -> Edge p q
  | Eentry : entry_edge p q -> Edge p q
  | Eexit : (exists h, exit_edge h p q) -> Edge p q.

  Lemma edge_Edge : forall (p q : Lab), edge__P p q -> Edge p q.
  Proof.
    intros ? ? Hedge.
    decide (deq_loop p q).
    - decide (deq_loop q p).
      + decide (a_edge__P p q).
        * econstructor;eauto;split;eauto.
        * eapply Eback. refine (conj Hedge n).
      + eapply Eexit.
        simpl_dec' n. simpl_dec' n. destructH.
        exists x. split;eauto.
    - eapply Eentry.
      unfold entry_edge. split_conj;eauto.
      + simpl_dec' n. simpl_dec' n. destructH.
        enough (x = q).
        * subst. eapply loop_contains_loop_head;eauto.
        * eapply dom_loop_contains in n1 as Hdom;eauto.
          specialize (PathSingle edge__P p) as Hpath.
          eapply PathCons in Hedge;eauto.
          eapply Hdom in Hedge. destruct Hedge;subst;auto.
          exfalso. cbn in H; destruct H;[|auto]. subst.
          eapply n1. eapply loop_contains_self;eapply loop_contains_loop_head;eauto.
      + contradict n. eapply loop_contains_deq_loop;auto.
  Defined.

  Lemma Edge_eq (p q : Lab)
        (H : edge__P p q)
        (Q : edge__P p q)
    : edge_Edge H = edge_Edge Q.
  Proof.
    f_equal.
    eapply proof_irrelevance.
  Qed.

  Definition STag (i : Tag)
    := match i with
       | nil => nil
       | n :: i => (S n) :: i
       end.
  
  Definition eff_tag' (p q : Lab) (i : Tag) (E : edge__P p q)
    := match edge_Edge E with
       | Enormal _ _ => i
       | Eback _ => STag i
       | Eentry _ => 0 :: i
       | Eexit _ => tl i
       end.

  Definition eff_tag (p q : Lab) (i : Tag)
    := match decision (edge__P p q) with
       | left E => Some (eff_tag' i E)
       | _ => None
       end.

  Lemma eff_tag'_eq (i : Tag) (p q : Lab) (H Q : edge__P p q)
    : eff_tag' i H = eff_tag' i Q.
  Proof.
    unfold eff_tag'.
    erewrite Edge_eq.
    reflexivity.
  Qed.
  
  (*
  Definition eff_tag p q i : Tag
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
   *)
  
  Definition tcfg_edge (c c' : Coord) :=
    let (p,i) := c  in
    let (q,j) := c' in
    edge__P p q /\ eff_tag p q i = Some j.
  
  Hint Unfold Coord tcfg_edge.

  Notation "pi -t> qj" := (tcfg_edge pi qj) (at level 50).
  (*Notation "pi -t> qj" := ((fun `(redCFG) => tcfg_edge pi qj = true) _ _ _ _ _)
                          (at level 50).*)

  Global Instance tcfg_edge_dec : forall pi qj, dec (pi -t> qj).
  Proof.
    intros. destruct pi as [p i]. destruct qj as [q j].
    cbn. decide (edge__P p q);eauto.
  Qed.

  Lemma tcfg_edge_spec (p q : Lab) i j
    : (p,i) -t> (q,j) <-> edge p q = true /\ eff_tag p q i = Some j.
  Proof.
    unfold tcfg_edge.
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
      unfold tcfg_edge in Hpq. conv_bool. destructH.
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
    Proof.
    Admitted.

    Lemma tag_entry_lt
          (Hlt : |i| < |j|)
      : j = O :: i.
    Proof.
    Admitted.

    Lemma tag_normal_iff
      : j = i <-> eq_loop p q.
    Proof.
    Admitted.
    
    Lemma tag_entry_iff
      : j = O :: i <-> entry_edge p q.
    Proof.
    Admitted.

    Lemma tag_back_edge_iff
      : match hd_error i with
        | Some n => S n :: tl i = j
        | None => False
        end <-> p ↪ q.
    Proof.
    Admitted.

    Lemma tag_deq_le
      : |i| <= |j| <-> deq_loop q p.
    Proof.
    Admitted.

    Lemma tag_deq_ge
      : |i| >= |j| <-> deq_loop p q.
    Proof.
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
    Proof.
    Admitted.

    Lemma tcfg_edge_destruct
      : i = j (* normal *)
        \/ j = O :: i (* entry *)
        \/ match hd_error i with Some n => S n :: tl i = j | None => False end (* back *)
        \/ j = tl i. (* exit *)
    Proof.
    Admitted.
    
  End eff_tag_facts.

  
  Definition TPath := Path tcfg_edge.

  Lemma tag_depth'  p i t
        (Hpath : TPath (root,start_tag) (p,i) t)
    : length i = depth p.
  Proof.
  Admitted.
    
  Lemma tag_depth  p i q j t
        (Hpath : TPath (root,start_tag) (p,i) t)
        (Hin : (q,j) ∈ t)
    : length j = depth q.
  Proof.
    eapply path_to_elem in Hpath;eauto. destructH.
    eapply tag_depth';eauto.
  Qed.

  Lemma STag_inj (i j : Tag)
        (Heq : STag i = STag j)
    : i = j.
  Proof.
    destruct i,j; cbn in *;eauto;congruence.
  Qed.

Lemma tag_eq_loop_exit p q i j j'
      (Htag : (q,j ) -t> (p,i))
      (Htag': (q,j') -t> (p,i))
      (Hneq : j <> j')
  : match (get_innermost_loop q) with
    | Some h => exit_edge h q p
    | None => False
    end.
Proof.
  unfold tcfg_edge,eff_tag in Htag,Htag'.
  do 2 destructH.
  decide (edge__P q p);[|congruence].
  unfold eff_tag' in *.
  inversion Htag1. inversion Htag'1. clear Htag1 Htag'1.
  destruct (edge_Edge e);subst.
  - contradiction.
  - eapply STag_inj in H1. subst j. contradiction.
  - inversion H1. subst. contradiction.
  - destructH.
    specialize (get_innermost_loop_spec q) as Himl.
    destruct (get_innermost_loop q).
    + replace e1 with h;eauto. eapply single_exit;eauto. unfold innermost_loop in Himl. destructH.
      unfold exit_edge. split_conj;eauto.
      specialize (exit_not_deq e0) as Q. contradict Q. eapply loop_contains_deq_loop in Q.
      rewrite Q. rewrite Himl1. eapply eq_loop_exiting;eauto.
    + eapply Himl. unfold exit_edge in e0. destructH. eauto.
Qed.

Lemma TPath_CPath  c c' π :
  TPath c c' π -> CPath (fst c) (fst c') (map fst π).
Proof.
  intros Q. dependent induction Q; [|destruct b,c]; econstructor; cbn in *.
  - apply IHQ. 
  - conv_bool. firstorder. 
Qed.

Parameter eff_tag_fresh : forall p q q0 i j j0 l,
    TPath (q0,j0) (q,j) l -> eff_tag q p j = Some i -> forall i', In (p, i') l -> i' <> i.

Parameter eff_tag_det : forall  q j p i i',
    eff_tag q p j = i ->
    eff_tag q p j = i' ->
    i = i'.

Lemma tpath_succ_eff_tag  p q r i j s t a l
      (Hpath : TPath (a,l) (r,s) ((r,s) :: t))
      (Hsucc : (q,j) ≻ (p,i) | (r,s) :: t)
  : eff_tag p q i = Some j.
Proof.
  unfold succ_in in Hsucc. destructH.
  assert ((r,s) :: t = l2 :r: (q,j) :r: (p,i) ++ l1) as Hsucc'.
  {
    rewrite Hsucc.
    do 2 rewrite app_cons_assoc. reflexivity.
  }
  rewrite Hsucc' in Hpath.
  eapply postfix_path with (l:=l2 :r: (q,j)) (p:=(p,i)) in Hpath.
  - eapply path_prefix_path with (ϕ:= [(p,i)]) (r:=(q,j))in Hpath.
    + inversion Hpath;subst;eauto. unfold tcfg_edge in H3. cbn in H3. destruct b. conv_bool.
      inversion H0;subst. destruct H3. eauto. inversion H5.
    + eauto.
    + cbn; clear. induction l2; cbn in *; econstructor; eauto.
  - cbn; clear. induction l2; cbn; destruct l1; cbn; eauto using postfix_cons.
    1,2: repeat (eapply postfix_cons; try econstructor). eapply postfix_nil.
Qed.

Lemma tpath_NoDup  p q t
      (Hpath : TPath p q t)
  : NoDup t.
Proof.
  induction Hpath.
  - econstructor; eauto. econstructor.
  - cbn. econstructor;eauto.
   destruct c. intro HIn. unfold tcfg_edge in H. destruct a, b. conv_bool. destruct H.
   eapply eff_tag_fresh in HIn;eauto.
Qed.

Lemma deq_loop_entry (p q : Lab)
      (Hentry : entry_edge p q)
  : deq_loop q p.
Proof.
  unfold entry_edge in Hentry.
  destructH.
  intros h Heq.
  assert (~ exit_edge h p q).
  - contradict Hentry0. eapply no_exit_head;eauto.
  - do 2 simpl_dec' H. destruct H as [H|[H|H]];[contradiction| |contradiction].
    eapply dec_DN;eauto.
Qed.

Lemma exit_edge_tcfg_edge (h p q : Lab) (j : Tag)
      (Hexit : exit_edge h q p)
  : (q,j) -t> (p,tl j).
Proof.
  cbn. copy Hexit Hexit'.
  unfold exit_edge in Hexit. destructH.
  split;auto.
  unfold eff_tag. decide (edge__P q p);[|contradiction].
  f_equal.
  unfold eff_tag'.
  destruct (edge_Edge e);auto.
  all: exfalso.
  - eapply Hexit2. eapply e0;eauto.
  - eapply back_edge_eq_loop in b. destruct b. eapply Hexit2. eauto.
  - eapply deq_loop_entry in e0. eapply Hexit2. eauto.
Qed.

(* possibly unused *)
Lemma exit_succ_exiting (p q h e : Lab) (k i j : Tag) r
      (Hpath : TPath (p,k) (q,j) (r :r: (p,k)))
      (Hexit : exited h e)
      (Hel : (e,i) ∈ r)
  : exists qe n, exit_edge h qe e /\ (e,i) ≻ (qe,n :: i) | r :r: (p,k).
Proof.
Admitted.

  Lemma prec_tpath_pre_tpath p i q j l
        (Hneq : p <> q)
        (Htr : TPath (root,start_tag) (p,i) ((p, i) :: l))
        (Hprec : Precedes fst l (q, j))
    : exists l', TPath (root,start_tag) (q,j) ((q,j) :: l') /\ Prefix ((q,j) :: l') ((p,i) :: l).
  Proof.
    eapply path_to_elem with (r:= (q,j)) in Htr.
    - destructH. exists (tl ϕ).
      assert (ϕ = (q,j) :: tl ϕ) as ϕeq.
      { inversion Htr0;subst a;cbn;eauto. }
      split;eauto.
      + rewrite ϕeq in Htr0;eauto.        
      + rewrite ϕeq in Htr1;eauto.
    - eapply precedes_in. econstructor;eauto;cbn;eauto.
  Qed.
  
  Lemma prec_tpath_tpath p i q j l
        (Htr : TPath (root,start_tag) (p,i) ((p, i) :: l))
        (Hprec : Precedes fst ((p,i) :: l) (q, j))
    : exists l', TPath (root,start_tag) (q,j) ((q,j) :: l').
  Proof.
    inversion Hprec;subst.
    - firstorder.
    - eapply prec_tpath_pre_tpath in Htr;eauto. destructH. eauto.
  Qed.

  Lemma precedes_fst_same_tag {A B : Type} `{EqDec B} (p : A) (i j : B) l
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

  Lemma tpath_tag_len_eq p j1 j2 l1 l2
        (Hpath1 : TPath (root, start_tag) (p, j1) l1)
        (Hpath2 : TPath (root, start_tag) (p, j2) l2)
    : length j1 = length j2.
  Proof.
    eapply tag_depth' in Hpath1.
    eapply tag_depth' in Hpath2.
    rewrite Hpath1,Hpath2. reflexivity.
  Qed.
  
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

  Lemma dom_tpath_prec p q i l
        (Hdom : Dom edge__P root q p)
        (Hpath : TPath (root,start_tag) (p,i) l)
    : exists j, Precedes fst l (q,j).
  Proof.
    (* FIXME *)
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
    - inversion HPath. (*subst a0 p i a. cbn in Hin. destruct Hin;[|contradiction].
      inversion H;subst. eauto.*)
    - destruct a. cbn in Hin.
      destruct Hin.
      + inversion H. subst. inversion HPath.
        * reflexivity.
        * exfalso.
          subst a c p i π. destruct b.
          eapply root_no_pred. eapply tcfg_edge_spec; eauto.
      + inversion HPath.
        * subst l. contradiction.
        * destruct b. eapply IHl;eauto.
  Qed.
  
  Lemma tag_prefix_ancestor a p q i j l
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

  Lemma tag_prefix_ancestor_elem a p q r i j k l
        (Hanc : ancestor a p q)
        (Hpath : TPath (root,start_tag) (r,k) ((r,k) :: l))
        (Hprec : Precedes fst ((r,k) :: l) (a,j))
        (Hib : (p,i) ≻* (a,j) | (r,k) :: l)
    : Prefix j i.
  Proof.
    eapply splinter_in in Hib as Hin. 
    eapply path_to_elem in Hin;eauto. destructH.
    decide (i = j).
    { subst. reflexivity. }
    eapply tag_prefix_ancestor;eauto.
    eapply path_contains_front in Hin0 as Hfront.
    eapply tpath_NoDup in Hin0. 
    eapply tpath_NoDup in Hpath. 
    clear - Hprec Hib Hin1 Hpath Hin0 n Hfront. set (l' := (r,k) :: l) in *.
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

  Lemma first_occ_tag j j1 j2 p t
        (Htag : j = j1 ++ j2)
        (Hpath : TPath (root,start_tag) (p,j) t)
    : exists h, loop_contains h p /\ Precedes fst t (h,j2).
  Proof.
    (* FIXME *)
  Admitted.
  
  Lemma first_occ_tag_elem i j j1 j2 p q t
        (Htag : j = j1 ++ j2)
        (Hpath : TPath (root,start_tag) (p,i) t)
        (Hin : (q,j) ∈ t)
    : exists h, loop_contains h q /\ Precedes fst t (h,j2) /\ (q,j) ≻* (h, j2) | t.
  Proof.
    eapply path_to_elem in Hpath;eauto. destructH.
    eapply first_occ_tag in Hpath0;eauto. destructH.
    (* FIXME *)
  Admitted.

  (* possibly not used *)
  Lemma prec_prec_eq l (q : Lab) (j j' : Tag)
        (Hprec1 : Precedes fst l (q,j))
        (Hprec2 : Precedes fst l (q,j'))
    : j = j'.
  Proof.  
  Admitted.
  
  (* possibly not used *)
  Lemma prefix_prec_prec_eq l l' (p q : Lab) (i j j' : Tag)
        (Hpre : Prefix ((p,i) :: l') l)
        (Hprec1 : Precedes fst l (q,j))
        (Hprec2 : Precedes fst ((p,i) :: l') (q,j'))
        (Hnd : NoDup l)
        (Hib : (p,i) ≻* (q,j) | l)
    : j' = j.
  Proof.
  Admitted.
  
  (* possibly not used *)
  Lemma ancestor_in_before_dominating a p q (i j k : Tag) l
        (Hdom : Dom edge__P root q p)
        (Hanc : ancestor a q p) 
        (Hprec__a: Precedes fst ((p,i) :: l) (a,k))
        (Hprec__q: Precedes fst ((p,i) :: l) (q,j))
    : (q,j) ≻* (a,k) | (p,i) :: l.
  Proof.
  Admitted.
    
  Lemma ancestor_level_connector p q a i j k t
        (Hpath : TPath (root,start_tag) (p,i) t)
        (Hin : (q,j) ∈ t)
        (Hanc  : near_ancestor a p q)
        (Hprec : Precedes fst t (a,k))
        (Hib : (q,j) ≻* (a,k) | t)
    : exists a', Precedes fst t (a',k) /\ (p,i) ≻* (a',k) ≻* (q,j) | t.
  Proof.
    (* FIXME *)
  Admitted.

  Lemma find_loop_exit h a p i j k n l
        (Hpath : TPath (root,start_tag) (p,i) l)
        (Hpre : Prefix k j)
        (Hib : (a,k) ≻* (h, n :: j) | l)
        (Hprec : Precedes fst l (h, n :: j))
    : exists qe e, (a,k) ≻* (e,j) ≻* (qe,n :: j) ≻* (h, n :: j) | l /\ (e,j) ≻ (qe,n :: j) | l /\ exit_edge h qe e.
  Proof.
    (* FIXME *)
  Admitted.
  
  Lemma tpath_deq_loop_prefix p q i j t x l y m
        (Hdeq : deq_loop p q)
        (Hpath : TPath (x,l) (y,m) t)
        (Hpre : Prefix j i)
    : (q,j) ≻* (p,i) | t.
  Proof.
     (* FIXME *)
  Admitted.
  
  Hint Resolve precedes_in.
  
  Lemma dom_dom_in_between  (p q r : Lab) (i j k : Tag) l
        (Hdom1 : Dom edge__P root r q)
        (Hdom2 : Dom edge__P root q p)
        (Hprec : Precedes fst ((p,i) :: l) (q,j))
        (Hin : (r,k) ∈ ((p,i) :: l))
        (Hpath : TPath (root,start_tag) (p,i) ((p,i) :: l))
    : (q,j) ≻* (r,k) | (p,i) :: l.
  Proof.
    (* FIXME *)
  Admitted.
  
  Lemma loop_cutting q p t
        (Hpath : CPath q p t)
        (Hnoh : forall h, loop_contains h q -> h ∉ t)
    : exists t', Path a_edge__P q p t'.
  Proof.
    (* FIXME *)
  Admitted.

  Lemma tpath_exit_nin h q e n j t
        (Hpath : TPath (root, start_tag) (q,n :: j) t)
        (Hloop : loop_contains h q)
        (Hexit : exited h e)
    : (e,j) ∉ t.
  Proof.
    intro N.
    unfold exited in Hexit. destructH.
    unfold exit_edge in Hexit. destructH.
    eapply PathCons in Hexit3;eauto. cycle 1.
  Admitted. (* FIXME *)
  
  Lemma loop_cutting_elem q p t i j x l
        (Hpath : TPath (x,l) (p,i) ((p,i) :: t))
        (Hib : (p,i) ≻* (q,j) | (p,i) :: t)
        (Hnoh : forall h k, loop_contains h q -> ~ (p,i) ≻* (h,k) ≻* (q,j) | (p,i) :: t)
    : exists t', Path a_edge__P q p t'.
  Proof.
    (* FIXME *)
  Admitted.
  
  Lemma exit_cascade u p t i j k x l
        (Hdom : Dom edge__P root u p)
        (Hprec : Precedes fst ((p,i) :: t) (u,j))
        (Hpath : TPath (x,l) (p,i) ((p,i) :: t))
    : forall h, loop_contains h u -> ~ (p,i) ≻* (h,k) ≻* (u,j) | (p,i) :: t.
    (* otw. there would be a path through this q to p without visiting u *)
    (* this could even be generalized to CPaths *)
    (* TODO: lift on tpaths, on cpaths we might have duplicates, thus it doesn't work there *)
  Proof. (* FIXME *)
  Admitted.  
  
  Lemma tpath_depth_eq (p q : Lab) (i j : Tag) pi qj t
        (Hpath : TPath pi qj t)
        (Hel1 : (p,i) ∈ t)
        (Hel2 : (q,j) ∈ t)
        (Heq : |i| = |j|)
    : depth p = depth q.
  Proof.
    (* FIXME *)
  Admitted.
  
  Lemma tpath_depth_lt (p q : Lab) (i j : Tag) pi qj t
        (Hpath : TPath pi qj t)
        (Hel1 : (p,i) ∈ t)
        (Hel2 : (q,j) ∈ t)
        (Hlt : |i| < |j|)
    : depth p < depth q.
  Proof.
    (* FIXME *)
  Admitted.
  
  Lemma loop_tag_dom (h p : Lab) (i j : Tag) t
    (Hloop : loop_contains h p)
    (Hpath : TPath (root,start_tag) (p,i) t)
    (Htagle : j ⊴ i)
    (Hdep : |j| = depth h)
    : (h,j) ∈ t.
  Proof.
    (* FIXME *)
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
  Proof.
    (* FIXME *)
  Admitted.
  
End tagged.
