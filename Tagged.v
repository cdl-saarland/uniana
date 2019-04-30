Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Utils.
Require Import Coq.Logic.Classical.
Require Import List.
Require Import Nat.
Require Import Bool.Bool.
Require Import Coq.Logic.Eqdep_dec.

Require Export CFG.

Generalizable Variable edge.

Definition Tag := list nat.

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

Hint Unfold Coord.

Ltac destr_let :=
  match goal with
  | [ |- context[let (_,_) := fst ?a in _]] => destruct a;unfold fst 
  | [ |- context[let (_,_) := snd ?a in _]] => destruct a;unfold snd
  | [ |- context[let (_,_) := ?a in _]] => destruct a
  end.

Definition tcfg_edge' (edge : Lab -> Lab -> bool) (tag : Lab -> Lab -> Tag -> Tag) :=
  (fun c c' : Coord => let (p,i) := c  in
                    let (q,j) := c' in
                    edge p q && ( (tag p q i) ==b j)).

Fixpoint eff_tag `{redCFG} p q i : Tag
  := if back_edge_b p q
     then match i with
          | nil => nil
          | n :: l => (S n) :: l
          end
     else 
       let l' := @iter Tag (@tl nat) i (exit_edge_num p q) in
       if loop_head_dec q then O :: l' else l'.

Definition tcfg_edge `{redCFG} := tcfg_edge' edge eff_tag.

Notation "pi -t> qj" := ((fun `(redCFG) => tcfg_edge pi qj = true) _ _ _ _ _)
                          (at level 50).

Lemma tag_eq_loop_exit `{redCFG} p q i j j'
      (Htag : (q,j ) -t> (p,i))
      (Htag': (q,j') -t> (p,i))
      (Hneq : j <> j')
  : exit_edge (get_innermost_loop q) q p.
Proof.
  unfold exit_edge. set (h := get_innermost_loop q).
  assert (get_innermost_loop q = h) as Heq by (subst;reflexivity).
  rewrite get_innermost_loop_spec in Heq. destructH.
  repeat split; eauto.
  - contradict Hneq. unfold deq_loop in Heq1.
    unfold tcfg_edge in *.
    unfold tcfg_edge' in *.
    conv_bool. destructH. destructH. unfold eff_tag in *.
    induction all_lab. destruct (back_edge_b p q). 

  
  
Admitted.

Definition TPath `{redCFG} := Path tcfg_edge.

Lemma tag_depth `{redCFG} p i q j t
      (Hpath : TPath (root,start_tag) (p,i) t)
      (Hin : (q,j) ∈ t)
  : length j = depth q.
Admitted.

Lemma TPath_CPath `{redCFG} c c' π :
  TPath c c' π -> CPath (fst c) (fst c') (ne_map fst π).
Proof.
  intros Q. dependent induction Q; [|destruct b,c]; econstructor; cbn in *.
  - apply IHQ. 
  - conv_bool. firstorder. 
Qed.            

Definition TPath' `{redCFG} π := TPath (ne_back π) (ne_front π) π.


Parameter eff_tag_fresh : forall `{redCFG} p q q0 i j j0 l,
    TPath (q0,j0) (q,j) l -> eff_tag q p j = i -> forall i', In (p, i') l -> i' <> i.

Parameter eff_tag_det : forall `{redCFG} q j p i i',
    eff_tag q p j = i ->
    eff_tag q p j = i' ->
    i = i'.

Lemma tpath_succ_eff_tag `{redCFG} p q r i j s t
      (Hpath : TPath' ((r,s) :< t))
      (Hsucc : (q,j) ≻ (p,i) | (r,s) :: t)
  : eff_tag p q i = j.
Proof.
  unfold succ_in in Hsucc. destructH.
  assert ((r,s) :< t = l2 >: (q,j) :>: (p,i) :+ l1) as Hsucc'.
  {
    rewrite nlcons_to_list in Hsucc. eapply ne_to_list_inj. rewrite Hsucc.
    simpl_nl.
    rewrite <-nlconc_to_list. simpl_nl. repeat rewrite app_cons_assoc. reflexivity.
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

Section tagged.
  
  Context `{C : redCFG}.

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
    - eapply precedes_in. simpl_nl. econstructor;eauto;cbn;eauto.
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
    symmetry; eapply root_tag_nil;eauto using precedes_in.
  Qed.

  Hint Unfold Coord.
  

  Lemma tag_prefix_ancestor_elem a p q r i j k l
        (Hanc : ancestor a p q)
        (Hpath : TPath (root,start_tag) (r,k) ((r,k) :< l))
        (Hprec : Precedes fst ((r,k) :: l) (a,j))
        (Hib : (p,i) ≻* (a,j) | (r,k) :: l)
    : Prefix j i.
  Proof.   
  Admitted.

  Lemma first_occ_tag j j1 j2 p t
        (Htag : j = j1 ++ j2)
        (Hpath : TPath (root,start_tag) (p,j) t)
    : exists h, loop_contains h p /\ Precedes fst t (h,j2).
  Admitted.
  
  Lemma first_occ_tag_elem i j j1 j2 p q t
        (Htag : j = j1 ++ j2)
        (Hpath : TPath (root,start_tag) (p,i) t)
        (Hin : (q,j) ∈ t)
    : exists h, loop_contains h q /\ Precedes fst t (h,j2) /\ (q,j) ≻* (h, j2) | t.
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
        (Hib : (p,i) ≻* (q,j) | l)
    : j' = j.
  Admitted.

  Lemma ancestor_in_before_dominating a p q (i j k : Tag) l
        (Hdom : Dom edge root q p)
        (Hanc : ancestor a q p) 
        (Hprec__a: Precedes fst ((p,i) :: l) (a,k))
        (Hprec__q: Precedes fst ((p,i) :: l) (q,j))
    : (q,j) ≻* (a,k) | (p,i) :: l.
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
        (Hib : (q,j) ≻* (a,k) | t)
    : exists a', Precedes fst t (a',k) /\ (p,i) ≻* (a',k) ≻* (q,j) | t.
  Admitted.

  Lemma find_loop_exit h a p i j k n l
        (Hpath : TPath (root,start_tag) (p,i) l)
        (Hpre : Prefix k j)
        (Hib : (a,k) ≻* (h, n :: j) | l)
        (Hprec : Precedes fst l (h, n :: j))
    : exists qe e, (a,k) ≻* (e,j) ≻* (qe,n :: j) ≻* (h, n :: j) | l /\ (e,j) ≻ (qe,n :: j) | l /\ exit_edge h qe e.
  Admitted.
  
  Lemma tpath_deq_loop_prefix p q i j t
        (Hdeq : deq_loop p q)
        (Hpath : TPath' t)
        (Hpre : Prefix j i)
    : (q,j) ≻* (p,i) | t.
  Admitted.
  
  Lemma tpath_tpath' r i0 p i t
        (Hpath : TPath (r,i0) (p,i) t)
    : TPath' t.
  Proof.
    unfold TPath'. eapply path_back in Hpath as Hback. eapply path_front in Hpath as Hfront.
    rewrite Hfront,Hback. assumption.
  Qed.

  Hint Resolve tpath_tpath'.
  Hint Resolve precedes_in.

  Lemma dom_dom_in_between p q r i j k l
        (Hdom1 : Dom edge root r q)
        (Hdom2 : Dom edge root q p)
        (Hpath : TPath' l)
        (Hnd : NoDup l)
    : (p,i) ≻* (q,j) ≻* (r,k) | l.
  Admitted.
  
  Lemma loop_cutting q p t
        (Hpath : CPath q p t)
        (Hnoh : forall h, loop_contains h q -> h ∉ t)
    : exists t', Path a_edge q p t'.
  Admitted.

  Lemma tpath_exit_nin h q e n j t
        (Hpath : TPath (root, start_tag) (q,n :: j) t)
        (Hloop : loop_contains h q)
        (Hexit : exited h e)
    : (e,j) ∉ t.
  Proof.
  Admitted.
  
  Lemma loop_cutting_elem q p t i j
        (Hpath : TPath' ((p,i) :< t))
        (Hib : (p,i) ≻* (q,j) | (p,i) :: t)
        (Hnoh : forall h k, loop_contains h q -> ~ (p,i) ≻* (h,k) ≻* (q,j) | (p,i) :: t)
    : exists t', Path a_edge q p t'.
  Admitted.

  Lemma exit_cascade u p t i j k
        (Hdom : Dom edge root u p)
        (Hprec : Precedes fst ((p,i) :: t) (u,j))
        (Hpath : TPath' ((p,i) :< t))
    : forall h, loop_contains h u -> ~ (p,i) ≻* (h,k) ≻* (u,j) | (p,i) :: t.
    (* otw. there would be a path through this q to p without visiting u *)
    (* this could even be generalized to CPaths *)
    (* TODO: lift on tpaths, on cpaths we might have duplicates, thus it doesn't work there *)
  Admitted.
  
End tagged.
