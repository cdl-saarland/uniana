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

Require Util Graph Evaluation Unchanged Disjoint UniquePI.

Module Uniana.
  Import Util Evaluation.Evaluation Disjoint.Disjoint Unchanged.Unchanged UniquePI.UniquePI.
  
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

  Definition uni_concr (u : Uni) : Hyper :=
    fun ts => forall t t', ts t -> ts t' ->
                   forall x p i s s', In (p, i, s) (`t) ->
                                 In (p, i, s') (`t') ->
                                 u p x = true -> s x = s' x.
  
  Definition uni_trans (uni : Uni) (upi : Upi) (unch : Unch) : Uni :=
    fun p
    => if p == root then uni root
      else fun x => ((join_andb (map (fun spl
                                   => match spl with
                                       (s, x) => uni s x
                                     end)
                                  (splits p ++ loop_splits p)))
                    && (join_andb (map (fun q => abs_uni_eff (uni q) x) (preds p)))
                    && (join_andb (map (fun q => upi_trans upi uni q p) (preds p)))
                 )
                 || join_orb (map (fun q => (q <>b p) && uni q x && upi_trans upi uni q p)
                                 (unch_trans unch p x)).

  Lemma uni_trans_root_inv :
    forall uni hom unch x, uni_trans uni hom unch root x = uni root x.
  Proof.
    intros.
    unfold uni_trans.
    destruct (equiv_dec root root).
    reflexivity.
    exfalso. apply c. reflexivity.
  Qed.

  
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

  Ltac solve_pair_eq :=
    repeat lazymatch goal with
           | [ H : ?a = (?b,?c) |- _ ] => destruct a; inversion H; clear H
           | _  => subst; eauto
           end.

  Ltac simpl_nl :=
    repeat lazymatch goal with
           | [ |- context[ne_front (nlcons ?a ?l)]] => rewrite nlcons_front
           | [ |- context[ne_to_list (_ :<: _)]] => rewrite nlcons_necons
           | [ |- context[ne_to_list (nlcons _ _)]] => rewrite <-nlcons_to_list
           end.

  Ltac simpl_nl' H := 
    repeat lazymatch type of H with
           | context[ne_front (nlcons ?a ?l)] => rewrite nlcons_front in H
           | context[ne_to_list (_ :<: _)] => rewrite nlcons_necons in H
           | context[ne_to_list (nlcons _ _)] => rewrite <-nlcons_to_list in H
           end.
        

(*  Hint Rewrite nlcons_front nlcons_necons nlcons_to_list : nl_ne.*)

  Lemma eff_eq_trace_eq p1 p2 q i1 i2 j s1 s2 r1 r2 l1 l2:
    eff (q,j,r1) = eff (q,j,r2)
    -> Tr ((p1,i1,s1) :<: nlcons (q,j,r1) l1)
    -> Tr ((p2,i2,s2) :<: nlcons (q,j,r2) l2)
    -> p1 = p2 /\ i1 = i2.
  Proof.
    intros.
    split; inversion H0; inversion H1;
    solve_pair_eq; simpl_nl' H5; simpl_nl' H9; rewrite H in H5; rewrite H5 in H9;
      inversion H9;eauto.
  Qed.

  Lemma postfix_rcons_trace_eff l k k' l' :
    Tr l'
    -> Postfix ((l :r: k) :r: k') l'
    -> eff k' = Some k.
  Proof.
  Admitted.

  Lemma disjoint_map_fst {A B : Type} (l1 l2 : list (A*B)) (l1' l2' : list A) :
    l1' = map fst l1
    -> l2' = map fst l2
    -> Disjoint l1' l2'
    -> Disjoint l1 l2.
  Admitted.
  
  Lemma postfix_rm_state_ex_state {A B : Type} l l' (a:A) :
    inhabited B
    -> Postfix (l :r: a) (ne_map fst l')
    -> exists l0 (b:B), Postfix (l0 :r: (a,b)) l' /\ l = map fst l0.
  Admitted.

  Lemma prefix_trace (l l' : ne_list Conf) :
    Prefix l l' -> Tr l' -> Tr l.
  Admitted.

  Lemma prefix_incl {A : Type} :
    forall l l' : list A, Prefix l l' -> incl l l'.
  Admitted.

  Definition option_fst {A B : Type} (ab : option (A*B)) : option A :=
    match ab with
    | Some ab => Some (fst ab)
    | _ => None
    end.
    
  Lemma not_same_step_disj_post q j r p i i' s q' j' r' s' l1 l2 l01 l02 S' s1' s2'
        (Hstep : eff (q, j, r) = Some (p, i, s))
        (Hstep' : eff (q', j', r') = Some (p, i, s'))
        (Hneq : q =/= q')
        (Htr1 : Tr (nlcons (q,j,r) l1))
        (Htr2 : Tr (nlcons (q',j',r') l2))
        (Hpost1 : Postfix (l01 :r: (S', i', s1')) (nlcons (q,j,r) l1))
        (Hpost2 : Postfix (l02 :r: (S', i', s2')) (nlcons (q',j',r') l2))
        (Hdisj : Disjoint (map fst l01) (map fst l02))
        (Hsplit : option_fst (eff (S', i', s1')) = option_fst (eff (S', i', s2'))) : False.
  Proof.  
    destruct l01, l02.
    --- (* Show q = S' = q' contradiction! *)
      cbn in Hpost1,Hpost2. rewrite <-nlcons_to_list in Hpost1,Hpost2.
      eapply postfix_hd_eq in Hpost1.
      eapply postfix_hd_eq in Hpost2.
      apply Hneq. clear - Hpost1 Hpost2. inversion Hpost1. inversion Hpost2. subst q q'.
      reflexivity.
    --- (* Show pi ∈ l02 contradiction *)
      assert (Hcr := cons_rcons p0 l02).      
      destruct Hcr as [p0' [l02' Hcr]].
      eapply ivec_fresh;[| |reflexivity].
      +++ instantiate (4:=(exist _ (nlcons (q',j',r') l2) _ )). cbn. simpl_nl. eauto.
      +++ cbn. 
          rewrite Hcr in Hpost2.
          instantiate (1:= snd p0').
          enough (p0' = (p,i,snd p0')).
          {  
            rewrite H in *. eapply postfix_incl. apply Hpost2.
            eapply In_rcons. right. apply In_rcons. left. reflexivity.
          }
          eapply postfix_rcons_trace_eff in Hpost2; eauto.
          setoid_rewrite Hpost2 in Hsplit.
          cbn in Hpost1. rewrite <-nlcons_to_list in Hpost1.
          eapply postfix_hd_eq in Hpost1 as Hpost1'. setoid_rewrite Hpost1' in Hsplit.
          rewrite Hstep in Hsplit. clear - Hsplit. inversion Hsplit. destruct p0',p0. inversion H0.
          subst. cbn. reflexivity.
    --- (* Show pi ∈ l01 contradiction! *)
      assert (Hcr := cons_rcons p0 l01).
      destruct Hcr as [p0' [l01' Hcr]].
      eapply ivec_fresh;[| |reflexivity].
      +++ instantiate (4:=(exist _ (nlcons (q,j,r) l1) _ )). cbn.
          rewrite nlcons_front. eauto.
      +++ cbn. 
          rewrite Hcr in Hpost1.
          instantiate (1:= snd p0').
          enough (p0' = (p,i,snd p0')).
          {  
            rewrite H in *. eapply postfix_incl. apply Hpost1.
            eapply In_rcons. right. apply In_rcons. left. reflexivity.
          }
          eapply postfix_rcons_trace_eff in Hpost1; eauto.
          setoid_rewrite Hpost1 in Hsplit.
          cbn in Hpost2. rewrite <-nlcons_to_list in Hpost2.
          eapply postfix_hd_eq in Hpost2 as Hpost2'. setoid_rewrite Hpost2' in Hsplit.
          rewrite Hstep' in Hsplit. clear - Hsplit. inversion Hsplit.
          destruct p0',p0. inversion H0. subst.
          cbn. reflexivity.
    --- (* exists qq ∈ l01 ∩ l02 contradiction! *)
      cbn.
      assert (Hcr1 := cons_rcons p0 l01).
      destruct Hcr1 as [p0' [l01' Hcr1]].
      assert (Hcr2 := cons_rcons p1 l02).
      destruct Hcr2 as [p1' [l02' Hcr2]].
      rewrite Hcr1 in Hpost1.
      rewrite Hcr2 in Hpost2.
      destruct p0',p1'.
      enough (p2 = p3).
      {
        rewrite Hcr1 in Hdisj. rewrite Hcr2 in Hdisj.
        clear - Hdisj H. subst p2.
        eapply Hdisj; unfold rcons in *; rewrite map_app in *; cbn in *.
        1: fold (rcons (map fst l02') p3).
        2: fold (rcons (map fst l01') p3).
        all: eapply In_rcons; left; eauto.
      }
      eapply postfix_rcons_trace_eff in Hpost1; eauto.
      eapply postfix_rcons_trace_eff in Hpost2; eauto.
      setoid_rewrite Hpost1 in Hsplit.
      setoid_rewrite Hpost2 in Hsplit.
      cbn in Hsplit. 
      inversion Hsplit; eauto.
      Unshelve. all: cbn; eauto.
  Qed.

  Lemma splits_is_branch br x p :
    In (br,x) (splits p) -> is_branch br x.
  Proof.
    intro HSsplit.
    eapply splits_spec in HSsplit. unfold DisjointBranch in HSsplit. firstorder.
  Qed.

  Lemma loop_splits_is_branch :
    forall (br : Lab) (x : Var) (p : Lab), In (br, x) (loop_splits p) -> is_branch br x.
  Proof.
    intros. eapply loop_splits_spec in H. firstorder.
  Qed.

  Parameter inh_state : inhabited State.

  Lemma front_eff_ex_succ l k1 k2 k :
    Tr l
    -> In k l
    -> ne_front l = k1
    -> eff k1 = Some k2
    -> exists k', eff k = Some k'.
  Proof.
    intros l' Htr Hfront Heff.
    induction l'.
  Admitted.

  Lemma last_common_lab_splits q1 j1 r1 q2 j2 r2 br p i s1 s2 l1 l2 :
    let l1' := nlcons (q1,j1,r1) l1 in
    let l2' := nlcons (q2,j2,r2) l2 in
    last_common (ne_map fst (ne_map fst l1')) (ne_map fst (ne_map fst l2')) br
    -> q1 =/= q2
    -> Tr ((p,i,s1) :<: l1')
    -> Tr ((p,i,s2) :<: l2')
    -> exists x, In (br,x) (splits p).
  Admitted.

  Lemma postfix_path `{Graph} l p q q' l' :
    Path q' q l'
    -> Postfix (l :r: p) l'
    -> Path p q (nl_rcons l p).
  Admitted.
  Lemma trace_path l :
    Tr l -> Path root (fst (fst (ne_front l))) (ne_map fst (ne_map fst l)).
  Admitted.
  Lemma postfix_map {A B : Type} (f : A -> B) :
    forall l l', Postfix l l' -> Postfix (map f l) (map f l').
  Admitted.
  Lemma map_rcons {A B : Type} (f : A -> B) :
    forall a l, map f (l :r: a) = map f l :r: (f a).
  Admitted.
  Lemma to_list_ne_map {A B : Type} (f : A -> B) (l : ne_list A) :
    map f l = ne_map f l.
  Admitted.
  
  Definition Tr' (l : ne_list Conf) :=
    exists l', Tr l' /\ Postfix l l'.

  Definition innermost_loop p qh :=
    in_loop p qh /\ forall qh', in_loop p qh -> in_loop qh qh'.

  Lemma tag_eq_ex_innermost_lh q q' j r r' l l' p i :
    Tr' ((q',j,r') :<: nl_rcons l (q,j,r))
    -> In (p,i) l'
    -> l' = map fst l
    -> i = j \/ exists lh, innermost_loop p lh /\ In lh (map fst (map fst l)).
  Admitted.
  
  Lemma disj_no_loopheads p i s1 s2 q r1 r2 l1 l2 qh :
    Tr' ((p,i,s1) :<: nl_rcons l1 (q,i,r1))
    -> Tr' ((p,i,s2) :<: nl_rcons l2 (q,i,r2))
    -> Disjoint (map fst l1) (map fst l2)
    -> loop_head qh
    -> In qh (map fst (map fst l1))
    -> ~ In qh (map fst (map fst l2)).
  Admitted.

  Lemma loop_head_tag_cases l q i r qh j :
    Tr' (nl_rcons l (q,i,r))
    -> loop_head qh
    -> In (qh,j) (map fst l)
    -> j = O :: i
      \/ match i with
        | nil => False
        | m :: i' => j = S m :: i'
        end.
  Admitted.

  Local Ltac last_common_splits_path_rcons l :=
    let H := fresh "H" in
    let Q := fresh "Q" in
    let H':= fresh "H" in
    lazymatch goal with
    | [ H : Postfix (?l1 :r: (?br,?i)) (ne_to_list (ne_map fst l)),
            Q : Tr l |- Path ?br ?q _ ]
      => apply id in H as H';
        eapply postfix_map with (f:=fst) in H;
        rewrite map_rcons in H;
        eapply trace_path in Q;
        eapply postfix_path in Q;[|rewrite <-to_list_ne_map;eauto];
        cbn in H;
        let P := fresh "P" in
        enough (fst (fst (ne_front l)) = q) as P;
        [setoid_rewrite P in Q; eassumption|];
        subst l; clear; rewrite nlcons_front; cbn; eauto
    end.
  
  Lemma in_fst {A B : Type} a (l : list (A * B)) :
    In a (map fst l)
    -> exists b, In (a,b) l.
  Admitted.

  Infix "∈" := In (at level 50).
  Notation "a '∉' l" := (~ a ∈ l) (at level 50).
                   
  Lemma last_common_splits q j r q' j' r' l l' p i s s' br :
    let l1 := nlcons ( q, j, r) l  in
    let l2 := nlcons (q',j',r') l' in
    last_common (ne_map fst l1) (ne_map fst l2) (br,i)
    -> q =/= q'
    -> Tr l1
    -> Tr l2
    -> eff (q,j,r)    = Some (p,i,s)
    -> eff (q',j',r') = Some (p,i,s')
    -> exists x, In (br,x) (splits p).
  Proof.
    intros l1 l2 [l1' [l2' [Hpost1 [Hpost2 [Hdisj [Hnin1 Hnin2]]]]]] Hneq Htr1 Htr2 Hstep Hstep'.
    setoid_rewrite <-splits_spec.
    assert (Hbr := branch_spec br).
    unfold DisjointBranch. unfold is_branch.
    destruct (branch br);[destruct p0,p0,p0|]. all: cycle 1.
    - exfalso.
      apply id in Hpost1 as Hpost1'. apply id in Hpost2 as Hpost2'.
      apply postfix_rm_state_ex_state in Hpost1' as [l01 [s1' [Hpost1' Hposteq1]]].
      apply postfix_rm_state_ex_state in Hpost2' as [l02 [s2' [Hpost2' Hposteq2]]].
      2,3: apply inh_state.
      subst l1' l2'.
      eapply not_same_step_disj_post with (q:=q); eauto.
      eapply front_eff_ex_succ in Hstep as [k Hk]; [|apply Htr1| |].
      2: eapply postfix_incl; [apply Hpost1'|apply In_rcons;left;eauto].
      2: subst l1; rewrite nlcons_front; reflexivity.
      eapply front_eff_ex_succ in Hstep' as [k' Hk'];[|apply Htr2| |].
      2: eapply postfix_incl; [apply Hpost2'|apply In_rcons;left;eauto].
      2: subst l2; simpl_nl; reflexivity.
      specialize (Hbr _ _ _ _ _ _ Hk Hk'). rewrite Hk,Hk'.
      destruct k as [[pp ii] ss]. destruct k' as [[qq jj] rr].
      cbn in Hbr. subst pp.
      eapply ivec_det with (i:=ii) (i':=jj) in Hk; eauto. subst ii.
      cbn. reflexivity.
    - exists v0, q, q', ((map fst l1')), ((map fst l2')).
      split_conj; eauto using step_conf_implies_edge.
      + last_common_splits_path_rcons l1.
      + last_common_splits_path_rcons l2.
      + split.
        * intros a Hina.
          apply in_fst in Hina. destruct Hina as [b Hina1].
          intro N. apply in_fst in N. destruct N as [b' Hina2].
          eapply id in Hina1 as Hina1'. eapply id in Hina2 as Hina2'.
          eapply tag_eq_ex_innermost_lh with (j:=i) in Hina1.
          eapply tag_eq_ex_innermost_lh with (j:=i) in Hina2.
          destruct Hina1; destruct Hina2. 
          -- subst b b'. eapply Hdisj; eauto.
          -- (* tag in one trace is the same, but in the other there it is in an inner loop C! *)
            Lemma lab_tag_same_length p i j l l' :
              Tr l
              -> Tr l'
              -> (p,i) ∈ (map fst l)
              -> (p,j) ∈ (map fst l')
              -> length i = length j.
            Admitted.

            Lemma tag_length_inbetween p i s l q r q' j :
              Tr' ((p,i,s) :<: nl_rcons l (q,i,r))
              -> (q',j) ∈ (map fst l)
              -> length i <= length j.
              (* because if we would exit a loop, we could never achieve to get the same tag again *)
            Admitted.

            (*Inductive Tc : ne_list Coord -> Prop :=
            | TcInit : Tc (ne_single (root,start_tag))
            | TcStep : Tc l -> p --> q -> Tc ((p,i) :<: l)*)
              
            
            admit.
          -- (* tag in one trace is the same, but in the other there it is in an inner loop C! *)
            admit.
          -- (* in both traces a is in an inner loop -> the loop header is in both traces C! *)
            admit.
          -- (* technical goal: Tr' ((p, i, s) :<: nl_rcons ?l (br, i, ?r0)) *)
            admit.
          -- (* technical goal: l2' = map fst ?l *)
            admit.
          -- (* technical goal: Tr' ((p, i, s') :<: nl_rcons ?l (br, i, ?r0)) *)
            admit.
          -- (* technical goal: l1' = map fst ?l0 *)
            admit.
        * admit. (* analogous to the previous case *)
  Admitted.

  Lemma ne_back_trace t :
    Tr t -> exists s, ne_back t = (root,start_tag,s).
  Proof.
    intro Htr.
    induction Htr; firstorder. exists s. cbn; reflexivity.
  Qed.

  Lemma ne_back_map {A B : Type} (f : A -> B) l :
    ne_back (ne_map f l) = f (ne_back l).
  Proof.
    induction l; firstorder.
  Qed.

  Lemma lc_loop_split_of_split p s1 s2 q1 q2 j1 j2 r1 r2 br br' i i' x l1 l2 :
    let l1' := nlcons (q1,j1,r1) l1 in
    let l2' := nlcons (q2,j2,r2) l2 in
    In (br,x) (splits p)
    -> Tr ((p,i,s1) :<: l1')
    -> Tr ((p,i,s2) :<: l2')
    -> q1 =/= q2
    -> i =/= i'
    -> last_common (ne_map fst l1') (ne_map fst l2') (br',i')
    -> exists x', In (br',x') (loop_splits br).
  Admitted.
  
  Lemma uni_correct :
    forall uni upi unch ts,
        sem_hyper (red_prod (red_prod (uni_concr uni) (upi_concr upi)) (lift (unch_concr unch))) ts ->
        uni_concr (uni_trans uni upi unch) ts.
  Proof.
    intros uni upi unch ts Hred.
    unfold sem_hyper in Hred.
    destruct Hred as [ts' [Hconcr Hstep]].
    unfold uni_concr.
    intros t t' Hsem Hsem' x p i s s' HIn HIn' Htrans.

    assert (upi_concr (upi_trans upi uni) ts) as HCupi. {
      apply upi_correct. 
      destruct Hconcr as [[_ Hhom] _].
      exists ts'; auto.
    }

    assert (unch_concr (unch_trans unch) t) as HCunch. {
      destruct Hconcr as [[_ _] Hunch].
      unfold lift in *; subst.
      apply unch_correct. assumption.
    } 
    
    assert (unch_concr (unch_trans unch) t') as HCunch'. {
      destruct Hconcr as [[_ _] Hunch].
      unfold lift in *; subst.
      apply unch_correct. assumption.
    }

    destruct Hconcr as [[HCuni HCupi'] _].

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
        eapply prefix_trans with (l2:=`t1) (l3:=`t) in rp; eauto.
        apply prefix_cons_in in rp. eapply tag_inj in HIn; [| apply rp]. subst s0. eauto.
      + specialize (root_prefix t2) as [s0 rp]. apply root_start_tag in HIn as rst. subst i.
        eapply prefix_cons_in in rp as rp'.
        assert (Prefix (`t2) (`t')) as pre_t.
        { rewrite Hteq2. cbn. econstructor. econstructor. }
        eapply prefix_trans with (l2:=`t2) (l3:=`t') in rp; eauto.
        apply prefix_cons_in in rp. eapply tag_inj in HIn'; [| apply rp]. subst s0. eauto.
    - conv_bool.
      destruct Htrans as [Htrans | Hunch].
      (* The uni/hom case *)
      + destruct Htrans as [[Hsplit Hpred] Hupi].
        rewrite Hteq1 in HIn. rewrite Hteq2 in HIn'.
        eapply in_pred_exists in HIn; try eassumption; [|setoid_rewrite <-Hteq1; exact (proj2_sig t)].
        eapply in_pred_exists in HIn'; try eassumption;[|setoid_rewrite <-Hteq2; exact (proj2_sig t')].
        destruct HIn as [q [j [r [HIn Hstep]]]].
        destruct HIn' as [q' [j' [r' [HIn' Hstep']]]].
        assert (List.In q (preds p)) as Hqpred by (eauto using step_conf_implies_edge).
        cut (q' = q); intros; subst.
        * cut (j' = j); intros; subst.
          -- eapply (local_uni_corr (uni q) q j p i r r' s s'); try eassumption.
             ** unfold uni_state_concr. intros.
                unfold uni_concr in HCuni .
                eapply (HCuni _ _ Hts1 Hts2 x0 q j); eassumption.
             ** eapply join_andb_true_iff in Hpred; try eassumption.
          -- (* unique preceding instances *)
            eapply join_andb_true_iff in Hupi; try eassumption.
            assert (p =/= q) by (symmetry; eauto using step_conf_implies_edge, no_self_loops).
            symmetry.
            eapply HCupi; [ eapply Hsem | eapply Hsem' | eassumption | | ].
            1: rewrite Hteq1. 2: rewrite Hteq2.
            all: cbn; rewrite nlcons_to_list; eapply precedes_step; eauto.
            all: rewrite <-nlcons_necons.
            ++ setoid_rewrite <-Hteq1. destruct t; cbn; eauto.
            ++ setoid_rewrite <-Hteq2. destruct t'; cbn; eauto.
        * (* disjoint paths! *)
          destruct (q == q') as [ Heq | Hneq ]; [ eauto | exfalso ].
          assert (In q' (preds p)) as Hqpred' by (eauto using step_conf_implies_edge).
          
          pose (tq1 := nlcons (q,j,r)     (prefix_nincl (q,j,r) (`t1))).
          pose (tq2 := nlcons (q',j',r') (prefix_nincl (q',j',r') (`t2))).
          assert (Tr tq1) as Htr1. {
            eapply prefix_trace. subst tq1. rewrite <-nlcons_to_list.
            eapply prefix_nincl_prefix.
            eauto. destruct t1; eauto.
          }
          assert (Tr tq2) as Htr2. {
            eapply prefix_trace. subst tq2. rewrite <-nlcons_to_list.
            eapply prefix_nincl_prefix.
            eauto. destruct t2;eauto.
          }
          assert (exists (si : Lab * Tag),
                        last_common (ne_map fst tq1) (ne_map fst tq2) si) as [[S' I'] LC_lt].
          {
            eapply ne_last_common. repeat rewrite ne_back_map.
            eapply ne_back_trace in Htr1 as [s1 Htr1].
            eapply ne_back_trace in Htr2 as [s2 Htr2].
            setoid_rewrite Htr1. setoid_rewrite Htr2. cbn;eauto.
          }
          assert (exists s, last_common (ne_map fst (ne_map fst tq1))
                                      (ne_map fst (ne_map fst tq2)) s) as [S LC_l].
             { eapply ne_last_common. admit. (* common root *) }
          decide' (i == I').
          -- apply id in LC_lt as LC_lt'.
             destruct LC_lt as [l1' [l2' [Hpost1 [Hpost2 [Hdisj [Hnin1 Hnin2]]]]]].
             eapply last_common_splits in LC_lt'; eauto.
             destruct LC_lt' as [x' HSsplit].
             ++ eapply join_andb_true_iff in Hsplit; eauto; [|apply in_or_app;left;eauto].
                cbn in Hsplit. conv_bool. 
                apply postfix_rm_state_ex_state in Hpost1 as [l01 [s1' [Hpost1 Hposteq1]]].
                apply postfix_rm_state_ex_state in Hpost2 as [l02 [s2' [Hpost2 Hposteq2]]].
                2,3: apply inh_state.
                eapply HCuni in Hsplit. all: cycle 1.
                ** exact Hts1.
                ** exact Hts2.
                ** eapply prefix_incl;eauto. eapply prefix_trans.
                   --- eapply prefix_nincl_prefix. eapply postfix_incl.
                       eapply Hpost1. eapply In_rcons;eauto.
                   --- subst tq1. rewrite <-nlcons_to_list. eapply prefix_nincl_prefix; eauto.
                   --- left. reflexivity.
                ** eapply prefix_incl;eauto. eapply prefix_trans.
                   --- eapply prefix_nincl_prefix. eapply postfix_incl.
                       eapply Hpost2. eapply In_rcons;eauto.
                   --- subst tq2. rewrite <-nlcons_to_list. eapply prefix_nincl_prefix; eauto.
                   --- left. reflexivity.
                ** eapply splits_is_branch in HSsplit as HSbranch.
                   assert (exists k, eff (S', i, s1') = Some k) as [k Hk] by admit.
                   (* because Tr ((p,i,s) ... (S',i,s')) *)
                   assert (exists k', eff (S', i, s2') = Some k') as [k' Hk'] by admit.
                   eapply branch_eff_eq in Hsplit; eauto.
                   subst l1' l2'.
                   eapply not_same_step_disj_post with (q:=q); eauto.
                   rewrite Hk, Hk'. cbn. 
                   unfold option_fst. rewrite Hsplit. reflexivity.
          -- eapply last_common_lab_splits with (p:=p) in LC_l; eauto;
               [|admit|admit]. (* easy Tr goals *)
             destruct LC_l as [X HSsplit].
             apply id in LC_lt as LC_lt'.
             eapply lc_loop_split_of_split in LC_lt; eauto; [|admit|admit]. (* easy Tr goals *)
             destruct LC_lt as [X' HSsplit'].
             destruct LC_lt' as [l1' [l2' [Hpost1 [Hpost2 [Hdisj [Hnin1 Hnin2]]]]]].
             ++ eapply join_andb_true_iff in Hsplit; [|apply in_or_app;right; eauto]. cbn in Hsplit.
                conv_bool.                 
                eapply postfix_rm_state_ex_state in Hpost1 as [l01 [s1' [Hpost1 Hposteq1]]].
                apply postfix_rm_state_ex_state in Hpost2 as [l02 [s2' [Hpost2 Hposteq2]]].
                2-5: eauto using inh_state, start_tag.
                eapply HCuni in Hsplit. all: cycle 1.
                ** exact Hts1.
                ** exact Hts2.
                ** eapply prefix_incl;eauto. eapply prefix_trans with (l2:=tq1).
                   --- eapply prefix_nincl_prefix. eapply postfix_incl.
                       eapply Hpost1. eapply In_rcons;eauto.
                   --- subst tq1. rewrite <-nlcons_to_list. eapply prefix_nincl_prefix; eauto.
                   --- left. reflexivity.
                ** eapply prefix_incl;eauto. eapply prefix_trans with (l2:=tq2).
                   --- eapply prefix_nincl_prefix. eapply postfix_incl.
                       eapply Hpost2. eapply In_rcons;eauto.
                   --- subst tq2. rewrite <-nlcons_to_list. eapply prefix_nincl_prefix; eauto.
                   --- left. reflexivity.
                ** eapply loop_splits_is_branch in HSsplit' as HSbranch.
                   assert (exists k, eff (S', I', s1') = Some k) as [k Hk] by admit.
                   (* because Tr ((p,i,s) ... (S',I',s')) *)
                   assert (exists k', eff (S', I', s2') = Some k') as [k' Hk'] by admit.
                   eapply branch_eff_eq in Hsplit; eauto.
                   subst l1' l2'.
                   eapply not_same_step_disj_post with (q:=q); eauto. 
                   rewrite Hk,Hk'. cbn. rewrite Hsplit. reflexivity.
        (* The unch case *)
      + rename Hunch into H.
        eapply join_orb_true_iff in H.
        destruct H as [u H].
        conv_bool.
        destruct H as [Hunch [[Hneq' Huni] Hupi]].
        specialize (HCunch p i s u x HIn Hunch).
        specialize (HCunch' p i s' u x HIn' Hunch).
        destruct HCunch as [j [r [Hprec Heq]]]; try eassumption.
        destruct HCunch' as [j' [r' [Hprec' Heq']]]; try eassumption.
        rewrite <- Heq. rewrite <- Heq'.
        cut (j' = j); intros.
        * subst j'. eapply HCuni. eapply Hts1. eapply Hts2. 3: eauto.
          all: eapply precedes_step_inv.
          -- rewrite <-nlcons_to_list. setoid_rewrite Hteq1 in Hprec. apply Hprec.
          -- rewrite <-nlcons_necons, <-Hteq1. destruct t; eauto.
          -- cbn. eauto.
          -- rewrite <-nlcons_to_list. setoid_rewrite Hteq2 in Hprec'. apply Hprec'.
          -- rewrite <-nlcons_necons, <-Hteq2. destruct t'; eauto.
          -- cbn;eauto.
        * symmetry. eapply (HCupi _ _ Hsem Hsem'); eauto. 
  Qed.


End Uniana.
      