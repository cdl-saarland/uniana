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

Require Util Graph Evaluation Unchanged Disjoint.

Module Splits.
  
  Import Util Evaluation.Evaluation Disjoint.Disjoint.

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

  
  Lemma front_eff_ex_succ l k1 k2 k :
    Tr l
    -> In k l
    -> ne_front l = k1
    -> eff k1 = Some k2
    -> exists k', eff k = Some k'.
  Proof.
    intros Htr Hin Hfront Heff.
    assert (exists l', Prefix (nlcons k l') l) as [l' Hpre].
    {
      clear - Hin. induction l.
      - destruct Hin;[subst|contradiction]. exists nil; cbn. econstructor.
      - destruct Hin;[subst;exists l; simpl_nl;econstructor|].
        eapply IHl in H. destruct H as [l' H]. exists l'. cbn; econstructor; assumption.
    }
    clear Hin.
    dependent induction Hpre.
    - eapply ne_to_list_inj in x. rewrite <-x in Heff. simpl_nl' Heff. eauto.
    - clear IHHpre Heff. 
      rewrite nlcons_to_list in x. eapply ne_to_list_inj in x. rewrite <-x in Htr.
      clear x.
      dependent induction Htr.
      + exfalso. destruct l'0; cbn in x;[|congruence].
        inversion Hpre;destruct l';cbn in H1; congruence.
      + inversion Hpre; subst; simpl_nl' x; cbn in x; inversion x; subst.
        * simpl_nl' H. eexists; exact H.
        * eapply IHHtr; eauto.
  Qed.

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

  Local Ltac last_common_splits_path_rcons l :=
    let H := fresh "H" in
    let Q := fresh "Q" in
    let H':= fresh "H" in
    lazymatch goal with
    | [ H : Postfix (?l1 :r: (?br,?i)) (ne_to_list (ne_map fst l)),
            Q : Tr l |- CPath ?br ?q _ ]
      => apply id in H as H';
        eapply postfix_map with (f:=fst) in H;
        rewrite map_rcons in H;
        eapply Tr_CPath in Q;
        eapply postfix_path in Q;[|rewrite <-to_list_ne_map;eauto];
        cbn in H;
        let P := fresh "P" in
        enough (fst (fst (ne_front l)) = q) as P;
        [setoid_rewrite P in Q;cbn in Q; eassumption|];
        subst l; clear; rewrite nlcons_front; cbn; eauto
    end.


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
      apply postfix_ex_unmapped_postfix in Hpost1' as [l01 [s1' [Hpost1' Hposteq1]]].
      apply postfix_ex_unmapped_postfix in Hpost2' as [l02 [s2' [Hpost2' Hposteq2]]].
      2,3: econstructor; apply zero.
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
            (* or we are re-entering a loop. but then we would get a tag different from i C! *)
            admit.
          -- (* tag in one trace is the same, but in the other there it is in an inner loop C! *)
            admit.
          -- (* in both traces a is in an inner loop -> the loop header is in both traces C! *)
            admit.
          -- (* technical goal: Tr' ((p, i, s) :<: nl_rcons ?l (br, i, ?r0)) *)
            admit.
          -- (* technical goal: Tr' ((p, i, s') :<: nl_rcons ?l (br, i, ?r0)) *)
            admit.
        * admit. (* analogous to the previous case *)
  Admitted.
  
End Splits.