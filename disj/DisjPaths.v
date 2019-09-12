Require Export DisjDef MaxPreSuffix.

Section disj.
  Context `{C : redCFG}.
  
  Notation "p '-a>b' q" := (a_edge p q) (at level 55).
  Notation "p '-a>' q" := (p -a>b q = true) (at level 55).
  Notation "p '-->b' q" := (edge p q) (at level 55).
  Notation "p '-->' q" := (p -->b q = true) (at level 55, right associativity).
  
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

  Lemma geq_tag_suffix_deq (p q : Lab) l t i j
        (Hpath : TPath (root,start_tag) (q,j) t)
        (Hpost : Postfix l t)
        (HForall : Forall (DecPred (fun xl => |j| <= |snd xl|)) l)
        (Hel : (p,i) ∈ l)
    : deq_loop p q.
  Proof.
  Admitted.

  Lemma geq_tag_suffix_tag_tl_eq (p q : Lab) l t i j
        (Hpath : TPath (root,start_tag) (q,j) t)
        (Hpost : Postfix l t)
        (HForall : Forall (DecPred (fun xl => |j| <= |snd xl|)) l)
        (Hel : (p,i) ∈ l)
    : take_r (| tl j |) i = tl j.
  Admitted.

  Lemma while'_front_In (A : Type) (e : A -> A -> bool) (P : decPred A) (l : ne_list A) (a b : A)
        (Hpath : Path e a b l)
        (HP : P b)
    : b ∈ while' P l.
  Proof.
    destruct Hpath;cbn.
    - decide (P a);try contradiction. left. auto.
    - decide (P c);try contradiction. left. auto.
  Qed.
  
  Lemma postfix_ex_cons
    : forall (A : Type) (l l' : list A) (a : A), Postfix l l' -> exists a' : A, Postfix (l :r: a') (l' :r: a).
  Proof.
    intros. eapply postfix_rev_prefix in H. eapply prefix_ex_cons in H. destructH.
    exists a'. eapply prefix_rev_postfix'. do 2 rewrite rev_rcons. eauto.
  Qed.

  Lemma eq_loop_same (h h' : Lab)
        (Heq : eq_loop h h')
        (Hl : loop_head h)
        (Hl' : loop_head h')
    : h = h'.
  Proof.
    eapply loop_contains_Antisymmetric.
    all: unfold eq_loop,deq_loop in *;destructH;eauto using loop_contains_self.
  Qed.
  
  Lemma entry_through_header h p q
        (Hnin : ~ loop_contains h p)
        (Hin : loop_contains h q)
        (Hedge : p --> q)
    : q = h.
  Admitted.
  

  Lemma ex_entry (h p q : Lab) (i j : Tag) t
        (Hin : innermost_loop h q)
        (Hnin : ~ loop_contains h p)
        (Hpath : TPath (root,start_tag) (q,j) t)
        (Hord : (q,j) ≻* (p,i) | t)
    : (h,0 :: tl j) ≻* (p,i) | t.
  Proof.
    remember (while' (DecPred (fun xl => |j| <= |snd xl|)) t) as t'.
    assert (Postfix t' t) as Hpost.
    { eapply while'_postfix;subst t';eauto. }
    assert (forall xl, xl ∈ t' -> loop_contains h (fst xl)) as Hloop.
    { intros. destruct xl as [x l]. eapply geq_tag_suffix_deq in H.
      4: subst t'; eapply while'_Forall.
      all: cbn;eauto;destruct Hin as [Hin _];eauto.
    } 
    inversion Hpost.
    - subst. eapply splinter_cons in Hord. eapply splinter_in in Hord.
      specialize (Hloop (p,i)).
      exploit Hloop.
      + rewrite H0; auto.
      + cbn in Hloop. contradiction.
    - subst l.
      specialize (rcons_destruct t') as Ht'.
      destruct Ht'. (* t' is not empty *)
      { enough ((q,j) ∈ t') as H00 by (rewrite H0 in H00;cbn in H00;contradiction).
        subst.
        eapply while'_front_In;eauto. cbn. omega. }
      destructH.
      destruct a0 as [h' k].
      eapply postfix_ex_cons in H1. destructH. erewrite H in H1.
      assert (h' = h); [|subst h'].
      { (*
         * h' is a header
         * it has an incoming edge from outside of h
         *)
        destruct a'.
        eapply entry_through_header;cycle 1.
        - destruct Hin as [Hin1 Hin2].
          enough (deq_loop h' h).
          { eapply H2. eapply loop_contains_self. eapply loop_contains_loop_head;auto. }
          eapply deq_loop_trans; eauto.
          + eapply geq_tag_suffix_deq. 2:eapply Hpost. all: eauto.
            * rewrite Heqt'. eapply while'_Forall.
            * rewrite H0. eapply In_rcons. left. auto.
          + eapply loop_contains_deq_loop;auto.
        - rewrite H0 in H1. 
          eapply postfix_path in H1;eauto 1.
          instantiate (1:=e).
          admit. (* inversion tactic for paths *)
        - eapply while'_max in H1;eauto. cbn in H1. contradict H1.
          admit. (* because depth = length of tag *)
      }
      eapply while'_max in H1 as Hmax;[|eauto]. cbn in Hmax.
      destruct a'. cbn in *. assert (|l| < |j|) as Hmax' by omega.
      assert (|j| <= |k|) as Hjk.
      { assert ((h,k) ∈ t') by (rewrite H0;eapply In_rcons;eauto).
        rewrite Heqt' in H2.
        eapply while'_forall in H2. cbn in H2. auto. }
      assert (|l| < |k|) by omega.
      eapply tag_entry_lt in H2.
      + destruct j.
        { exfalso. cbn in Hmax'. omega. }
        assert (j = tl k).
        { replace j with (tl (n :: j)) by (cbn;auto). erewrite <-geq_tag_suffix_tag_tl_eq.
          - rewrite take_r_tl;eauto. cbn. rewrite H2. cbn. cbn in Hmax. rewrite H2 in Hjk. cbn in Hjk. omega.
          - eauto.
          - eapply Hpost. 
          - subst t'. eapply while'_Forall.
          - rewrite H0. eapply In_rcons. left. eauto.
        }
        rewrite H2 in H3. cbn in H3. cbn. subst j k.
        clear - Hpost Heqt' H0 H Hpath Hord Hin Hnin.
        eapply postfix_eq in Hpost. destructH.
        rewrite H,Hpost.
        rewrite consAppend. 
        eapply splinter_app; eapply splinter_single.
        * rewrite H0. eapply In_rcons. auto.
        * eapply splinter_cons in Hord. eapply splinter_in in Hord.
          rewrite Hpost in Hord. eapply in_app_or in Hord. destruct Hord;auto.
          exfalso.
          rewrite Heqt' in *.
          eapply geq_tag_suffix_deq in Hpath;cycle 1.
          -- eapply while'_postfix. symmetry. eauto.
          -- rewrite Heqt'. eapply while'_Forall.
          -- rewrite Heqt'. eapply H1.
          -- eapply Hnin. eapply Hpath. eapply Hin.
      + rewrite H0 in H1. eapply postfix_path in H1;eauto.
        rewrite rcons_nl_rcons in H1. simpl_nl' H1.
        eapply path_nlrcons_edge in H1. simpl_nl' H1. eauto.
    (*
     * define t' as the maximal suffix of t with tag dim >= |j|.
     * then forall x ∈ t', deq_loop x q thus x ∈ h
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
      2: eapply last_common'_sym in Hlc.
      2,3: eapply lc_succ_rt1;eauto.
      rewrite Htag in Hinner.
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
