Require Export CFGdeq.

Section cfg.
  Context `{C : redCFG}.
  
  Notation "p '-a>b' q" := (a_edge p q) (at level 55).
  Notation "p '-a>' q" := (p -a>b q = true) (at level 55).
  Notation "p '-->b' q" := (edge p q) (at level 55).
  Notation "p '-->' q" := (p -->b q = true) (at level 55, right associativity).
  
  (** innermost_loops **)
  
  Definition innermost_loop h p : Prop := loop_contains h p /\ deq_loop h p.

  Definition innermost_loop_strict (h p : Lab)
    := loop_contains h p /\ h <> p /\ forall h', loop_contains h' p -> (loop_contains h' h \/ h' = p).
  
  Definition finType_sig_or_never (X : finType) (P : decPred X) : {x : X | P x} + {forall x : X, ~ P x}.
  Proof.
    remember (filter P (elem X)).
    destruct l.
    - right. intros ? ?. specialize (in_filter_iff P x (elem X)) as Hiff. rewrite <-Heql in Hiff.
      cbn in Hiff. eapply Hiff. split;eauto.
    - left. econstructor. specialize (in_filter_iff P e (elem X)) as Hiff.
      rewrite <-Heql in Hiff. cbn in Hiff. eapply Hiff. eauto.
  Qed.
  
  Definition ex_innermost_loop p
    := finType_sig_or_never (DecPred (fun h => innermost_loop h p)).
    
  Definition ex_innermost_loop_strict (p : Lab)
    : {h : Lab | innermost_loop_strict h p} + {forall h, ~ innermost_loop_strict h p}
    := finType_sig_or_never (DecPred (fun h => innermost_loop_strict h p)).

  Definition get_innermost_loop (p : Lab) : option Lab :=
    match ex_innermost_loop p with
    | inleft (exist _ h _) => Some h
    | inright _ => None
    end.

  Definition get_innermost_loop_strict (p : Lab) : option Lab :=
    match ex_innermost_loop_strict p with
    | inleft (exist _ h _) => Some h
    | inright _ => None
    end.
  
  Definition get_innermost_loop_dep (p : Lab) : option {h : Lab | loop_contains h p} :=
    match ex_innermost_loop p with
    | inleft (exist _ h H) => Some (exist _ h (match H with
                                              | conj Q _ => Q
                                              end))
    | inright _ => None
    end.                    
  
  Definition get_innermost_loop_strict_dep (p : Lab) : option {h : Lab | loop_contains h p} :=
    match ex_innermost_loop_strict p with
    | inleft (exist _ h H) => Some (exist _ h (match H with
                                              | conj Q _ => Q
                                              end))
    | inright _ => None
    end.

  Lemma innermost_loop_strict_unique (* unused *)(h h' p : Lab)
        (H : innermost_loop_strict h p)
        (Q : innermost_loop_strict h' p)
    : h = h'.
  Proof.
    unfold innermost_loop_strict in *. do 2 destructH.
    eapply H3 in Q0. destruct Q0;[|contradiction].
    eapply Q3 in H0. destruct H0;[|contradiction].
    eapply loop_contains_Antisymmetric;auto.
  Qed.

  Definition LPath := Path (fun h p => decision (innermost_loop_strict h p)).
  
  (** StrictPrefix **)

  Definition StrictPrefix' := 
    fun (A : Type) (l l' : ne_list A) => exists a : A, Prefix (a :<: l) l'.

  Lemma prefix_strictPrefix:
    forall (e : Lab) (x ϕ : ne_list Lab), Prefix ϕ x -> StrictPrefix' ϕ (e :<: x).
  Proof.
    intros e x ϕ Hϕ1.
    unfold StrictPrefix'. cbn.
    revert dependent e.
    induction Hϕ1; intros.
    - exists e; econstructor.
    - specialize(IHHϕ1 a). destructH. exists a0. econstructor. auto.
  Qed.

  Lemma StrictPrefix_well_founded (A : Type) : well_founded (@StrictPrefix' A).
  Proof.
    unfold well_founded.
    intros. 
    induction a.
    - econstructor. intros. unfold StrictPrefix' in *. destructH. inversion H;[congruence'|]. inversion H2.
    - constructor. intros.
      unfold StrictPrefix' in H.
      destructH. cbn in *. inversion H;subst.
      + eapply ne_to_list_inj in H3. subst. auto.
      + eapply IHa. unfold StrictPrefix'. exists a1. cbn. auto.
  Qed.
  
  Lemma find_some_strong (A : Type) `{Q:EqDec A eq} (f : A -> bool) (l : list A) (x : A) (Hnd : NoDup l)
    : find f l = Some x -> x ∈ l /\ f x = true /\ forall y, y ≻* x | l -> f y = true -> x = y.
  Proof.
    repeat split. 1,2: eapply find_some in H; firstorder.
    revert dependent x.
    induction l;intros.
    - inversion H0.
    - cbn in H.
      destruct (f a) eqn:E.
      + inversion H; subst. inversion H0;subst;auto.
        inversion Hnd; subst. exfalso; contradict H5. eapply splinter_incl;[eapply H4|]. firstorder 0.
      + destruct (a == y);[rewrite e in E;congruence|].
        inversion Hnd; subst. eapply IHl;eauto. inversion H0;subst;auto. congruence.
  Qed.

  (** LPath **)
  
  Lemma loop_LPath_helper p h π
        (Hpath : Path a_edge root p (p :<: π))
        (Hloop : loop_contains h p)
        (Hin : h ∈ π)
        (Hnolo : forall q : Lab, q ≻* h | π -> toBool _ (D:=decision (loop_contains q p)) = true -> h = q)
    : (forall h' : Lab, loop_contains h' p -> loop_contains h' h \/ h' = p).
  Proof.
    intros. eapply loop_contains_either in H as H';[|apply Hloop].
    destruct H';[|left;auto].
    decide (h' = p);[right;auto|]. 
    specialize (Hnolo h'). exploit Hnolo.
    - eapply subgraph_path' in Hpath;eauto using a_edge_incl.
      eapply loop_contains_splinter in Hpath;eauto.
      cbn in Hpath. inversion Hpath;subst;auto. inversion H2;subst;contradiction.
    - decide (loop_contains h' p); cbn in *;[congruence|contradiction].
    - subst. left. eapply loop_contains_self. eapply loop_contains_loop_head;eauto.
  Qed.
  
  Lemma loop_LPath h p
        (Hloop : loop_contains h p)
    : exists π, LPath h p π.
  Proof.
    specialize (a_reachability p) as Hreach.
    destructH. revert dependent p. revert dependent π.
    specialize (well_founded_ind (R:=(@StrictPrefix' Lab)) (@StrictPrefix_well_founded Lab)
                                 (fun π : ne_list Lab => forall p, loop_contains h p
                                                           -> Path a_edge root p π
                                                           -> exists (π0 : ne_list Lab), LPath h p π0))
      as WFind.
    eapply WFind.
    intros;clear WFind.
    destruct x.
    - inversion H1; subst p a e.
      eapply root_loop_root in H0. subst. repeat econstructor.
    - remember (find (fun h' => decision (loop_contains h' p)) x) as S.
      destruct S; symmetry in HeqS.
      + eapply find_some_strong in HeqS. destructH. decide (loop_contains e0 p);cbn in *;[|congruence].
        inversion H1;subst.
        decide (h = e).
        { subst;eexists;econstructor. }
        specialize (path_to_elem _ a_edge _ _ e0 x H6 HeqS0) as [ϕ [Hϕ0 Hϕ1]].
        specialize (H ϕ). exploit' H.
        { cbn. clear - Hϕ1.
          eapply prefix_strictPrefix;auto.
        } 
        specialize (H e0). exploit H.
        { clear - l H0 n HeqS0 HeqS3 H1.
          decide (e0 = h);[subst;eapply loop_contains_self;unfold loop_contains in H0;firstorder|].
          eapply loop_contains_either in H0 as H0'; eauto.
          destruct H0';[exfalso|auto].
          eapply (loop_LPath_helper) in HeqS3;auto. 2:exact H0. destruct HeqS3;[|contradiction].
          eapply loop_contains_Antisymmetric in H. exploit H. contradiction.
        } 
        destructH.        
        exists (e :<: π0).
        econstructor;cycle 1.
        * instantiate (1:=e0). decide (innermost_loop_strict e0 e);cbn;[auto|exfalso;contradict n0].
          unfold innermost_loop_strict. split;auto. split.
          -- eapply acyclic_path_NoDup in H1. clear - HeqS0 H1. inversion H1; subst.
             contradict H2. subst. auto.
          -- eapply loop_LPath_helper;eauto.
        * auto.
        * auto.
        * inversion H1;subst. eapply acyclic_path_NoDup; eauto.
      + decide (h = e); subst.
        { inversion H1. subst. repeat econstructor. }
        eapply find_none in HeqS;cycle 1.
        * instantiate (1:=h).
          enough (h ∈ (e :<: x)) as Hex.
          { destruct Hex;[symmetry in H2;contradiction|auto]. }
          eapply dom_dom_acyclic;eauto. eapply dom_loop;auto.
        * exfalso. decide (loop_contains h p); cbn in *; [congruence|contradiction].
  Qed.    
  
  Lemma loop_contains_innermost (h p : Lab)
        (Hloop : loop_contains h p)
    : exists h', innermost_loop h' p.
  Proof.
    unfold innermost_loop.
    eapply loop_LPath in Hloop as Hloop'. destructH.
    decide (loop_head p).
    + exists p. split;eauto using loop_contains_self. unfold deq_loop; firstorder.
    + inversion Hloop'. subst.
      * exists p. split;eauto using loop_contains_self. unfold deq_loop; firstorder.
      * subst. exists b.
        decide (innermost_loop_strict b p);cbn in *;[|congruence]. unfold innermost_loop_strict in i.
        clear - i n. destructH. unfold deq_loop.
        split;auto. intros. exploit i3. destruct i3;auto.
        subst. eapply loop_contains_loop_head in H. contradiction.
  Qed.

  Lemma loop_contains_innermost_strict (h p : Lab)
        (Hloop : loop_contains h p)
        (Hneq : h <> p)
    : exists h', innermost_loop_strict h' p.
  Proof.
    eapply loop_LPath in Hloop as Hloop'. destructH.
    inversion Hloop';subst;eauto;[contradiction|].
    exists b. decide (innermost_loop_strict b p);cbn in *;[auto|congruence].
  Qed.
  
  Lemma get_innermost_loop_spec
    : forall p : Lab,
      match get_innermost_loop p with
      | Some h => innermost_loop h p
      | None => forall h' : Lab, loop_contains h' p -> False
      end.
  Proof.
    unfold get_innermost_loop.
    intro. destruct (ex_innermost_loop p).
    - destruct s;eauto.
    - cbn in n. unfold innermost_loop in n. intros.
      eapply loop_contains_innermost in H. clear h'. destructH.
      specialize (n h'). eapply dec_DM_and in n;eauto.
      destruct n;unfold innermost_loop in H;firstorder.
  Qed.
  
  Lemma get_innermost_loop_dep_spec
    : forall p : Lab,
      match get_innermost_loop_dep p with
      | Some (exist _ h _) => innermost_loop h p
      | None => forall h' : Lab, loop_contains h' p -> False
      end.
  Proof.
    unfold get_innermost_loop_dep.
    intro. destruct (ex_innermost_loop p).
    - destruct s;eauto.
    - cbn in n. unfold innermost_loop in n. intros.
      eapply loop_contains_innermost in H. clear h'. destructH.
      specialize (n h'). eapply dec_DM_and in n;eauto.
      destruct n;unfold innermost_loop in H;firstorder.
  Qed.

  Lemma get_innermost_loop_strict_spec (* unused *)(p : Lab)
    : match get_innermost_loop_strict p with
      | Some h => innermost_loop_strict h p
      | None => forall h', loop_contains h' p -> h' = p
      end.
  Proof.
    unfold get_innermost_loop_strict.
    destruct (ex_innermost_loop_strict p); cbn.
    - destruct s. eauto.
    - intros. 
      decide (h' = p);[eauto|].
      eapply loop_contains_innermost_strict in H;eauto.
      destructH. specialize (n h'0); contradiction.
  Qed.
  
  Lemma get_innermost_loop_strict_dep_spec (* unused *)(p : Lab)
    : match get_innermost_loop_strict_dep p with
      | Some (exist _ h H) => innermost_loop_strict h p
      | None => forall h', loop_contains h' p -> h' = p
      end.
  Proof.
    unfold get_innermost_loop_strict_dep.
    destruct (ex_innermost_loop_strict p); cbn.
    - destruct s. eauto.
    - intros. 
      decide (h' = p);[eauto|].
      eapply loop_contains_innermost_strict in H;eauto.
      destructH. specialize (n h'0); contradiction.
  Qed.
  
  Lemma deq_loop_trans p q r
        (H1 : deq_loop p q)
        (H2 : deq_loop q r)
    : deq_loop p r.
  Proof.
    unfold deq_loop in *. intros. eapply H1,H2;eauto.
  Qed.

  Program Instance deq_loop_PreOrder : PreOrder deq_loop.
  Next Obligation.
    unfold Reflexive. eapply deq_loop_refl.
  Qed.
  Next Obligation.
    unfold Transitive; eapply deq_loop_trans.
  Qed.

  Lemma loop_contains_deq_loop h p
        (Hloop : loop_contains h p)
    : deq_loop p h.
  Proof.
    unfold deq_loop. intros. eapply loop_contains_trans;eauto.
  Qed.

  Lemma innermost_loop_deq_loop (* unused *)h p q
        (Hinner : innermost_loop h p)
        (Hloop : loop_contains h q)
    : deq_loop q p.
  Proof.
    unfold innermost_loop in Hinner. destructH.
    eapply deq_loop_trans;eauto.
    eapply loop_contains_deq_loop;eauto.
  Qed.

  (** preds **)

  Definition preds `{redCFG Lab edge} p : list Lab := filter (decPred_bool (fun q => edge q p)) (elem Lab). 

  Lemma preds_in_same_loop h p q
        (Hl : loop_contains h p)
        (Hneq : h <> p)
        (Hedge : q --> p)
    : loop_contains h q.
  Proof.
    unfold loop_contains in Hl.
    destructH.
    eapply path_rcons in Hl2 as Hl2';eauto.
    exists p0, (π :>: q). repeat (split;eauto).
    simpl_nl. rewrite rev_rcons. cbn. eapply nin_tl_iff in Hl3;auto.
    destruct Hl3 as [Hl3|Hl3];[contradict Hl3;eapply in_rev;auto|eapply path_back in Hl2;subst;auto].
  Qed.

  Lemma deq_loop_exited h qe e
        (Hexit : exit_edge h qe e)
    : deq_loop qe e.
  Proof.
    eapply no_exit_head in Hexit as Hneh.
    unfold exit_edge in *. destructH.
    unfold deq_loop. intros. 
    eapply preds_in_same_loop in H;eauto.
    intro N. eapply loop_contains_loop_head in H. subst. contradiction.
  Qed.
  
  Lemma deq_loop_exiting h qe e
        (Hexit : exit_edge h qe e)
    : deq_loop h qe.
  Proof.
    unfold deq_loop;intros. copy Hexit Hexit'.
    unfold exit_edge in Hexit. destructH. eapply loop_contains_either in Hexit0;eauto.
    destruct Hexit0;[auto|].
    enough (h = h0) by (subst;eauto using loop_contains_self,loop_contains_loop_head).
    eapply single_exit;eauto.
    unfold exit_edge. repeat (split;eauto).
    contradict Hexit2. eapply loop_contains_trans;eauto.
  Qed.

  Definition get_innermost_loop' p
    := match get_innermost_loop p with
       | Some h => h
       | None => root
       end.

  Lemma deq_loop_innermost' (p : Lab)
    : deq_loop (get_innermost_loop' p) p.
  Proof.
    remember (get_innermost_loop' p) as h.
    specialize (get_innermost_loop_spec p) as Hspec.
    unfold get_innermost_loop' in Heqh.
    destruct (get_innermost_loop p).
    - subst. unfold innermost_loop in Hspec. subst. destructH; auto.
    - subst. unfold deq_loop. intros. exfalso; eauto.
  Qed.
  Definition innermost_loop' (* unused *)`{redCFG} (h p : Lab) := (loop_contains h p \/ h = root) /\ deq_loop h p.

  Definition get_innermost_loop_strict' p
    := match get_innermost_loop_strict p with
       | Some h => h
       | None => root
       end.

  Lemma eq_loop_innermost h p q
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

End cfg.