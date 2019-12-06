Require Export CFGloop.

Section cfg.
  Context `{C : redCFG}.
  
  Notation "p '-a>b' q" := (a_edge p q) (at level 55).
  Notation "p '-a>' q" := (p -a>b q = true) (at level 55).
  Notation "p '-->b' q" := (edge p q) (at level 55).
  Notation "p '-->' q" := (p -->b q = true) (at level 55, right associativity).

  (** * loop ordering by relative depth **)

  Definition deq_loop q p : Prop :=
    forall h, loop_contains h p -> loop_contains h q.

  Global Instance deq_loop_dec h p : dec (deq_loop h p).
  eauto.
  Qed.

  (** * Preorder properties of deq_loop **)

  (** Reflexivity **)
  
  Lemma deq_loop_refl l :
    deq_loop l l.
  Proof.
    unfold deq_loop;firstorder.
  Qed.
  
  Global Instance deq_loop_Reflexive : Reflexive deq_loop.
  Proof.
    unfold Reflexive. intros. eapply deq_loop_refl.
  Qed.

  (** * Transitivity **)
  
  Lemma deq_loop_trans p q r
        (H1 : deq_loop p q)
        (H2 : deq_loop q r)
    : deq_loop p r.
  Proof.
    unfold deq_loop in *. intros. eapply H1,H2;eauto.
  Qed.

  Global Instance deq_loop_Transitive : Transitive deq_loop.
  Proof.
    unfold Transitive; eapply deq_loop_trans.
  Qed.
  
  Program Instance deq_loop_PreOrder : PreOrder deq_loop.

  (** * deq_loop facts **)
  
  Lemma loop_contains_deq_loop h p
        (Hloop : loop_contains h p)
    : deq_loop p h.
  Proof.
    unfold deq_loop. intros. eapply loop_contains_trans;eauto.
  Qed.
  
  Lemma deq_loop_root p
    : deq_loop p root.
  Proof.
    unfold deq_loop.
    intros.
    exfalso.
    eapply root_loop_root in H as H'. subst.
    unfold loop_contains in H. destructH.
    eapply back_edge_incl in H0. eapply root_no_pred;eauto.
  Qed.
  
  Lemma exit_not_deq h p q
        (Hexit : exit_edge h p q)
        (Hdeq : deq_loop q h)
    : False.
  Proof.
    unfold exit_edge in Hexit. destructH.
    apply Hexit2.
    eapply Hdeq.
    eapply loop_contains_self. eapply loop_contains_loop_head;eauto.
  Qed.
  
  Lemma deq_loop_head_loop_contains p h
        (Hdeq : deq_loop p h)
        (Hhead : loop_head h)
    : loop_contains h p.
  Proof.
    eapply Hdeq.
    eapply loop_contains_self.
    eauto.
  Qed.
  
  Lemma deq_loop_depth p q
        (Hdeq : deq_loop p q)
    : depth q <= depth p.
  Proof.
    unfold depth.
    eapply NoDup_incl_length.
    - eapply NoDup_iff_dupfree.
      eapply dupfree_filter.
      eapply dupfree_elements. 
    - intros x Hx.
      eapply in_filter_iff in Hx. cbn in Hx.
      eapply in_filter_iff. cbn. destruct Hx. split;auto.
  Qed.
  
  Lemma deq_loop_depth_leq p q
        (Hdeq : deq_loop p q)
        (Hdep : depth p <= depth q)
    : deq_loop q p.
  Proof.
    unfold depth in Hdep.
    eapply NoDup_length_incl in Hdep.
    - unfold incl in Hdep. setoid_rewrite in_filter_iff in Hdep. cbn in Hdep.
      intros a Ha. eapply Hdep;eauto.
    - eapply NoDup_iff_dupfree. eapply dupfree_filter. eapply dupfree_elements.
    - unfold incl. setoid_rewrite in_filter_iff. intros.
      cbn in *. destructH. eapply Hdeq in H1. eauto.
  Qed.
    
  Lemma deq_loop_depth_eq p q
        (Hdeq : deq_loop p q)
        (Hdep : depth q = depth p)
    : deq_loop q p.
  Proof.
    eapply deq_loop_depth_leq;eauto.
    omega.
  Qed.

  (** * Equivalence relation eq_loop **)

  Definition eq_loop q p : Prop :=
    deq_loop q p /\ deq_loop p q.

  Lemma eq_loop1  p p' q
    : eq_loop p p' -> deq_loop p q -> deq_loop p' q.
  Proof.
    intros. destruct H.
    eapply deq_loop_trans;eauto.
  Qed.

  Lemma eq_loop2 p q q'
    : eq_loop q q' -> deq_loop p q -> deq_loop p q'.
  Proof.
    intros. destruct H.
    eapply deq_loop_trans;eauto.
  Qed.

  
  Global Instance eq_loop_Eq : Equivalence eq_loop.
  Proof.
    econstructor.
  - econstructor;apply deq_loop_refl.
  - econstructor; destruct H;eauto.
  - econstructor; destruct H,H0; eapply deq_loop_trans;eauto.
  Qed.

  Global Instance eq_loop_proper_deq_loop1 (p : Lab)
    : Proper (eq_loop ==> Basics.impl) ((Basics.flip deq_loop) p).
  Proof.
    unfold Proper. unfold respectful. unfold Basics.impl.
    intros. eapply eq_loop1; eauto.
  Qed.
  
  Global Instance eq_loop_proper_deq_loop2 (p : Lab) : Proper (eq_loop ==> Basics.impl) (deq_loop p).
  Proof.
    unfold Proper. unfold respectful. unfold Basics.impl.
    intros. eapply eq_loop2; eauto.
  Qed.

  Global Instance eq_loop_proper_contains (h : Lab)
    : Proper (eq_loop ==> iff) (loop_contains h).
  Proof.
    unfold Proper, respectful, Basics.impl.
    intros. split;eapply H. 
  Qed.

  Global Instance eq_loop_depth
    : Proper (eq_loop ==> eq) depth.
  Proof.
    clear.
    unfold Proper,respectful. intros.
    destruct H.
    eapply deq_loop_depth in H.
    eapply deq_loop_depth in H0.
    omega.
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
  
  (** * Definitions for innermost loops **)
  
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

  (** * simple facts about innermost loops **)
  
  
  Lemma innermost_eq_loop h q
        (Hinnermost : innermost_loop h q)
    : eq_loop h q.
  Proof.
    destruct Hinnermost. split;auto.
    eapply loop_contains_deq_loop;auto.
  Qed.

  Lemma innermost_loop_deq_loop h p q
        (Hinner : innermost_loop h p)
        (Hloop : loop_contains h q)
    : deq_loop q p.
  Proof.
    unfold innermost_loop in Hinner. destructH.
    eapply deq_loop_trans;eauto.
    eapply loop_contains_deq_loop;eauto.
  Qed.

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

  (** * Uniqueness of innermost loops *)

  Lemma innermost_loop_strict_unique (h h' p : Lab)
        (H : innermost_loop_strict h p)
        (Q : innermost_loop_strict h' p)
    : h = h'.
  Proof.
    unfold innermost_loop_strict in *. do 2 destructH.
    eapply H3 in Q0. destruct Q0;[|contradiction].
    eapply Q3 in H0. destruct H0;[|contradiction].
    eapply loop_contains_Antisymmetric;auto.
  Qed.

  (** * LPath **)
  
  Definition LPath := Path (fun h p => decision (innermost_loop_strict h p)).
  
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
  
  Lemma loop_LPath_helper p h π
        (Hpath : Path a_edge root p (p :: π))
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
                                 (fun π : list Lab => forall p, loop_contains h p
                                                           -> Path a_edge root p π
                                                           -> exists (π0 : list Lab), LPath h p π0))
      as WFind.
    eapply WFind.
    intros;clear WFind.
    destruct x.
    - inversion H1; subst p a e.
    - remember (find (fun h' => decision (loop_contains h' p)) x) as S.
      destruct S; symmetry in HeqS.
      + eapply find_some_strong in HeqS. destructH. decide (loop_contains e0 p);cbn in *;[|congruence].
        2: auto.
        2: { eapply acyclic_path_NoDup in H1. inversion H1;auto. }
        inversion H1; [subst x ;contradiction|]. subst π a c e.
        decide (h = p).
        { subst;eexists;econstructor. }
        specialize (@path_to_elem _ a_edge _ _ e0 x H6 HeqS0) as [ϕ [Hϕ0 Hϕ1]].
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
        exists (p :: π0).
        econstructor;cycle 1.
        * instantiate (1:=e0). decide (innermost_loop_strict e0 p);cbn;[auto|exfalso;contradict n0].
          unfold innermost_loop_strict. split;auto. split.
          -- eapply acyclic_path_NoDup in H1. clear - HeqS0 H1. inversion H1; subst.
             contradict H2. subst. auto.
          -- eapply loop_LPath_helper;eauto.
        * auto.
      + decide (h = e); subst.
        { inversion H1.
          - subst x e p a. repeat econstructor.
          - subst π e c a. repeat econstructor. }
        eapply find_none in HeqS;cycle 1.
        * instantiate (1:=h).
          enough (h ∈ (e :: x)) as Hex.
          { destruct Hex;[symmetry in H2;contradiction|auto]. }
          eapply dom_dom_acyclic;eauto. eapply dom_loop;auto.
        * exfalso. decide (loop_contains h p); cbn in *; [congruence|contradiction].
  Qed.

  (** * Existence of innermost loops **)
  
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

  Lemma get_innermost_loop_strict_spec (p : Lab)
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
  
  Lemma get_innermost_loop_strict_dep_spec (p : Lab)
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

  (** * Lemmas about relative loop depth on exit edges **)
  
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
  
  Lemma deq_loop_exited' : forall (h qe e : Lab), exit_edge h qe e -> deq_loop h e.
  Proof.
    intros.
    eapply deq_loop_exited in H as H'.
    eapply deq_loop_exiting in H as H''.
    eapply deq_loop_trans;eauto.
  Qed.
  
  Lemma eq_loop_exiting h p q
        (Hexit : exit_edge h p q)
    : eq_loop h p.
  Proof.
    split.
    - eapply deq_loop_exiting;eauto.
    - unfold exit_edge in Hexit.
      destruct Hexit as [Hexit _].
      eapply loop_contains_deq_loop;eauto.
  Qed.      
  
  (** * Variant of get_innermost_loop that uses the root if there is no loop **)

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
  Definition innermost_loop' `{redCFG} (h p : Lab) := (loop_contains h p \/ h = root) /\ deq_loop h p.

  Definition get_innermost_loop_strict' p
    := match get_innermost_loop_strict p with
       | Some h => h
       | None => root
       end.

  (** * innermost loop facts **)
  
  Lemma exit_edge_innermost h q e
        (Hexit : exit_edge h q e)
    : innermost_loop h q.
  Proof.
    clear - Hexit.
  Admitted. (* FIXME *)
  
  Lemma dom_self_loop h p π
        (Hpath : CPath p p π)
        (Hinl : innermost_loop h p)
        (Hnin : h ∉ π)
    : π = [p].
  Proof.
    clear - Hpath Hinl Hnin.
  Admitted. (* FIXME *)

End cfg.
