Require Import Ensembles.
Require Import Coq.Program.Equality.

Require Export Graph Disjoint DecTac.

Section Algo.

  Variable L : finType.

  Variable S : list L.

  Definition in_S x := In x S.

  Variable edge : L -> L -> Prop.

  Variable dec : EqDec L eq.

  Variable ac : acyclic edge.

  Definition DPath := Path edge.

  Definition sdom q p := forall 𝜋 s, in_S s -> DPath s p 𝜋 -> q ∈ 𝜋.

  Definition reachable a b := exists 𝜋, DPath a b 𝜋.

  Definition reachable_from_S p := exists s 𝜋, in_S s /\ DPath s p 𝜋.

  Definition first_sdom d p := sdom d p /\ forall q, sdom q p -> reachable d q.

  Axiom menger_for_two :
    forall p q,
      (~ exists d, sdom d p /\ sdom d q) ->
      exists s1 s2 𝜋 𝜙, 
        in_S s1 /\
        in_S s2 /\
        DPath s1 p 𝜋 /\
        DPath s2 q 𝜙 /\
        Disjoint 𝜋 𝜙.

  Lemma prefix_in 𝜋 𝜙 a b c x
    (Hprefix : Prefix 𝜙 𝜋)
    (H𝜋 : DPath a c 𝜋)
    (H𝜙 : DPath a b 𝜙)
    (Hin : x ∈ 𝜙) :
    x ∈ 𝜋.
  Proof.
    induction H𝜋.
    - inversion Hprefix; subst; eauto.
      inversion H1; subst. contradiction Hin.
    - inversion Hprefix; subst.
      + assumption.
      + simpl. eauto.
  Qed.

  Inductive Concat {A : Type} : list A -> list A -> list A -> Prop :=
  | ConcatEmpty l a : Concat (a :: l) [a] (a :: l)
  | ConcatNode l r s a : Concat l r s -> Concat l (a :: r) (a :: s).

  Lemma path_trans a b c 𝜋 𝜙
        (H𝜋 : DPath a b 𝜋)
        (H𝜙 : DPath b c 𝜙) :
    exists 𝜌, DPath a c 𝜌 /\ Concat 𝜋 𝜙 𝜌.
  Proof.
    induction H𝜙.
    - eexists. split.
      + eassumption.
      + inversion_clear H𝜋; econstructor.
    - destruct IHH𝜙 as [𝜌 [H𝜌 Hconcat]]; [ eauto |].
      eexists. split; econstructor; eassumption.
  Qed.

  Lemma concat_in 𝜋 𝜙 𝜌 (a : L)
        (Hconcat : Concat 𝜋 𝜙 𝜌)
        (Ha : a ∈ 𝜌) :
    a ∈ 𝜋 \/ a ∈ 𝜙.
  Proof.
    induction Hconcat.
    - firstorder.
    - destruct Ha.
      + firstorder.
      + destruct IHHconcat; firstorder.
  Qed.

  Lemma not_in_concat 𝜋 𝜙 𝜌 (a : L)
        (Hconcat : Concat 𝜋 𝜙 𝜌)
        (Hnotin𝜋 : a ∉ 𝜋)
        (Hnotin𝜙 : a ∉ 𝜙)
    : a ∉ 𝜌.
  Proof.
    induction Hconcat; firstorder.
  Qed.

  Lemma concat_not_in_pair 𝜋 𝜙 𝜌 (a : L)
        (Hconcat : Concat 𝜋 𝜙 𝜌)
        (Hnotin : a ∉ 𝜌)
    : a ∉ 𝜋 /\ a ∉ 𝜙.
  Proof.
    induction Hconcat; try split; firstorder.
  Qed.

  Lemma path_split_concat a b x 𝜋
        (H𝜋 : DPath a b 𝜋)
        (Hin : x ∈ 𝜋) :
    exists 𝛼 𝛽, DPath a x 𝛼 /\ DPath x b 𝛽 /\ Concat 𝛼 𝛽 𝜋.
  Proof.
    induction H𝜋.
    - inversion_clear Hin; subst.
      + exists [x]. exists [x].
        repeat split; try econstructor.
      + inversion H.
    - inversion Hin.
      + subst.
        exists (x :: π). exists [x].
        repeat split; try econstructor; try eassumption.
      + destruct IHH𝜋 as [𝛼 [𝛽 [H𝛼 [H𝛽 Hconcat]]]]; try assumption.
        exists 𝛼. eexists.
        split; try assumption.
        split.
        * econstructor; try eassumption.
        * econstructor. assumption.
  Qed.

  Lemma acyclic_not_in_postfix 𝜋 a b c
        (H𝜋 : DPath a c 𝜋)
        (Hin : b ∈ 𝜋)
        (Hneq : b <> a) : 
    exists 𝜙, DPath b c 𝜙 /\ a ∉ 𝜙.
  Proof.
    specialize (path_to_elem H𝜋 Hin); intro.
    destruct H as [𝜙 [H𝜙 Hpost]].
    specialize (path_from_elem _ H𝜋 Hin); intro.
    destruct H as [𝜌 [H𝜌 Hpre]].
    exists 𝜌. split; [eauto |].
    intro Hin2.
    specialize (path_to_elem H𝜌 Hin2); intro.
    destruct H as [𝜙' [H𝜙' _]].
    eapply path_path_acyclic; try eassumption.
  Qed.

  Lemma sdom_trans a b c :
    sdom a b ->
    sdom b c ->
    sdom a c.
  Proof.
    intros Ha Hb.
    unfold sdom.
    intros 𝜋 s Hin Hpath.
    unfold sdom in Ha, Hb.
    specialize (Hb 𝜋 s Hin Hpath).
    eapply path_to_elem in Hb.
    - destruct Hb as [𝜙 [H𝜙 Hprefix]].
      specialize (Ha 𝜙 s Hin H𝜙).
      eapply prefix_in; eauto.
    - eauto.
  Qed.

  Lemma suffix_disjoint s1 dp q dq 𝜋 𝜙
        (path_𝜋 : DPath s1 dp 𝜋)
        (path_𝜙 : DPath dq q 𝜙)
        (Hins : in_S s1)
        (Hsdom_q : first_sdom dq q)
        (Hdqnotin_𝜋 : dq ∉ 𝜋)
        (Hdneq : dq <> dp) :
    Disjoint 𝜋 𝜙.
  Proof.
    intro a. intro Hain_𝜋. intro Hain_𝜙.
    destruct (decide_eq a dq) as [Had_eq | Had_neq].
    - subst a. contradiction Hain_𝜋.
    - destruct (acyclic_not_in_postfix path_𝜙 Hain_𝜙 Had_neq) as [𝜙' [path_𝜙' Hdqnotin_𝜙']].
      destruct (path_split_concat path_𝜋 Hain_𝜋) as [𝜋1 [𝜋2 [path_𝜋1 [path_𝜋2 Hconc]]]].
      destruct (concat_not_in_pair Hconc Hdqnotin_𝜋) as [Hdqnotin_𝜋1 Hdqnotin_𝜋2].
      destruct (path_trans path_𝜋1 path_𝜙') as [contra [path_contra Hconcat_contra]].
      eapply (not_in_concat Hconcat_contra); try eassumption.
      eapply Hsdom_q; try eassumption.
  Qed.

  Lemma disjoint_symm {A : Type} 𝜋 𝜙
        (Hdisj : Disjoint 𝜋 𝜙) :
    @Disjoint A 𝜙 𝜋.
  Proof.
    firstorder.
  Qed.

  Lemma two_parts_disjoint 𝜋 𝜙 𝜌1 𝜎1 𝜌2 𝜎2
        (Hconcat1 : Concat 𝜌1 𝜎1 𝜋)
        (Hconcat2 : Concat 𝜌2 𝜎2 𝜙)
        (Hdisj1 : Disjoint 𝜌1 𝜌2)
        (Hdisj2 : Disjoint 𝜌1 𝜎2)
        (Hdisj3 : Disjoint 𝜎1 𝜌2)
        (Hdisj4 : Disjoint 𝜎1 𝜎2) :
    @Disjoint L 𝜋 𝜙.
  Proof.
    induction Hconcat1; 
    intro x; intros Hin1; intro Hin2;
      assert (Hnin : x ∉ 𝜙) by (eapply (not_in_concat Hconcat2); firstorder);
      contradiction.
  Qed.
  
  Section disjoint_first.
    Variable p q dp dq : L.
    Hypothesis p_from_S : reachable_from_S p.
    Hypothesis q_from_S : reachable_from_S q.
    Hypothesis dp_first : first_sdom dp p.
    Hypothesis dq_first : first_sdom dq q.
    Hypothesis dpq_neq : dp <> dq.

    Lemma no_single_dom :
      (exists d, sdom d dp /\ sdom d dq) -> False.
    Proof.
      intros.
      unfold first_sdom in *.
      inversion_clear dp_first as [Hsdom_p Hfirst_p].
      inversion_clear dq_first as [Hsdom_q Hfirst_q].
      inversion_clear p_from_S as [s1 [𝜋 [in1 path1]]].
      inversion_clear q_from_S as [s2 [𝜙 [in2 path2]]].
      inversion_clear H as [d [Hsdom_d_dp Hsdom_d_dq]].

      destruct (decide_eq d dp).
      - subst dp.
        assert (Hsdom_d_q : sdom d q) by (eauto using sdom_trans).
        eapply Hfirst_q in Hsdom_d_q.
        unfold reachable in Hsdom_d_q.
        destruct Hsdom_d_q as [𝜌 path_𝜌].
        specialize (Hsdom_q 𝜙 s2 in2 path2).
        destruct (path_to_elem path2 Hsdom_q) as [𝜎 [path_𝜎 prefix_𝜎]].
        unfold sdom in Hsdom_d_dq.
        specialize (Hsdom_d_dq 𝜎 s2 in2 path_𝜎).
        destruct (path_from_elem _ path_𝜎 Hsdom_d_dq) as [x [H _]]. 
        eapply path_path_acyclic; eauto. 

      - assert (Hsdom_d_p : sdom d p) by (eauto using sdom_trans).
        eapply Hfirst_p in Hsdom_d_p.
        unfold reachable in Hsdom_d_p.
        destruct Hsdom_d_p as [𝜌 path_𝜌].
        specialize (Hsdom_p 𝜋 s1 in1 path1).
        destruct (path_to_elem path1 Hsdom_p) as [𝜎 [path_𝜎 prefix_𝜎]].
        unfold sdom in Hsdom_d_dp.
        specialize (Hsdom_d_dp 𝜎 s1 in1 path_𝜎).
        destruct (path_from_elem _ path_𝜎 Hsdom_d_dp) as [x [H _]]. 
        eapply path_path_acyclic; eauto. 
    Qed.

    Lemma first_disjoint :
      exists s1 s2 𝜋 𝜙, in_S s1 /\ in_S s2 /\ DPath s1 dp 𝜋 /\ DPath s2 dq 𝜙 /\ Disjoint 𝜋 𝜙.
    Proof.
      eauto using menger_for_two, no_single_dom.
    Qed.

    Lemma disjoint_from_first_sdom 𝜌 𝜎
          (path𝜌 : DPath dp p 𝜌)
          (path𝜎 : DPath dq q 𝜎) :
        Disjoint 𝜌 𝜎.
    Proof.
      specialize first_disjoint; intros.
      destruct H as [s1 [s2 [𝜋 [𝜙 [in1 [in2 [path1 [path2 Hdisj]]]]]]]].
      clear p_from_S q_from_S.
      assert (Hdp_notin_𝜙 : dp ∉ 𝜙). {
        intro. eapply Hdisj; try eassumption. inversion path1; eauto.
      }
      assert (Hdq_notin_𝜋 : dq ∉ 𝜋). {
        intro. eapply Hdisj; try eassumption. inversion path2; eauto.
      }
      destruct (In_dec _ dq 𝜌).
      - exfalso.
        destruct (acyclic_not_in_postfix path𝜌 H) as [𝛼 [path𝛼 Hnotin_dp]]; [ firstorder|].
        destruct (path_trans path2 path𝛼) as [contra [path_contra Hconcat]].
        eapply not_in_concat; try eassumption.
        inversion_clear dp_first as [Hsdom_p _].
        eapply Hsdom_p; try eassumption.
      - unfold Disjoint.
        intros d Hdin𝜌.
        intro Hdin𝜎.
        assert (Hddq : d <> dq). {
          intro. subst. contradiction H.
        }
        destruct (acyclic_not_in_postfix path𝜎 Hdin𝜎) as [𝛽 [path𝛽 Hnotin𝛽]]. {
          intro. subst. eauto.
        }
        destruct (path_split_concat path𝜌 Hdin𝜌) as [𝛼 [𝛼' [path𝛼 [path𝛼' Hconcat]]]].
        destruct (concat_not_in_pair Hconcat H) as [Hnotin𝛼 _].
        destruct (path_trans path1 path𝛼) as [𝛾 [path𝛾 Hconcat𝛾]].
        destruct (path_trans path𝛾 path𝛽) as [contra [path_contra Hconcat_contra]].
        eapply (not_in_concat Hconcat_contra).
        + eapply (not_in_concat Hconcat𝛾); try eassumption.
        + eassumption.
        + inversion_clear dq_first as [Hsdom_q _].
          eapply Hsdom_q. apply in1. assumption.
    Qed.

    Lemma ex_disjoint :
      exists s1 s2 𝜋 𝜙, in_S s1 /\ in_S s2 /\ DPath s1 p 𝜋 /\ DPath s2 q 𝜙 /\ Disjoint 𝜋 𝜙.
    Proof.
      destruct p_from_S.
      destruct first_disjoint as [s1 [s2 [𝜋 [𝜙 [in1 [in2 [path1 [path2 Hdisj]]]]]]]].
      inversion dp_first as [Hsdom_p Hfirst_p].
      destruct p_from_S as [s1' [𝜋' [Hins1' path_𝜋']]].
      assert (Hdpin : dp ∈ 𝜋') by eauto.

      inversion dq_first as [Hsdom_q Hfirst_q].
      destruct q_from_S as [s2' [𝜙' [Hins2' path_𝜙']]].
      assert (Hdqin : dq ∈ 𝜙') by eauto.

      destruct (path_split_concat path_𝜋' Hdpin) as [_ [𝜋2 [_ [path_𝜋2 _]]]].
      destruct (path_split_concat path_𝜙' Hdqin) as [_ [𝜙2 [_ [path_𝜙2 _]]]].
      clear s1' 𝜋' Hins1' path_𝜋' Hdpin.
      clear s2' 𝜙' Hins2' path_𝜙' Hdqin.

      destruct (path_trans path1 path_𝜋2) as [𝜋c [path_𝜋c Hconc_𝜋c]].
      destruct (path_trans path2 path_𝜙2) as [𝜙c [path_𝜙c Hconc_𝜙c]].
      exists s1. exists s2. exists 𝜋c. exists 𝜙c. repeat split; try eassumption.
      assert (dqp_neq : dq <> dp). {
        intro. apply dpq_neq. subst. reflexivity.
      }
        
      eapply (two_parts_disjoint Hconc_𝜋c Hconc_𝜙c).
      - assumption.
      - eapply suffix_disjoint; try eassumption.
        eapply disjoint_symm in Hdisj.
        eapply Hdisj.
        eauto using path_contains_front.
      - eapply disjoint_symm. eapply suffix_disjoint; try eassumption.
        eapply Hdisj.
        eauto using path_contains_front.
      - eauto using disjoint_from_first_sdom.
    Qed.

  End disjoint_first.
  
  Lemma pred_sdom_diff a b p da db
        (Hreach_a : reachable_from_S a)
        (Hreach_b : reachable_from_S b)
        (Hedge_a : edge a p)
        (Hedge_b : edge b p) 
        (Ha : first_sdom da a)
        (Hb : first_sdom db b)
        (Hneq : da <> db) :
    first_sdom p p.
  Proof.
    unfold first_sdom.
    split. {
      unfold sdom. intros. eauto using path_contains_front.
    }
    intros.
    decide (p = q) as [ Heq | Hneqpq ]. {
      subst q. unfold reachable. exists [p]. econstructor.
    }
    destruct (ex_disjoint Hreach_a Hreach_b Ha Hb Hneq) as
        [s0 [s1 [𝜋 [𝜙 [HinS0 [HinS1 [path_𝜋 [path_𝜙 Hdisj]]]]]]]].
    assert (path_𝜋' : DPath s0 p (p :: 𝜋)). {
      econstructor; try eassumption.
    }
    assert (path_𝜙' : DPath s1 p (p :: 𝜙)). {
      econstructor; try eassumption.
    }
    exfalso. unfold Disjoint in Hdisj.
    unfold sdom in H.
    assert (Hqin_𝜋 : q ∈ 𝜋). {
      apply H in path_𝜋'; try eassumption.
      inversion path_𝜋'; firstorder.
    }
    assert (Hqin_𝜙 : q ∈ 𝜙). {
      apply H in path_𝜙'; try eassumption.
      inversion path_𝜙'; firstorder.
    }
    eapply Hdisj; try eassumption.
  Qed.

  Lemma pred_sdom_same p dp 
        (Hpred : forall q, edge q p -> first_sdom dp q)
        (Hreach : reachable_from_S p)
        (HnotinS : ~ in_S p) :
    first_sdom dp p.
  Proof.  
    unfold first_sdom in *.
    assert (Hsdom : sdom dp p). {
      unfold sdom. intros.
      inversion H0; subst.
      contradiction H.
      apply Hpred in H2.
      destruct H2 as [Hsdom Hfirst].
      eauto.
    }
    split; [ assumption |].
    intros. 
    unfold reachable_from_S in Hreach.
    destruct Hreach as [s [𝜋 [HinS path_𝜋]]].
    decide (q = p) as [ | Hne ]; [ subst q |]. {
      unfold sdom in Hsdom.
      specialize (Hsdom 𝜋 s HinS path_𝜋).
      unfold reachable.
      destruct (path_from_elem _ path_𝜋 Hsdom). firstorder.
    }
    inversion path_𝜋; subst.
    - contradiction HinS.
    - rename path_𝜋 into path_π.
      assert (Hsdom_b : sdom q b). {
        unfold sdom. intros 𝜋 s0 Hins0 path_𝜋.
        assert (path_𝜋' := PathCons path_𝜋 H1).
        unfold sdom in H.
        specialize (H (p :: 𝜋) s0 Hins0 path_𝜋').
        inversion H; firstorder.
      }
      firstorder.
  Qed.
      
  Lemma sdom_init s
        (HinS : in_S s) :
    first_sdom s s.
  Proof.
    unfold first_sdom, sdom.
    split.
    - eauto using path_contains_front.
    - intros. unfold reachable. 
      specialize (H [s] s HinS (PathSingle _ s)).
      inversion H.
      + subst q. exists [s]. constructor.
      + contradiction H0.
  Qed.

End Section Algo.

