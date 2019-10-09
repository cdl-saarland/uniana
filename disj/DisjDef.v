Require Export Tagged LastCommon Disjoint.


Parameter path_splits : forall `{redCFG}, Lab -> list (Lab * Lab * Lab).

Parameter loop_splits : forall `{redCFG}, Lab -> Lab -> list (Lab * Lab * Lab).

(* remove branch from splits, we can use the assumed global branch function to get varsets back*)
Definition pl_split `{redCFG} (qh qe q1 q2 br : Lab) :=
  (exists π ϕ, CPath br qh (π :>: br)
          /\ CPath br qe (ϕ :>: br)
          /\ q1 = ne_back π
          /\ q2 = ne_back ϕ
          /\ q1 <> q2 (* if π = single or φ = single, then this is not implied by the next condition *)
          /\ Disjoint (tl π) (tl ϕ)).

Parameter path_splits_spec (* unused *): forall `{redCFG} p q1 q2 br,
    pl_split p p q1 q2 br <->
    (br, q1, q2) ∈ path_splits p.

Parameter loop_splits_spec (* unused *): forall `{redCFG} qh qe q1 q2 br,
    loop_contains qh br /\ (* otherwise some splits would be considered as loop splits *)
    exited qh qe /\
    pl_split qh qe q1 q2 br <->
    (br, q1, q2) ∈ loop_splits qh qe.

Parameter splits' : forall `{redCFG}, Lab -> Lab -> list (Lab * Lab * Lab).
Parameter splits  : forall `{redCFG}, Lab -> list (Lab * Lab * Lab).
Parameter rel_splits : forall `{redCFG}, Lab -> Lab -> list (Lab * Lab * Lab).

(** * Some useful lemmas **)

Lemma path_nlrcons_edge (* unused *){A : Type} (a b c : A) l f
      (Hpath : Path f b c (l :>: a))
  : f a (ne_back l) = true.
Proof.
  revert dependent c.
  induction l; intros; inversion Hpath; subst; cbn in *.
  - inversion H3. subst b0 b a1. auto.
  - eauto.
Qed.

Lemma lc_nil1 {A : Type} `{EqDec A eq} l1 l2 l2' (x : A)
      (Hlc : last_common' l1 l2 [] l2' x)
  : Some x = hd_error l1.
Proof.
  unfold last_common' in Hlc. destructH.
  cbn in *.
  destruct l1;[inversion Hlc0;congruence'|].
  cbn.
  f_equal.
  eapply postfix_hd_eq;eauto.
Qed.

Lemma lc_cons1 {A : Type} `{EqDec A eq} l1 l2 l1' l2' (x y : A)
      (Hlc : last_common' l1 l2 (x :: l1') l2' y)
  : Some x = hd_error l1.
Proof.
  unfold last_common' in Hlc. destructH.
  destruct l1;[inversion Hlc0;congruence'|].
  cbn.
  rewrite cons_rcons_assoc in Hlc0.
  f_equal.
  eapply postfix_hd_eq;eauto.
Qed.

Lemma hd_error_ne_front {A : Type} (l : ne_list A)
  : hd_error l = Some (ne_front l).
Proof.
  induction l;cbn;auto.
Qed.


Lemma lc_succ_rt1 {A : Type} `{EqDec A eq} l1 l2 l1' l2' (x y : A)
      (Hlc : last_common' l1 l2 l1' l2' x)
      (Hin : y ∈ l1')
  : y ≻* x | l1.
Proof.
  unfold last_common' in Hlc. destructH.
  eapply splinter_postfix;eauto.
  eapply splinter_rev. cbn. rewrite rev_rcons. econstructor. econstructor.
  eapply splinter_single. rewrite <-In_rev. auto.
Qed.
  
Lemma lc_succ_rt2 (A : Type) `{EqDec A eq} (l1 l2 l1' l2' : list A) (a b c : A)
      (Hlc : last_common' l1 l2 l1' l2' a)
      (Hnd : NoDup l2)
      (Hsucc : b ≻* c | l2)
      (Hel : c ∈ l2')
  : b ∈ l2'.
Proof.
  unfold last_common' in Hlc. destructH.
  eapply splinter_in in Hsucc as Hel'.
  eapply postfix_eq in Hlc2. destructH.
  rewrite <-app_cons_assoc in Hlc2.
  setoid_rewrite Hlc2 in Hsucc.
  eapply succ_NoDup_app in Hsucc;eauto. 
  setoid_rewrite <-Hlc2;eauto.
Qed.

Lemma lc_succ_rt_eq_lc {A : Type} `{EqDec A eq} l1 l2 l1' l2' (x y : A)
      (Hlc : last_common' l1 l2 l1' l2' x)
      (Hsucc1 : y ≻* x | l1)
      (Hsucc2 : y ≻* x | l2)
      (Hnd1 : NoDup l1)
      (Hnd2 : NoDup l2)
  : x = y.
Proof.
  unfold last_common' in Hlc. destructH.
  dependent induction Hsucc1.
  - clear IHHsucc1.
    destruct l1';cbn in Hlc0; eapply postfix_hd_eq in Hlc0; eauto.
    subst a.
    dependent induction Hsucc2.
    + destruct l2';cbn in Hlc2; eapply postfix_hd_eq in Hlc2; eauto. subst.
      exfalso. eapply Hlc1;left; reflexivity.
    + destruct l2';cbn in Hlc2; eapply postfix_hd_eq in Hlc2 as Heq; eauto.
      * subst a.
        eapply splinter_cons in Hsucc2. exfalso. eapply splinter_in in Hsucc2. inversion Hnd2. auto.
      * eapply IHHsucc2 with (l2':=l2') ; eauto.
        -- eapply cons_postfix;eauto.
        -- clear - Hlc1. eapply disjoint_cons2 in Hlc1. firstorder.
        -- inversion Hnd2. auto.
  - destruct l1';cbn in Hlc0; eapply postfix_hd_eq in Hlc0 as Heq; eauto.
    + subst a.
      eapply splinter_cons in Hsucc1. eapply splinter_in in Hsucc1. inversion Hnd1. subst. contradiction.
    + eapply IHHsucc1 with (l1':=l1');eauto.
      * eapply cons_postfix;eauto.
      * eapply disjoint_cons1 in Hlc1. firstorder.
      * inversion Hnd1. auto.
Qed.
