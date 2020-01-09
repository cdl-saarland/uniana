Require Export CFGdef CFGTac.

Lemma all_sat_restrict_edge'
      (L : Type)
      (f : L -> L -> Prop)
      (p q : L)
      (π : list L)
      (Hπ : Path f p q π)
      (P : decPred L)
      (Hsat :  forall x : L, x ∈ π -> P x)
  : Path (restrict_edge' f P) p q π.
Proof.
  induction Hπ.
  - econstructor.
  - econstructor.
    + eapply IHHπ. intros; eapply Hsat. cbn. firstorder.
    + unfold_edge_op; split_conj; eauto; eapply Hsat; cbn; auto.
      right. eapply path_contains_front;eauto.
Qed.

Lemma loop_contains'_basic `{redCFG} h p
  : loop_contains' edge__P a_edge__P h p = loop_contains h p.
Proof.
  reflexivity.
Qed.  

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Lemma is_true2_decision (A B : Type) (f : A -> B -> Prop) 
      (Hdec : forall (a : A) (b : B), dec (f a b)) 
  : is_true2 (fun a b => decision (f a b)) = f.
Proof.
  do 2 (apply functional_extensionality; intro).
  eapply propositional_extensionality.
  unfold is_true2, is_true, toBool.
  split;intro H;decide (f x x0);auto. congruence.
Qed.

Lemma decision_prop_iff (P : Prop) (Hdec : dec P)
  : @toBool P (decision P) = true  <-> P.
Proof.
  split;unfold toBool;intro H;decide P;auto;congruence.
Qed.
