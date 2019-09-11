Require Export PreSuffix NeList.


Lemma postfix_map (* unused *){A B : Type} (f : A -> B) :
  forall l l', Postfix l l' -> Postfix (map f l) (map f l').
Proof.
  intros ? ? Hpost.
  induction Hpost;[econstructor|rewrite map_rcons;econstructor;assumption].
Qed.

Lemma prefix_nlcons (A : Type) : forall (l l' : list A) (a : A),
    Prefix (a :< l) l' -> Prefix l l'.
Proof.
  destruct l;[intros;eapply prefix_nil|
              cbn;intros;eapply prefix_cons;setoid_rewrite nlcons_to_list at 2;eauto].
Qed.

(** * StrictPrefix **)

Section StrictPre.

  Variable (A : Type).

  Definition StrictPrefix' := 
    fun (l l' : ne_list A) => exists a : A, Prefix (a :<: l) l'.

  Lemma prefix_strictPrefix:
    forall (e : A) (x ϕ : ne_list A), Prefix ϕ x -> StrictPrefix' ϕ (e :<: x).
  Proof.
    intros e x ϕ Hϕ1.
    unfold StrictPrefix'. cbn.
    revert dependent e.
    induction Hϕ1; intros.
    - exists e; econstructor.
    - specialize(IHHϕ1 a). destructH. exists a0. econstructor. auto.
  Qed.

  Lemma StrictPrefix_well_founded : well_founded (StrictPrefix').
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

End StrictPre.