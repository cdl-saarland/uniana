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
