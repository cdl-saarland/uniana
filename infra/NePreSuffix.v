Require Export PreSuffix NeList.



Lemma prefix_nlcons (A : Type) : forall (l l' : list A) (a : A),
    Prefix (a :< l) l' -> Prefix l l'.
Proof.
  destruct l;[intros;eapply prefix_nil|
              cbn;intros;eapply prefix_cons;setoid_rewrite nlcons_to_list at 2;eauto].
Qed.

