Require Export NeList.

Ltac simpl_nl :=
  repeat lazymatch goal with
         | [ |- ne_to_list _ = ne_to_list _] => f_equal
         | [ |- context[ne_front (nlcons ?a ?l)]] => rewrite nlcons_front
         | [ |- context[ne_back (?l >: ?a)]] => rewrite nl_rcons_back
         | [ |- context[ne_back (?l :>: ?a)]] => rewrite ne_rcons_back
         | [ |- context[(_ :< ne_to_list _)]] => rewrite <-nlcons_necons
         | [ |- context[(ne_to_list _ >: _)]] => rewrite <-nercons_nlrcons
         | [ |- context[ne_to_list (_ :< _)]] => rewrite <-nlcons_to_list
         | [ |- context[ne_to_list (_ >: _)]] => rewrite <-rcons_nl_rcons
         | [ |- context[ne_to_list (_ :+: _)]] => rewrite <-neconc_app
         | [ |- context[ne_to_list (_ :+ _)]] => rewrite <-nlconc_to_list
         | [ |- context[ne_map ?f (_ :< _)]] => rewrite ne_map_nlcons
         | [ |- context[ne_to_list (_ :>: _)]] => rewrite <-rcons_necons
         end.

Goal forall (A:Type) (a : A) (l :ne_list A) , ne_to_list l = ne_to_list l. intros. simpl_nl. Qed.
Set Printing Coercions.

Ltac simpl_nl' H := 
  repeat lazymatch type of H with
         | ne_to_list _ = ne_to_list _ => eapply ne_to_list_inj in H
         | ne_to_list ?l = ?a :: nil => rewrite nlcons_to_list in H; apply ne_to_list_inj in H
         | ?a :: nil = ne_to_list ?l => rewrite nlcons_to_list in H; apply ne_to_list_inj in H
         | ne_to_list ?l = nil => symmetry in H; apply ne_to_list_not_nil in H
         | nil = ne_to_list ?l => apply ne_to_list_not_nil in H
         | context[ne_front (nlcons ?a ?l)] => rewrite nlcons_front in H
         | context[ne_back (?l >: ?a)] => rewrite nl_rcons_back in H
         | context[ne_back (?l :>: ?a)] => rewrite ne_rcons_back in H
         | context[(_ :< ne_to_list _)] => rewrite <-nlcons_necons in H
         | context[(ne_to_list _ >:  _)] => rewrite <-nercons_nlrcons in H
         | context[ne_to_list (nlcons _ _)] => rewrite <-nlcons_to_list in H
         | context[ne_to_list (nl_rcons _ _)] => rewrite <-rcons_nl_rcons in H
         | context[ne_map ?f (_ :< _)] => rewrite ne_map_nlcons in H
         | context[ne_to_list (_ :>: _)] => rewrite <-rcons_necons in H
         end.

Ltac cbn_nl :=
  repeat (cbn; simpl_nl).

Ltac cbn_nl' H :=
  repeat (cbn in H; simpl_nl' H).

Ltac ne_r_destruct l :=
  let H := fresh "H" in
  specialize (ne_list_nlrcons l) as H;
  destruct H as [? [? ?]]; subst l.
  
Ltac destr_r x :=
  let Q := fresh "Q" in
  specialize (ne_list_nlrcons x) as Q;
  let a := fresh "a" in
  let l := fresh "l" in
  destruct Q as [a [l Q]];
  rewrite Q in *.
