Require Export NeList PreSuffix Decidable Disjoint.

Ltac prove_not_In H Q b :=
  (contradict H; inversion H; eauto; subst b; exfalso; apply Q; reflexivity).

Ltac enrich H :=
  (let h1 := fresh "post" in
   let h2 := fresh "post" in
   eapply postfix_rcons_nil_eq in H as [h1 h2];
   lazymatch type of h1 with
   | ?a = ?b => subst a
   end;
   lazymatch type of h2 with
   | ?a = ?b => subst a
   end).

Ltac prove_last_common' :=
  lazymatch goal with
  | [ |- Postfix ?l ?l] => econstructor
  | [ H : ?a === ?b |- Postfix (nil :r: ?c) (?d :: ?l)] => cbn; rewrite <-H; prove_last_common'
  | [ |- Postfix ?l ?l'] => eauto using postfix_cons, postfix_nil, cons_rcons_assoc
  | [ |- Disjoint ?l ?l'] => unfold Disjoint; firstorder
  | [ |- ~ False] => tauto
  | [ |- ~ In ?a nil] => eauto
  | [H : ~ In ?a ?l, Q : ?a =/= ?b |- ~ In ?a (?b :: ?l)] => prove_not_In H Q b
  | [H : ~ In ?a ?l, Q : ?b =/= ?a |- ~ In ?a (?b :: ?l)] => prove_not_In H Q b
  | [H : ~ In ?b ?l, Q : ?a =/= ?b |- ~ In ?a (?b :: ?l)] => prove_not_In H Q b
  | [H : ~ In ?b ?l, Q : ?b =/= ?a |- ~ In ?a (?b :: ?l)] => prove_not_In H Q b
  | [ |- _ ] => idtac
  end.

Ltac prove_last_common :=
  lazymatch goal with
  | [ H : Postfix (?l :r: ?a) (?b :: nil) |- _ ] => enrich H
  | [ H : Postfix ?a ?b |- _ ] => cbn in H
  | [ |- _ ] => idtac
  end; split_conj; prove_last_common'.
