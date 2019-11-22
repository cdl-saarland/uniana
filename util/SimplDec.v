Require Export FinTypes.


Lemma dec_DM_and_iff (X Y : Prop) : dec X -> ~ (X /\ Y) <-> ~ X \/ ~ Y.
  split;[now eapply dec_DM_and|firstorder].
Qed.
Lemma dec_DM_and_iff' (X Y : Prop) : dec Y -> ~ (X /\ Y) <-> ~ X \/ ~ Y.
  split;[now eapply dec_DM_and'|firstorder].
Qed.
Lemma dec_DN_iff (X : Prop) : dec X -> ~ ~ X <-> X.
  split;[now eapply dec_DN|firstorder].
Qed.
Lemma dec_DM_impl_iff (X Y : Prop) : dec X -> dec Y -> ~ (X -> Y) <-> X /\ ~ Y.
  split;[now eapply dec_DM_impl|firstorder].
Qed.

Ltac simpl_dec' H :=
  (first [(setoid_rewrite (DM_notAll _) in H;eauto)|
          (setoid_rewrite (dec_DM_and_iff _ _) in H;eauto)|
          (setoid_rewrite (dec_DM_and_iff' _ _) in H;eauto)|
          setoid_rewrite DM_not_exists in H|
          setoid_rewrite DM_or in H|
          (setoid_rewrite (dec_DN_iff _) in H;eauto)|
          (setoid_rewrite (dec_DM_impl_iff _ _) in H;eauto)]).
Ltac simpl_dec :=
  (try (setoid_rewrite DM_notAll;[|eauto]);
   try (setoid_rewrite (dec_DM_and_iff _ _);[|eauto]);
   try (setoid_rewrite (dec_DM_and_iff' _ _);[|eauto]);
   try setoid_rewrite DM_not_exists;
   try setoid_rewrite DM_or;
   try (setoid_rewrite (dec_DN_iff _);[|eauto]);
   try (setoid_rewrite (dec_DM_impl_iff _ _);eauto)).

(*Ltac collapse H :=
  lazymatch type of H with
  | ?a /\ ?b => let H1 := fresh "H" in
              let H2 := fresh "H" in
              destruct H as [H1 H2];
              collapse H1;
              collapse H2
  | ?a \/ ?b => destruct H as [H|H]; collapse H
  | ~ ?x => simpl_dec' H; collapse H
  | _ => idtac
  end.*)


