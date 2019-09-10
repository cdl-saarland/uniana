
Ltac solve_pair_eq :=
  repeat lazymatch goal with
         | [ H : ?a = (?b,?c) |- _ ] => destruct a; inversion H; clear H
         | _  => subst; eauto
         end.


Ltac exploit' H :=
  let p := fresh "Q" in
  lazymatch type of H with
  | ?P -> ?Q => assert P as p; [eauto|specialize (H p); clear p]
  | forall (x : ?P), ?Q => lazymatch goal with
                     | [ p : P |- _ ] => specialize (H p)
                     end
  end.

Ltac exploit H :=
  let p := fresh "Q" in
  lazymatch type of H with
  | ?P -> ?Q => assert P as p; [eauto|specialize (H p); clear p;try exploit H]
  | forall (x : ?P), ?Q => lazymatch goal with
                     | [ p : P |- _ ] => specialize (H p);try exploit H
                     end
  end.


Ltac destructH' H :=
  lazymatch type of H with
  | ?P /\ ?Q => let H1 := fresh H in
              let H2 := fresh H in
              destruct H as [H1 H2]; destructH' H1; destructH' H2
  | exists x, ?P => let x0 := fresh x in
              destruct H as [x0 H]; destructH' H
  | _ => idtac
  end.

Ltac destructH :=
  match goal with
  | [H : ?P /\ ?Q |- _ ] => let H1 := fresh H in
                         let H2 := fresh H in
                         destruct H as [H1 H2]; destructH' H1; destructH' H2
  | [H : exists x, ?P |- _ ] => let x0 := fresh x in
                         destruct H as [x0 H]; destructH' H
  end.

Ltac copy H Q :=
  eapply id in H as Q.


Ltac eapply2 H H1 H2 :=
  eapply H in H2; only 1: eapply H in H1.

Ltac eapply2' H H1 H2 Q1 Q2 :=
  eapply H in H2 as Q2; only 1: eapply H in H1 as Q1.

Ltac subst' :=
  repeat
    match goal with
    | [H:(_,_) = (_,_) |- _] => inversion H; subst; clear H
    | [H: _ = _ /\ _ = _ |- _]=> destruct H; subst
    end.

Ltac split_conj :=
  lazymatch goal with
  | [ |- _ /\ _ ] => split; split_conj
  | [ |- _ <-> _ ] => split; split_conj
  | _ => idtac
  end.