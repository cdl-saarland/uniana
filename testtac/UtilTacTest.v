Require Import UtilTac.

  Goal forall (V X Y Z : Type) (x:X) (y:Y) (P : V -> Prop), (X -> Y -> V) -> (forall v:V, P v -> X -> Y -> Z) -> (forall v, P v) -> Z.
    intros V X Y Z x y P Hxy Hv HP. 
    exploit Hxy. exploit Hv. exact Hv.
  Qed.

  Goal forall (X : Type) (P : X -> Prop) (x:X), (forall x, P x) -> True.
    intros. exploit H. exact I.
  Qed.
