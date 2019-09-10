Require Import Coq.Classes.EquivDec.

  Ltac decide' X :=
    let e := fresh "e" in
    let c := fresh "c" in
    lazymatch X with
    | ?a == ?b => destruct X as [e|c]; [destruct e|]
    | _ => lazymatch type of X with
          | ?a == ?b => destruct X as [e|c]; [destruct e|]
          | {_ === _} + {_ =/= _} => destruct X as [e|c]; [destruct e|]
          end
    end.