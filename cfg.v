
Require Import List.

Inductive Empty_set : Type := .
Fixpoint nat_iter {T : Type} (n : nat) (f : T -> T) (base : T) :=
  match n with
  | S n' => f (nat_iter n' f base)
  | O => base
  end.
Definition Fin (n : nat): Type := nat_iter n option Empty_set.

Fixpoint In2 {A : Type} (a a' : A) (l : list A) : Prop :=
  match l with
  | nil => False
  | b :: l' => match hd_error l' with
               | None => False
               | Some b' => (a = b /\ a' = b') \/ In2 a a' l'
               end
  end.

Section CFG.
  Variable N : nat.
  Definition Lab := Fin N.
  Variables Var : Type.
  Variables Val : Type.

  Definition IVec := (list nat).
  Definition State := Var -> Val.
  Definition Coord := prod Lab IVec.
  Definition Conf := prod Coord State.
  Variables eff : Conf -> option Conf.
  Variables has_edge : Lab -> Lab -> bool.

  Definition is_effect_on (p q : Lab) :=
    exists i i' s s', eff ((p, i), s) = Some ((q, i'), s').

  Variables edge_spec :
    forall p q, is_effect_on p q -> has_edge p q = true.

  
  Definition Trace := list Conf.

  Definition step (t : Trace) : Trace :=
    match t with
    | nil => nil
    | k :: t' => match eff k with
                 | Some k' => k' :: t
                 | None => t
                 end
    end.

  Definition Traces := Trace -> Prop.
  Definition Hyper := Traces -> Prop.

  (* This is the concrete transformer for sets of traces *)
  Definition concrete (ts : Traces) : Traces :=
    fun t' =>  ts t' \/ forall t, ts t -> t' = step t.

  Definition Uni := Lab -> Var -> bool.
  Definition Hom := Lab -> bool.
  
  Definition uni_concr (u : Uni) : Hyper :=
    fun ts => forall t t', ts t -> ts t' ->
                           forall x p i s s', In ((p, i), s) t ->
                                              In ((p, i), s') t' ->
                                              u p x = true -> s x = s' x.

  Definition hom_concr (h : Hom) : Hyper :=
    fun ts => forall t t', ts t -> ts t' ->
                           forall p, h p = true ->
                                     forall q q' j j' i s s' s1 s2, In2 ((q, j), s) ((p, i), s1) t ->
                                                                    In2 ((q', j'), s') ((p, i), s2) t ->
                                                                    q = q' /\ j = j'.


End CFG.

  
                  
        
           |
  
 