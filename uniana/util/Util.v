Global Set Nested Proofs Allowed.

Require Import List.
Require Import Coq.Program.Utils.

Require Import ConvBoolTac.

(* Some helpers to deal with booleans *)

Section Join.

  Definition join_andb (l : list bool) := fold_right andb true l.

  Lemma join_andb_true_iff {A : Type} : 
    forall f (l : list A), (join_andb (map f l) = true) -> (forall x, List.In x l -> f x = true).
  Proof.
    intros.
    unfold join_andb in H.
    induction l; inversion H0; simpl in H; apply andb_true_iff in H; try subst; destruct H; auto.
  Qed.

  Definition join_orb (l : list bool) := fold_right orb false l.

  Lemma join_orb_true_iff {A : Type} :
    forall f (l : list A), (join_orb (map f l) = true) -> (exists x, List.In x l /\ f x = true).
  Proof.
    intros.
    unfold join_orb in H.
    induction l; simpl in H.
    - inversion H.
    - conv_bool.
      inject H.
      * exists a. simpl. eauto.
      * eapply IHl in H0. destruct H0 as [x [Hin Hf]].
        exists x. simpl. eauto.
  Qed.

End Join.

(**  option extra *)

Section Option.
  
Definition option_fst {A B : Type} (ab : option (A*B)) : option A :=
  match ab with
  | Some ab => Some (fst ab)
  | _ => None
  end.

Definition option_prod {A B : Type} (a : option A) (b : option B) : option (A*B) :=
  match a,b with
  | Some a, Some b => Some (a,b)
  | _,_ => None
  end.

End Option.

(*Infix "∘" := Basics.compose (at level 40).*)
