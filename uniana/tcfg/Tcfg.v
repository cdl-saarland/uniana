Require Export EEdge Tagle.
Require Import PropExtensionality Lia.

Section cfg.
  Context `{C : redCFG}.

  Program Instance Tag_dec : EqDec Tag eq.
  Next Obligation.
    apply list_eqdec, nat_eq_eqdec.
  Qed.

  Definition start_tag : Tag := nil.

  Definition Coord : Type := (Lab * Tag).
  Hint Resolve Tag_dec.

  Program Instance Coord_dec : EqDec Coord eq.
  Next Obligation.
    eapply prod_eqdec;eauto.
  Qed.

  Hint Resolve Coord_dec : tcfg.
  Hint Unfold Coord : tcfg.


  (** ** Basic facts **)

  Definition eff_tag (p q : Lab) (i : Tag)
    := match decision (edge__P p q) with
       | left E => match edge_Edge E with
                  | Enormal _ => Some i
                  | Eback _ => match i with
                              | nil => None
                              | n :: i' => Some ((S n) :: i')
                              end
                  | Eentry _ => Some (0 :: i)
                  | Eexit _ => match i with
                              | nil => None
                              | _ :: i' => Some i'
                              end
                  end
       | _ => None
       end.

  (** * The edge relation on the tagged CFG **)

  Definition tcfg_edge (c c' : Coord) :=
    let (p,i) := c  in
    let (q,j) := c' in
    edge__P p q /\ eff_tag p q i = Some j.

  Notation "pi -t> qj" := (tcfg_edge pi qj) (at level 50).

  (** ** Basic facts **)

  Global Instance tcfg_edge_dec : forall pi qj, dec (pi -t> qj).
  Proof.
    intros. destruct pi as [p i]. destruct qj as [q j].
    cbn. decide (edge__P p q);eauto.
  Qed.

  Lemma tcfg_edge_spec (p q : Lab) i j
    : (p,i) -t> (q,j) <-> edge p q = true /\ eff_tag p q i = Some j.
  Proof.
    reflexivity.
  Qed.

  Definition TPath := Path tcfg_edge.

  Lemma TPath_CPath  c c' π :
    TPath c c' π -> CPath (fst c) (fst c') (map fst π).
  Proof.
    intros Q. dependent induction Q; [|destruct b,c]; econstructor; cbn in *.
    - apply IHQ.
    - conv_bool. firstorder.
  Qed.
End cfg.
