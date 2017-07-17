
Require Import List.
Require Import Omega.

Inductive Empty_set : Type := .
Fixpoint nat_iter {T : Type} (n : nat) (f : T -> T) (base : T) :=
  match n with
  | S n' => f (nat_iter n' f base)
  | O => base
  end.
Definition Fin (n : nat): Type := nat_iter n option Empty_set.

Fixpoint members (n : nat) : list (Fin n) :=
  match n with
  | O => nil
  | S n' => @None (Fin n') :: (map (fun e => Some e) (members n'))
  end.

Fixpoint In2 {A : Type} (a a' : A) (l : list A) : Prop :=
  match l with
  | nil => False
  | b :: l' => match hd_error l' with
               | None => False
               | Some b' => (a = b /\ a' = b') \/ In2 a a' l'
               end
  end.


Lemma allin :
  forall n p, n > 0 -> In p (members n).
Proof.
  intros.
  induction H.
  + simpl. cbv in p. destruct p.
    - destruct e; auto.
    - auto.
  + destruct p.
    - simpl. right. 
      apply in_map. apply IHle.
    - simpl. auto.
Qed.

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

  Variables dummy : Conf.
  Definition nodes := members N.


  Definition is_effect_on (p q : Lab) :=
    exists i i' s s', eff ((p, i), s) = Some ((q, i'), s').

  Variables edge_spec :
    forall p q, is_effect_on p q -> has_edge p q = true.

  Definition preds (p : Lab) := filter (fun q => has_edge q p) nodes.

  Definition Trace := list Conf.

  Definition step (t : Trace) : Trace :=
    match t with
    | nil => nil
    | k :: t' => match eff k with
                 | Some k' => k' :: k :: t'
                 | None => dummy :: k :: t'
                 end
    end.

  Definition Traces := Trace -> Prop.
  Definition Hyper := Traces -> Prop.

  (* This is the concrete transformer for sets of traces *)
  Definition sem_trace (ts : Traces) : Traces :=
    fun t' => (exists t, ts t /\ t' = step t).

  Definition sem_hyper (T : Hyper) : Hyper :=
    fun ts' => exists ts, T ts /\ ts' = sem_trace ts.
  
  Definition Uni := Lab -> Var -> Prop.
  Definition Hom := Lab -> Prop.

  Definition traces_closed (ts : Traces) : Prop :=
    forall t,  ts t -> ts (step t).
  
  Definition uni_concr (u : Uni) : Hyper :=
    fun ts => traces_closed ts /\
              forall t t', ts t -> ts t' ->
                           forall x p i s s', In ((p, i), s) t ->
                                              In ((p, i), s') t' ->
                                              u p x -> s x = s' x.

  Definition hom_concr (h : Hom) : Hyper :=
    fun ts => traces_closed ts /\
              forall t t', ts t -> ts t' ->
                           forall p, h p ->
                                     forall q q' j j' i s s' s1 s2, In2 ((q, j), s) ((p, i), s1) t ->
                                                                    In2 ((q', j'), s') ((p, i), s2) t ->
                                                                    q = q' /\ j = j'.
  Definition red_prod (h h' : Hyper) : Hyper :=
    fun ts => h ts /\ h' ts.
  
  Definition uni_trans (uni : Uni) (hom : Hom) : Uni :=
    fun p => fun x => hom p /\ forall q, has_edge q p = true -> uni q x.

  Lemma in_to_in2 :
    forall (k : Conf) (t t' : Trace), In k t -> In k t' -> (exists k' k'', In2 k k' t /\ In2 k k'' t') \/ (t = nil \/ t' = nil).
  Proof.
    intros k t t'.
    intros HIn HIn'.
  Admitted.
    

  Lemma step_rewr :
    forall c t t', 
      c :: t = step t' -> t = t'.
  Proof.
    intros.
    unfold step in H.
    destruct t'.
    inversion H.
    destruct (eff c0); inversion H; subst; reflexivity.
  Qed.

  Lemma uni_correct :
    forall uni hom, forall T,
        sem_hyper (red_prod (uni_concr uni) (hom_concr hom)) T ->
        uni_concr (uni_trans uni hom) T.
  Proof.
    intros uni hom T Hred.
    unfold uni_concr.
    unfold sem_hyper in Hred.
    destruct Hred as [ts [Hconcr Hstep]]; subst.
    unfold red_prod in Hconcr.
    destruct Hconcr as [HCuni HChom].
    destruct HChom as [Hclosed HChom].

    split.
    + unfold traces_closed in *.
      intros.
      unfold sem_trace in *.
      destruct H. destruct H. subst.
      apply Hclosed in H.
      exists (step x).
      auto.
    + intros t t' HTin HTin' x p i s s'.
      intros HIn HIn' Htrans.
      unfold uni_trans in Htrans.
      destruct Htrans as [Hhom Htrans].
      destruct HTin as [r [Hr Hstep]].
      destruct HTin' as [r' [Hr' Hstep']].
      subst.
      apply Hclosed in Hr.
      apply Hclosed in Hr'.
      specialize (HChom (step r) (step r') Hr Hr' p Hhom).
      assert (((p, i, s) :: t) ts).

      apply Hclosed in H.

    intros.

    destruct H as [Hhom Hpred].
    unfold sem_hyper in Hred.
    
    destruct t as [| c t]; try (apply in_nil in HIn; contradiction).
    destruct t' as [| c' t']; try (apply in_nil in HIn'; contradiction).


    
    inversion HIn.
    inversion HIn'.

    Goal 3.

    subst.
    clear HIn HIn'.
    
    simpl in HIn.
    apply step_rewr in Hstep; subst.
    apply step_rewr in Hstep'; subst.
    

    unfold hom_concr in *.
    specialize (HChom r r' Hr Hr' p Hhom).
    unfold uni_concr in HCuni.

    unfold step in *.
    destruct r; try inversion Hstep.
    destruct (eff c0).



    
    inversion HIn; inversion HIn'; subst.



    destruct r; try (inversion Hstep).
    destruct r'; try (inversion Hstep').
    
    unfold uni_concr in HCuni.
    destruct t' as [| c' t']; try (inversion HIn').
    admit.
    , t' as [| c' t']; inversion HIn.
    + inversion HIn'.
    + inversion HIn'.
    + admit.
    + inversion HIn.
    + unfold sem_trace in *.
    unfold uni_concr in *.
    eapply HCuni.

    apply Hr.
    apply Hr'.

    hnf in Hcuni, Hchom.
    eapply Hcuni.
    unfold sem_hyper, sem_trace in *.
    un
    pose proof (Hcuni).
    pose (hom_concr hom T) as H.
    unfold hom_concr in H.
    clearbody H.

    cut (hom_concr hom T).
    unfold hom_concr.
    intros.
    generalize hom.
    apply hom_concr in (hom H0).

    unfold sem_hyper, sem_trace in H.
    unfold 
    intros.
      
End CFG.

  
                  
        
           |
  
 