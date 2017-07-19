
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
  Variable Lab : Type.
  Variable Var : Type.
  Variable Val : Type.
  Variable init_uni : Var -> Prop.

  Definition IVec := (list nat).
  Definition State := Var -> Val.
  Definition Coord := prod Lab IVec.
  Definition Conf := prod Coord State.

  Variable eff : Conf -> option Conf.
  Variable has_edge : Lab -> Lab -> Prop.
  Variable dummy : Conf.
  Variable root : Lab.
  Variable initial_uni : Var -> Prop.
  Variable is_root : Lab -> bool.
  Variable is_root_spec : forall l, is_root l = true <-> l = root.

  Definition start_coord := (root, @nil nat) : Coord.

  Definition is_effect_on (p q : Lab) :=
    exists i i' s s', eff ((p, i), s) = Some ((q, i'), s').

  Variables edge_spec :
    forall p q, is_effect_on p q -> has_edge p q.
  
  Inductive tr : list Conf -> Prop := 
    | Init : forall s, tr ((start_coord, s) :: nil)
    | Step : forall k k' t, tr (k :: t) -> eff k = Some k' -> tr (k' :: k :: t).

  Definition Trace := list Conf.
  Definition Traces := Trace -> Prop.
  Definition Hyper := Traces -> Prop.

  (* This is the concrete transformer for sets of traces *)
  Definition sem_trace (ts : Traces) : Traces :=
    fun t' => (exists s, ts ((start_coord, s) :: nil))
              \/ (exists k k' t, ts (k :: t) /\ Some k' = eff k /\ t' = k' :: k :: t). 

  Definition Uni := Lab -> Var -> Prop.
  Definition Hom := Lab -> Prop.

  Definition sem_hyper (T : Hyper) : Hyper :=
    fun ts' => exists ts, T ts /\ ts' = sem_trace ts.

  Definition traces (ts : Traces) : Prop :=
    forall t, ts t -> tr t.
    (* (forall s, ts ((start_coord, s) :: nil)) /\ forall t, ts t -> ts (step t). *)

  Definition uni_concr (u : Uni) : Hyper :=
   fun ts => traces ts /\
              forall t t', ts t -> ts t' ->
                           forall x p i s s', In ((p, i), s) t ->
                                              In ((p, i), s') t' ->
                                              u p x -> s x = s' x.


  Definition hom_concr (h : Hom) : Hyper :=
    fun ts => traces ts /\
              forall t t', ts t -> ts t' ->
                           forall p, h p ->
                                     forall q q' j j' i s s' s1 s2, In2 ((q, j), s) ((p, i), s1) t ->
                                                                    In2 ((q', j'), s') ((p, i), s2) t ->
                                                                    q = q' /\ j = j'.
  Definition red_prod (h h' : Hyper) : Hyper :=
    fun ts => h ts /\ h' ts.
  
  Definition uni_trans (uni : Uni) (hom : Hom) : Uni :=
    fun p => match is_root p with
             | true => init_uni
             | false => fun x => hom p /\ forall q, has_edge q p -> uni q x
             end.

  (*
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
*)

  Lemma all_sem_trace :
    forall ts, traces ts -> traces (sem_trace ts).
  Proof.
    intros.
    unfold traces in *.
    intros.
    unfold sem_trace in *.
    destruct H0.
    destruct H0.
    subst.
    specialize (H ((start_coord, x) :: nil) H0).
    destruct H as [Hstart Hstep].
    split; intros; unfold sem_trace.
    + left. exists s. reflexivity.
    + right. exists t. split; try reflexivity.
      destruct H; destruct H; subst.
      - apply Hstart.
      - destruct H; subst. auto.
  Qed.

  Lemma in_root :
    forall (s : State) t ts, traces ts -> ts t -> In (start_coord, s) t -> t = (start_coord, s) :: nil.
  Proof.
    intros s t ts Ht Histrace Hin. 
    unfold traces in Ht.
    induction (step t).
    inversion Hin.
    destruct Ht.
    + 
    inversion H.

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
    destruct HCuni as [Hclosed HCuni].

    split.
    + apply all_sem_trace. assumption.
    + intros t t' HTrace HTrace' x p i s s'.
      intros HIn HIn' Htrans.
      unfold uni_trans in Htrans.
      destruct HTrace as [[s0 Hstart] | Hstep]; subst.
      - destruct HTrace' as [[s0' Hstart'] | Hstep']; subst.
        * destruct Hclosed as [Hclosed _].
          specialize (HCuni ((start_coord, s0) :: nil) ((start_coord, s0') :: nil)).
          eapply HCuni; try auto.
          apply HIn.
          apply HIn'.
          admit.
        * 
        
        inversion HIn; subst.
        inversion HIn; try contradiction; subst.
        inversion HIn'; try contradiction; subst.
        * 
      destruct HTrace' as [r' [Hr' Hstep']].
      subst.
      apply Hclosed in Hr.
      apply Hclosed in Hr'.
      specialize (HChom (step r) (step r') Hr Hr' p Hhom).
      unfold uni_concr in HCuni.
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
  
 