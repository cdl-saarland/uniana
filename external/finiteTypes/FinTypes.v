Require Export BasicDefinitions.
(** ** Formalisation of finite types using canonical structures and type classes *)

(** * Definition of finite Types *)

(** Type Class for finite Types. Is dependent on the type. *)
Class finTypeC  (type:eqType) : Type := FinTypeC {
                               enum: list type;
                               enum_ok: forall x: type, count enum x = 1
                                          }.

(** Finite Types are not dependent on the type but contains an element of finTypeC *)

Structure finType : Type := FinType {
                                type:> eqType;
                                class: finTypeC type }.
(** Since finTypeC is a Type class it can be infered automatically if the type is known. Therefore finite Types can be declared only using the type, if the corresponding Instance is declared. This is not possible with only canonical structures *)
Arguments FinType type {class}.
Existing Instance class | 0.

(** toeqType is not automatically unfolded when type checking occures. Therefore this has to exists as well, to make stuff type where toeqType is used *)
 Instance FinTypeClass2 (F: finType) :finTypeC (toeqType F) | 1.
Proof.
 now destruct F as [[type eqdec] class].
Defined.

Definition tofinType (T: Type) (_: eq_dec T)  (f: finTypeC _): finType := FinType (toeqType T).
Arguments tofinType T {_} {f}.

 Lemma tofinType_works (T: Type) {H: eq_dec T} {f: finTypeC (toeqType T)} : T = tofinType T.
 Proof.
   reflexivity.
 Qed.

 (** tofinType of a finType does not change the finType *)
 Lemma tofinType_idempotent (Z: finType) : tofinType (tofinType Z) = tofinType Z.
 Proof.
   reflexivity. 
 Qed.

 (** A way to get at the elements of a finType directly from the finType whithout having to use the class *)
Definition elem (F: finType) := @enum (type F) (class F).
Hint Unfold elem.
Hint Unfold class.

Lemma elementIn (X: finType) (x:X) : x el (elem X).
Proof.
  apply countIn.  pose proof (enum_ok x) as H. unfold elem. omega.
Qed.

Hint Resolve elementIn.
Hint Resolve enum_ok.

Lemma allSub (X: finType) (A:list X) : A <<= elem X.
Proof.
  intros x _. apply elementIn.
Qed.
Arguments allSub {X} A a.
Hint Resolve allSub.

  (** A properties that hold on every element of (elem X) hold for every element of the finType X *)
Theorem Equivalence_property_all (X: finType) (p: X -> Prop) :
  (forall x, p x) <-> forall x, x el (elem X) -> p x.
Proof.
  split; auto. 
Qed.

Theorem Equivalence_property_exists (X: finType) (p:X -> Prop):
  (exists x, p x) <-> exists x, x el (elem X) /\ p x.
Proof.
  split.
  - intros [x P]. eauto.
  - intros [x [E P]]. eauto.
Qed.

Theorem Equivalence_property_exists' (X: finType) (p: X -> Prop):
    (exists x, p x) <-> exists x, x el (elem X) -> p x.
Proof.
  split; intros [x H]; eauto.
Qed.

Instance finType_forall_dec (X: finType) (p: X -> Prop): (forall x, dec (p x)) -> dec (forall x, p x).
Proof.
  intros D. eapply dec_trans. Focus 2.
  - symmetry. exact (Equivalence_property_all p).
  - auto.
Qed.

Instance finType_exists_dec (X:finType) (p: X -> Prop) : (forall x, dec (p x)) -> dec (exists x, p x).
Proof.
  intros D. eapply dec_trans. Focus 2.
  - symmetry. exact (Equivalence_property_exists p).
  - auto.
Qed.

Definition finType_cc (X: finType) (p: X -> Prop) (D: forall x, dec (p x)) : (exists x, p x) -> {x | p x}.
Proof.
  intro H.
  assert(exists x, x el (elem X) /\ p x) as E by firstorder.
  pose proof (list_cc D E) as [x G].
  now exists x.
Defined.

Definition pickx (X: finType): X + (X -> False).
Proof.
  destruct X as [X [enum ok]]. induction enum.
  - right. intro x. discriminate (ok x).
  - tauto.
Defined.

 (** * Properties of decidable Propositions *)

 Lemma DM_notAll (X: finType) (p: X -> Prop) (D:forall x, dec (p x)): (~ (forall x, p x)) <-> exists x, ~ (p x).
 Proof.     
   decide (exists x,~ p x); firstorder.
 Qed.

 Lemma DM_exists (X: finType) (p: X -> Prop) (D: forall x, dec (p x)):
   (exists x, p x) <->  ~(forall x, ~ p x).
 Proof.
   split.
   - firstorder.
   - decide (exists x, p x); firstorder.
Qed.     
 
(** * Completeness Lemmas for lists of basic types *)
(** Does not work like that without canonical structures. because second argument of count cannot be infered*)
Lemma bool_enum_ok x:
  count  [true; false] x = 1.
Proof.
  simpl.   dec; destruct x; congruence.
Qed.

(** Just as an example becomes useless in this form with the definition of allInoption*)
Lemma boolOption_enum_ok (x: option bool):
 count [None; Some false; Some true] x = 1. 
Proof.
  simpl. destruct x.
  -  dec; destruct b; congruence.
  -  dec; congruence.    
Qed.

Lemma unit_enum_ok x:
  count [tt] x = 1.
Proof.
 simpl. destruct x; dec; congruence.
Qed.

Lemma Empty_set_enum_ok (x: Empty_set):
  count nil x = 1.
Proof.
  tauto.
Qed.

Lemma True_enum_ok x:
count [I] x = 1.
Proof.
  simpl; dec;  destruct x; congruence.
Qed.

Lemma False_enum_ok (x: False):
  count nil x = 1.
Proof.
  tauto.
Qed.

(** ** Declaration of finTypeCs for base types as instances of the type class *)

Instance finTypeC_bool: finTypeC EqBool.
Proof.
  econstructor. apply bool_enum_ok.
Defined.

Instance finTypeC_unit: finTypeC EqUnit.
Proof. econstructor. apply unit_enum_ok.
Defined.

Instance finTypeC_empty : finTypeC EqEmpty_set.
Proof.
  econstructor. apply Empty_set_enum_ok.
Defined.

Instance finTypeC_True : finTypeC EqTrue.
Proof.
  econstructor. apply True_enum_ok.
Defined.

Instance  finTypeC_False : finTypeC EqFalse.
Proof.
  econstructor. apply False_enum_ok.
Defined.

(** * Canonical structures declarations for finTypes of base types *)
(** Should not be defined using tofinType type since then the inference does not seem to work because to top symbol at one place is always toeqType and everything is made to unit (first canonical structure definition *)

Definition finType_unit : finType := FinType EqUnit.
Definition  finType_bool: finType :=  FinType EqBool.
Definition finType_Empty_set :finType := FinType EqEmpty_set.
Definition finType_True : finType := FinType EqTrue.
Definition finType_False : finType :=  FinType EqFalse.

Canonical Structure  finType_unit.
Canonical Structure finType_bool.
Canonical Structure finType_Empty_set.
Canonical Structure finType_True.
Canonical Structure finType_False.

(** * Correctness of finTypes for basic types 
Lemmas hold because of coercion to Type*)

Goal (bool: Type) = finType_bool.
Proof.
  reflexivity.
Qed.

Goal (unit: Type) = finType_unit.
Proof.
  reflexivity.
Qed.

Goal (Empty_set: Type) = finType_Empty_set.
Proof.
  reflexivity.
Qed.

Goal (True: Type) = finType_True.
Proof.
  reflexivity.
Qed.

Goal (False: Type) = finType_False.
Proof.
  reflexivity.
Qed.

(** The following equalities hold without coercions *)
Set Printing Coercions.
Goal tofinType bool = finType_bool.
Proof.
  reflexivity.
Qed.

Goal tofinType unit = finType_unit.
Proof.
  reflexivity.
Qed.

Goal tofinType Empty_set = finType_Empty_set.
Proof.
  reflexivity.
Qed.

Goal tofinType True = finType_True.
Proof.
  reflexivity.
Qed.

Goal tofinType False = finType_False.
Proof.
  reflexivity.
Qed.
Unset Printing Coercions.
(** ** Completeness lemma and Canonical Structure definition for cartesian product and option types *)
(** In the list which is the cartesian product of two list a tupel (a,b) is contained exactly |a| * |b| times when |x| denotes the number of occurences of x in the original list from which it was taken. *) 

Lemma ProdCount (T1 T2: eqType) (A: list T1) (B: list T2) (a:T1) (b:T2)  :
  count (prodLists A B) (a,b) =  count A a * count B b .
  Proof.
    induction A.
    - reflexivity.
    - cbn. rewrite <- countSplit. rewrite IHA. decide (a = a0) as [E | E].
      + cbn. f_equal. subst a0. apply countMap.
      + rewrite <- plus_O_n. f_equal. now apply countMapZero.
  Qed.

  Lemma prod_enum_ok (T1 T2: finType) (x: T1 * T2):
  count (prodLists (elem T1) (elem T2)) x = 1.
  Proof.
    destruct x as [x y]. rewrite ProdCount. unfold elem.
    now repeat rewrite enum_ok.
  Qed.

 Instance finTypeC_Prod (F1 F2: finType) : finTypeC (F1** F2).
 Proof.
 econstructor.  apply prod_enum_ok.
 Defined.

 (** Wrapping elements in "Some" does not change the number of occurences in a list *)
  Lemma SomeElement (X: eqType) (A: list X) x:
    count (toOptionList A) (Some x) = count A x .
  Proof.
    unfold toOptionList. simpl. dec; try congruence.
    induction A.
    + tauto.  
    + simpl. dec; congruence.
  Qed.

  (** A list produced by toOptionList contains None exactly once *)
  Lemma NoneElement (X: eqType) (A: list X) :
    count (toOptionList A) None = 1.
  Proof.
    unfold toOptionList. simpl. dec; try congruence. f_equal.
    induction A.
    - reflexivity.
    - simpl; dec; congruence.    
 Qed.
  
Lemma option_enum_ok (T: finType) x :
  count (toOptionList (elem T)) x = 1.
Proof.
  destruct x.
  + rewrite SomeElement. apply enum_ok.
  + apply NoneElement.
Qed.

Instance  finTypeC_Option(F: finType): finTypeC (?? F).
Proof.
 eapply FinTypeC.  apply option_enum_ok.
Defined.

(** ** Definition of the actual finTypes for option types and cross products  *)

Canonical Structure finType_Prod (F1 F2: finType) := FinType (F1 ** F2).
Canonical Structure finType_Option (F: finType) := FinType (?? F).

(** ** Potentially useful notations *)
Notation "F1 (x) F2" := (finType_Prod F1 F2) (at level 40, left associativity).
Notation " ? F" := (finType_Option F) (at level 39).

(** ** Correctness proofs for the cross product and option type finTypes from above 
- the produced Type is correct
- the finType contains the correct list of elements*)

(* Problem: Andere Richtung geht nicht *)
Lemma finType_Prod_correct (T1 T2: finType) :
   prod T1 T2  = T1 (x) T2. 
Proof.
reflexivity.
Qed.

Lemma finTypeProd_enum (T1 T2: finType) :
  prodLists (elem T1) (elem T2) = elem (T1 (x) T2). 
Proof.
  reflexivity.
Qed.

Lemma finTypeOption_correct (T: finType) :
  option T = ? T.
Proof.
  reflexivity.
Qed.

Lemma finTypeOption_enum (T: finType) :
  toOptionList (elem T) = elem (? T). 
Proof.
  reflexivity.
Qed.
(* The following equations hold without the use of coercions *)
Set Printing Coercions.
Goal forall (F1 F2: finType), tofinType (F1 * F2) = F1 (x) F2.
Proof.
  reflexivity.
Qed.

Goal forall (F: finType), tofinType (option F) = ? F.
Proof.
  reflexivity.
Qed.
Unset Printing Coercions.
(** * Tests and Examples *)
Section Test.


  (** Function returning the first position of an element in a list. Returns 0 if the element is not in the list *)
  Fixpoint  getPosition {E: eqType} (A: list E) x := match A with
                                                   | nil => 0
                                                   | cons x' A' => if decision (x=x') then 0 else 1 + getPosition A' x end.

  (* Returns the position of an element of a finite Type in the list of elements *)
  Definition index {F: finType} (x:F) := getPosition (elem F) x.
  Notation "# x" := (index x) (at level 65).
  
  (** ** Tests whether Type inference works correctly *)
 (** Function returning the nth element of a list (Returns an Option ) *)
 
Lemma CardIn (Z: Type) (z: Z) (A: list Z) : z el A -> | A | >= 1.
Proof.
  destruct A; cbn; [> tauto | omega ].
Qed.
   
Definition Cardinality (F: finType) := | elem F |.


 (** * Examples depending on type classes *)
 Definition expl : eqType := toeqType (bool * unit).
 (** ** Great Success
- This example did not work with just Type classes since there was no cross product rule for arbitrary types.
- This did not work with just canonical structures because tofintype depends on type classes.
- Together this works beautifully *)
 Definition finType_BoolUnit := tofinType (bool * unit).
 Variables X Y: finType.
 Definition success2: finType := tofinType (X * Y).
 Definition success3 : finType := tofinType (option bool).
 (** These things do not work because eqTypes are expected. *)
Fail  Definition Example1 := FinType (bool ** unit).
Fail Definition Example2 := FinType (bool * unit)%type.
(** These alternatives do work *)
Definition Example1 := FinType (bool ** unit)%type.
Definition Example2 := tofinType (bool * unit).
(** toeqType of a finType is the same as the coercion *)
Set Printing Coercions.
 Goal toeqType X = X.
 Proof.
unfold toeqType. destruct X as [X' [A AI]].  destruct X'. reflexivity.
 Qed.
Unset Printing Coercions.
 
 
End Test.


(** * Definition of sum Type as finType *)

(** The sum of two nats can only be 1 if one of them is 1 and the other one is 0 *)
Lemma proveOne m n: m = 1 /\ n = 0 \/ n = 1 /\ m = 0 -> m + n = 1.
Proof.
  omega.
Qed.

Lemma sum_enum_ok (X: finType) (Y: finType) x :
  count (toSumList1 Y (elem X) ++ toSumList2 X (elem Y)) x = 1.
Proof.
  rewrite <- countSplit. apply proveOne. destruct x.
  - left. split.
    + rewrite toSumList1_count. apply enum_ok.
    + apply toSumList2_missing.
  - right. split.
    + rewrite toSumList2_count. apply enum_ok.
    + apply toSumList1_missing.
Qed.

(** Instance declaration for sum types for  the type class *)
Instance finTypeC_sum (X Y: finType) : finTypeC (EqSum X Y).
Proof.
  eapply FinTypeC. apply sum_enum_ok.
Defined.

Canonical Structure finType_sum (X Y: finType): finType := FinType (EqSum X Y).
Notation "X (+) Y" := (finType_sum X Y) (at level 50, left associativity).

Lemma finTypeSum_correct (X Y: finType): (X + Y)%type = X (+) Y.
Proof.
  reflexivity.
Qed.

Lemma finTypeSum_enum (X Y: finType) :
  (toSumList1 Y (elem X) ++ toSumList2 X (elem Y)) = elem (X (+) Y).
Proof.
  reflexivity.
Qed. 
Set Printing Coercions.
Goal forall (F1 F2 : finType), tofinType (F1 + F2) = F1 (+) F2.
Proof.
  reflexivity.
Qed.
Unset Printing Coercions.
(** * Dupfreeness *)
(* Proofs about dupfreeness *)


Lemma dupfree_countOne (X: eqType) (A: list X) : (forall x, count A x <= 1) -> dupfree A.
Proof.
  induction A.
  - constructor.
  - intro H. constructor.
    + cbn in H.  specialize (H a). deq a. assert (count A a = 0) by omega. now apply countZero.
    + apply IHA. intro x. specialize (H x). cbn in H. dec; omega.
Qed.

Lemma dupfree_elements (X: finType) : dupfree (elem X).
Proof.
  destruct X as [X [A AI]]. assert (forall x, count A x <= 1) as H'.
  {
    intro x. specialize (AI x). omega.
  }
now apply dupfree_countOne.  
Qed.

Lemma dupfree_length (X: finType) (A: list X) : dupfree A -> |A| <= Cardinality X.
Proof.
  unfold Cardinality.  intros D.
  rewrite <- (dupfree_card D). rewrite <- (dupfree_card (dupfree_elements X)).
  apply card_le. apply allSub.
Qed.

Lemma disjoint_concat X (A: list (list X)) (B: list X) : (forall C, C el A -> disjoint B C) -> disjoint B (concat A).
Proof.
  intros H. induction A.
  - cbn. auto.
  - cbn. apply disjoint_symm. apply disjoint_app. split; auto using disjoint_symm.
Qed.

Lemma dupfree_concat (X: Type) (A: list (list X)) : (forall B, B el A -> dupfree B) /\ (forall B C, B <> C -> B el A -> C el A -> disjoint B C) -> dupfree A -> dupfree (concat A).
Proof.
  induction A.
  - constructor.
  - intros [H H'] D. cbn. apply dupfree_app.
    + apply disjoint_concat. intros C E. apply H'; auto. inv D. intro G; apply H2. now subst a.
    + now apply H.
    + inv D; apply IHA; auto.
Qed.     

(** * Definition of vectors (extensional/ set theoretic functions) 
  structure containing a list representing the image and a proof that the list has exactly as many elements as the source type *)
Definition Card_X_eq X Y (A: list Y) := |A| = Cardinality X.
Definition vector (X: finType) (Y: Type) := subtype (@Card_X_eq X Y).
Notation "X --> Y" := (vector X Y) (at level 55, right associativity).
Hint Unfold pure.
Hint Unfold Card_X_eq.
(** Projects the list from a STF *)
Definition image (X: finType) (Y: Type) (f: X --> Y) := proj1_sig  f.

(** Instance Declaration for Type decision Type class for vectors. *)
Instance vector_eq_dec (X: finType) (Y: eqType) : eq_dec (X --> Y).
Proof.
  auto.
Qed.

Canonical Structure EqVect (X: finType) (Y: eqType) := EqType (X --> Y).

(** Function which produces a list of all list containing elements from A with length n *)
Fixpoint images (Y: Type) (A: list Y) (n: nat): list (list Y) :=
  match n with
  | 0 => [[]]
  | S n' => concat (map (fun x => map (cons x) (images A n')) A)
  end.

Lemma imagesNonempty (Y: Type) y (A: list Y) : forall n, images (y::A) n <> nil.
Proof.
  intro n. induction n.
  - cbn. congruence.
  - cbn. intro H. pose proof (app_eq_nil _ _ H) as [E1 E2]. clear H. pose proof (map_eq_nil _ _ E1).  auto.
Qed.

(** If x is unequal to y then a list starting with y cannot be found in a list of list all starting with x *)
Lemma notInMapCons (X: Type) (x y: X) (A: list X) (B: list (list X)):
  x <> y -> y::A el (map (cons x) B) -> False.
Proof.
  intros neq E. rewrite in_map_iff in E. destruct E as [C [E _]]. congruence.
Qed.

Definition mC X B := (fun x:X => map (cons x) B).
Definition mmC  X B (A: list X) := map (mC B) A.

Lemma disjoint_map_cons X (A: list (list X)) (x y: X): x <> y -> disjoint (map (cons x) A) (map (cons y) A).
Proof.
  intro N; induction A.
  - cbn. auto.
  - cbn. unfold disjoint. intros [B [H1 H2]]. destruct H1, H2.
    + congruence.
    + subst B. eapply notInMapCons. Focus 2.
      * apply H0.
      * congruence.
    + subst B. eapply notInMapCons; eauto.
    + apply IHA. now exists B.
Qed.  

Lemma disjoint_in (X: Type) x A (B: list (list X)) (E: B <> nil) B' (H: ~ x el A): B' el map (mC B) A -> disjoint (map (cons x) B) B'. 
Proof.
  destruct B; try congruence.
  intro H'. induction A.
  - contradiction H'.
  - pose proof (negOr H) as [G G']. destruct H' as [H' | H'].
    + subst B'. apply disjoint_map_cons; congruence.
    + apply IHA; auto.
Qed.

Lemma disjoint_in_map_map_cons X  (A: list X) (B C C': list (list X)) (H: C <> C') (E: C el (mmC B A)) (E': C' el (mmC B A)) (N: B <> nil) (D: dupfree A):
  disjoint C C'.
Proof. 
  induction D.
  - contradiction E.
  - destruct B; try congruence; clear N. destruct E, E'; try congruence.
    + subst C. eapply disjoint_in; now eauto.
    + subst C'. apply disjoint_symm. eapply disjoint_in; now  eauto.
    + now apply IHD.
Qed.      
  
Lemma dupfree_concat_map_cons (X: Type) (A: list X) (B: list (list X)):
  dupfree A -> dupfree B -> B <> nil ->  dupfree (concat (map (fun x => map (cons x) B) A)).
Proof.
  intros D D' N. apply dupfree_concat; try split.
  - intros C E. induction D.
    +  contradiction E.
    + destruct E; auto. subst C. apply dupfree_map; auto. congruence.
  -  intros B' B'' E E' H. eapply disjoint_in_map_map_cons; eauto.
  - apply dupfree_map; auto. intros x y _ _ E. destruct B.
      + congruence.
      +  cbn in E. now inv E.
Qed.

Lemma imagesDupfree (Y: Type) (A: list Y) (n:nat) : dupfree A -> dupfree (images A n).
Proof.
  induction n.
  - now repeat constructor.
  - cbn. intro D. destruct A.
    +constructor.
    + apply dupfree_concat_map_cons; auto. apply imagesNonempty.
Qed.

Lemma inConcatCons (Y: Type) (A C: list Y) (B: list (list Y)) y: y el A /\ C el B -> (y::C) el (concat (map (fun x => map (cons x) B) A)).
Proof.
  intros [E E']. induction A.
  - contradiction E.
  - cbn. destruct E as [E | E].
    + subst a. apply in_app_iff. left. apply in_map_iff. now exists C.
    + auto. 
Qed.                                                               
    
Lemma inImages (Y: Type) (A B: list Y): (forall x, x el B -> x el A) -> B el images A (|B|).
Proof.
 intros E. induction B.
  - cbn. now left.
  - cbn. apply inConcatCons. auto.
Qed.      
 
(** images produces a list of containing all lists of correct length *)
Lemma vector_enum_ok (X: finType) (Y: finType) f:
|f| = Cardinality X -> count (images  (elem Y) (Cardinality X)) f= 1.
Proof.
  intros H. apply dupfreeCount.
  - apply imagesDupfree. apply dupfree_elements.
  - rewrite <- H. now apply inImages.
Qed.

(** FunctionLists A n only produces lists of length n *)
Lemma imagesInnerLength (Y: Type) (n: nat) :
  forall (A: list Y) B, B el (images A n) -> | B | = n.
Proof.
  induction n; intros A B; cbn.
  - intros H. destruct H; try tauto. now subst B.
  - pattern A at 1. generalize A at 2. induction A; cbn.
    +  tauto.
    + intros C E. destruct (in_app_or  _ _ B E) as [H|H].
      * pose proof (in_map_iff (cons a)  (images C n) B) as [G _]. specialize (G H); clear H.
        destruct G as [D [H G]]. specialize (IHn  _ _ G). subst B. cbn. omega.
      * now apply (IHA C).
Qed.

(** Function converting a list (list Y) containing lists of length Cardinality X into a lists of vectors (X --> Y) *)
Definition extensionalPower (X Y: finType) (L: list (list Y))  (P: L <<= images (elem Y) (Cardinality X)): list (X --> Y).
Proof.
  revert L P.
  refine (fix extPow L P :=  _). destruct L.
  -  exact nil.
  - apply cons.
   + exists l. specialize (P l (or_introl eq_refl)). unfold pure. dec; auto. contradiction ( n (imagesInnerLength P)).
   + eapply extPow. intros A E. apply P. exact (or_intror E).
Defined.

(** To vectors  are equal if there images are equal *)
Lemma vector_extensionality (X: finType) (Y: Type) (F G: X --> Y) : (image F = image G) -> F = G.
Proof.
  apply subtype_extensionality. 
Qed.
      
(** The number if occurences of a function in extensionalpower is equal to the number of occurences of its image in the original list given to extensionalpower as an argument *)
 Lemma counttFL X Y L P f :
  count (@extensionalPower X Y L P) f = count L (image f).
Proof.
  induction L.
  -   reflexivity.
  - simpl. dec; rename a into A; decide (image f = A).
    +  now rewrite IHL.
    +contradict n. now subst f.      
    +  contradict n. now apply vector_extensionality.
    + apply IHL.        
Qed.

Instance finTypeC_vector (X Y: finType) :
  finTypeC (EqVect X Y).
Proof.
 apply (FinTypeC (enum := @extensionalPower _ _ (images (elem Y) (Cardinality X)) (fun x => fun y => y))).
 intro f. rewrite counttFL. apply vector_enum_ok. destruct f as [A p]. cbn. now impurify p.
Defined.

Canonical Structure finType_vector (X Y: finType) := FinType (EqVect X Y).

Notation "Y ^ X" := (finType_vector X Y).

Lemma finType_vector_correct (X Y: finType):
  X --> Y =  Y^ X.
Proof.
  reflexivity.
Qed.

Lemma finType_vector_enum (X Y: finType):
  elem (Y^ X) = @extensionalPower _ _ (images (elem Y) (Cardinality X)) (fun x => fun y => y).
Proof.
  reflexivity.
Qed.

Set Printing Coercions.

Lemma tofinType_vector_correct (X Y: finType):
  tofinType (X --> Y) = Y ^ X.
Proof.
  reflexivity.
Qed.
Unset Printing Coercions.
(** ** Conversion between vectors and functions *)
Notation "# x" := (index x) (at level 65).
(** Returns the element of A at position n, if A does not have a position n x is returned. *)
Fixpoint getAt (X: Type) (A: list X)(n: nat) (x:X) : X :=
 match n with
 | 0 =>  match A with         
       | nil => x                 
       | cons a A' => a                       
       end         
 | (S n') => match A with
              |nil => x
              | cons _ A' => getAt A' n' x
              end
 end.

(** Function that applies a vector to an argument *)                
Definition applyVect (X: finType) (Y: Type) (f: X --> Y): X -> Y.
Proof.
  refine (fun x: X => _).
  destruct (elem X) eqn: E.
  - exfalso. pose proof (elementIn x). now rewrite E in H.    
  - destruct f as [image p]. destruct image.
    + exfalso. unfold Card_X_eq, Cardinality in p. rewrite E in p. now impurify p.
    + exact (getAt (y::image0) (# x) y).
Defined.

Coercion applyVect: vector >-> Funclass.

(** A function converting A function f into the list representing its image on elements of A*)
Definition getImage {X: finType} {Y: Type} (f: X -> Y) :=map f (elem X).

(** getImage contains the right elements *)
Lemma getImage_in (X: finType) (Y: Type) (f: X -> Y) (x:X) : (f x) el (getImage f).
Proof.
  unfold getImage. now apply in_map.
 Qed.
(** getImage only produces lists of the correct length *)
Lemma getImage_length (X: finType) (Y: Type) (f: X -> Y) :  |getImage f| = Cardinality X.
Proof.
  apply map_length.
Qed.

(** Function converting a function into a vector *)
Definition vectorise {X: finType} {Y: Type} (f: X -> Y) : X --> Y :=
  exist (pure (@Card_X_eq X Y)) (getImage f) (purify (getImage_length f)).

Lemma getImage_correct (X:finType) (Y:Type) (f: X -> Y):
  getImage f = image (vectorise f).
Proof.
  reflexivity.
Qed.

(** A generalisation of a late case of apply_toVector_inverse *)
Lemma HelpApply (X: eqType) (Y: Type) (A: list X) (f: X -> Y) x y (C: count A x > 0):
  getAt (map f A) (getPosition A x) y = f x.
Proof.
  induction A.
  - cbn in *. omega.
  - cbn in *. dec.
    + congruence.
    + now apply IHA.
Qed.

(** If a function is converted into a vector and then applied to an argument the result is the same as if one had just applied the function to the argument *)
Lemma apply_vectorise_inverse (X: finType) (Y: Type) (f: X -> Y) (x: X) :
    (vectorise f) x = f x.  
Proof.
 destruct X as [X [A ok]]. destruct A.
  - discriminate (ok x).
  - cbn  in  *. specialize (ok x). dec.
    + congruence.
    + apply HelpApply. omega.
Qed.

(** The position of x in a list containg x exactly once is one greater than the size of the sublist befor x *)
Lemma countNumberApp (X: eqType) (x:X) (A B: list X)  (ok : count (A ++ x::B) x = 1) :
  getPosition (A ++ x::B) x = |A|.
Proof.
  induction A.
  - cbn. now deq x.
  - cbn in *. dec.
    + inv ok. pose proof (countApp a A B). omega.
    + auto.
Qed.

Lemma getAt_correct (Y:Type) (A A': list Y) y y':
getAt (A' ++ y::A) (|A'|) y' = y.
Proof.
  induction A'; cbn.
  - reflexivity.
  - cbn in *. apply IHA'.
Qed.    
    
Lemma rightResult (X: finType) (x:X) (B B': list X) (Y: Type)  (y:Y) (A A': list Y) (H:  pure (@Card_X_eq X Y) (A' ++ y::A))  (H': |A'| = | B'|)  (G: elem X = B' ++ x::B):
 ((exist _ _ H): X --> Y) x = y.
Proof.
destruct X as [X [C ok]]. unfold applyVect. cbn in *. subst C. destruct B'; destruct A' ; cbn in *; impurify H; unfold Card_X_eq in H;  cbn in H.
  -  now deq x. 
  -  rewrite app_length in H.  inv H. omega.
  - rewrite app_length in H. cbn in H. omega.
  - specialize (ok x). dec.
    + subst e. inv ok.  pose proof countApp x B' B. omega.
    + rewrite countNumberApp; auto.
   inv H'. eapply getAt_correct.
Qed.      

Lemma vectorise_apply_inverse' (X: finType) (B B': list X) (Y: Type) (A A' A'': list Y) (H: pure (@Card_X_eq X Y) A'') (H': |A'| = | B' |) (H'': |A| = | B|) (E: A' ++ A = A'') (G: elem X = B' ++ B) :
  map ((exist _ _ H): X --> Y) B= A.
  Proof.
    revert A A' B' H' H'' E G. induction B; intros A A' B' H' H'' E G.
    - cbn. symmetry. now rewrite <- length_zero_iff_nil.
    - cbn. destruct A; try (discriminate H''). f_equal.
      +  subst A''. eapply rightResult.
        * inv H'. exact H1.
        * exact G.
      + apply (IHB A (A' ++ [y]) (B' ++ [a])).
        * repeat rewrite app_length. cbn. omega.
        * now inv H''.
        *  now rewrite app_assoc_reverse.
        * rewrite G.  replace (a::B) with ([a]++B) by auto. now rewrite app_assoc.
  Qed.

Lemma vectorise_apply_inverse (X: finType) (Y: Type) (f: X --> Y): vectorise f = f.
Proof.
  apply vector_extensionality. cbn. destruct f as [A p].
  eapply vectorise_apply_inverse'; eauto using app_nil_l; now impurify p.
Qed.

(** * Proofs about Cardinality *)

Lemma Card_positiv (X: finType) (x:X) : Cardinality X > 0.
Proof.
  pose proof (elementIn x).  unfold Cardinality.  destruct (elem X).
  - contradiction H.
  - cbn. omega.
Qed. 

Lemma Cardinality_card_eq (X: finType): card (elem X) = Cardinality X.
Proof.
  apply dupfree_card. apply dupfree_elements.
Qed.

Lemma card_upper_bound (X: finType) (A: list X): card A <= Cardinality X.
Proof.
 rewrite <-  Cardinality_card_eq. apply card_le. apply allSub.
Qed.  


Lemma injective_dupfree (X: finType) (Y: Type) (A: list X) (f: X -> Y) : injective f -> dupfree (getImage f).
Proof.
  intro inj. unfold injective in inj.
  unfold getImage. apply dupfree_map.
  - firstorder.
  - apply dupfree_elements.
Qed.

Theorem pidgeonHole_inj (X Y: finType) (f: X -> Y) (inj: injective f): Cardinality X <= Cardinality Y.
Proof.
  rewrite <- (getImage_length f). apply dupfree_length. apply (injective_dupfree (elem X) inj).
Qed.

Lemma surj_sub (X Y: finType) (f: X -> Y) (surj: surjective f): elem Y <<= getImage f.
Proof.
intros y E. specialize (surj y). destruct surj as [x H]. subst y. apply getImage_in.
Qed.

Theorem pidgeonHole_surj (X Y: finType) (f: X -> Y) (surj: surjective f): Cardinality X >= Cardinality Y.
Proof.
  rewrite <- (getImage_length f). rewrite <- Cardinality_card_eq.
    pose proof (card_le (surj_sub surj)) as H. pose proof (card_length_leq (getImage f)) as H'. omega.
Qed.

Lemma eq_iff (x y: nat) : x >= y /\ x <= y -> x = y.
Proof.
  omega.
Qed.

Corollary pidgeonHole_bij (X Y: finType) (f: X -> Y) (bij: bijective f):
  Cardinality X = Cardinality Y.
Proof.
  destruct bij as [inj surj]. apply eq_iff. split.
  - now eapply pidgeonHole_surj.
  - eapply pidgeonHole_inj; eauto.
Qed.    

Lemma Prod_Card (X Y: finType) : Cardinality (X (x) Y) = Cardinality X * Cardinality Y.
Proof.
  cbn.  unfold prodLists. unfold Cardinality. induction (elem X). 
  - reflexivity.
  - cbn. rewrite app_length. rewrite IHl. f_equal. apply map_length.
Qed.    

Lemma Option_Card (X: finType) : Cardinality (? X) = S(Cardinality X).
Proof.
  cbn. now rewrite map_length.
Qed.

Lemma SumCard (X Y: finType) : Cardinality (finType_sum X Y) = Cardinality X + Cardinality Y.
Proof.
  unfold Cardinality. cbn. rewrite app_length. unfold toSumList1, toSumList2. now  repeat rewrite map_length.
Qed.

Lemma extPow_length X Y L P: |@extensionalPower X Y L P| = | L |.
Proof.
  induction L.
  -  reflexivity.
  - simpl. f_equal. apply IHL.
Qed.


Lemma concat_map_length (X: Type) (A: list X) (B: list (list X)) :
| concat (map (fun x => map (cons x) B) A) |= |A| * |B|.
Proof.
  induction A.
  - reflexivity.
  - cbn. rewrite app_length. rewrite map_length. congruence.
Qed.    
  
Lemma images_length Y (A: list Y) n : |images A n| = (|A| ^ n)%nat.
Proof.
  induction n.
  - reflexivity.
  - cbn. rewrite concat_map_length.  now rewrite IHn.
Qed.

Lemma Vector_Card (X Y: finType): Cardinality (Y ^ X) = (Cardinality Y ^ (Cardinality X ))%nat.
Proof.
  cbn. rewrite extPow_length. now rewrite images_length.
Qed.


(** * Dependent pairs *)

Fixpoint toSigTList (X: Type) (f: X -> finType) (A: list X) : list (sigT f) :=
  match A with
  | nil => nil
  | cons x A' => (map (existT f x) (elem (f x))) ++ toSigTList f A' end.


Lemma countMapExistT (X: eqType) (f: X -> eqType) (x:X) (A: list (f x)) (y: f x) :
  count (map (existT f x) A) (existT f x y) = count A y.
Proof.
  induction A.
  -  reflexivity.
  - simpl. dec.
    + subst a. f_equal. apply IHA.
    + contradict n. exact (sigT_proj2_fun _ e).
    + subst a. contradict n. reflexivity.
    + exact IHA.
Qed.      

Lemma countMapExistT_Zero (X: eqType) (f: X -> eqType) (x x':X) (A: list (f x)) (y: f x') :
  x <> x' -> count (map (existT f x) A) (existT f x' y) = 0.
Proof.
  intros E. induction A.
  - reflexivity.
  - simpl. dec.
    + contradict E. eapply sigT_proj1_fun; eauto.
    + exact IHA.
Qed.

Lemma toSigTList_count (X: eqType) (f: X -> finType) (A: list X) (s: sigT f):
  count (toSigTList f A) s = count A (projT1 s).
Proof.
  induction A.
  - reflexivity.
  -  destruct s. cbn in *. rewrite <- countSplit. rewrite IHA. dec.
    + change (S (count A x)) with (1 + count A x). f_equal. subst a.
      rewrite (@countMapExistT _ f x (elem (f x)) e). apply enum_ok.
    + change (count A x) with (0+ (count A x)). f_equal. rewrite (@countMapExistT_Zero _ f a x); auto.
Qed.

Lemma sigT_enum_ok (X:finType) (f: X -> finType) (s: sigT f) : count (toSigTList f (elem X)) s = 1.
Proof.
  rewrite toSigTList_count. now pose proof (enum_ok (projT1 s)).
Qed.

Instance finTypeC_sigT (X: finType) (f: X -> finType): finTypeC (EqSigT f).
Proof.
  econstructor.  apply sigT_enum_ok.
Defined.

Canonical Structure finType_sigT (X: finType) (f: X -> finType) := FinType (EqSigT f).

Lemma finType_sigT_correct (X: finType) (f: X -> finType):
  sigT f = finType_sigT f.
Proof.
  reflexivity.
Qed.

Lemma finType_sigT_enum (X: finType) (f: X -> finType) :
  toSigTList f (elem X) = (elem (finType_sigT f)).
Proof.
  reflexivity.
Qed.
Set Printing Coercions.
Lemma tofinType_sigT_correct (X: finType) (f: X -> finType) :
  tofinType (sigT f) = finType_sigT f.
Proof.
  reflexivity.
Qed.
Unset Printing Coercions.
(** * Subtypes *)

Fixpoint toSubList (X: Type) (A: list X) (p: X -> Prop) (D:forall x, dec (p x))  : list (subtype p) :=
  match A with
  | nil => nil
  | cons x A' => match decision (p x) with
                | left px => (exist  _ x (purify px)) :: toSubList A' D
                | right _ => toSubList  A' _ end
  end.

Arguments toSubList {X} A p {D}.

Lemma toSubList_count (X: eqType) (p: X -> Prop) (A: list X) (_:forall x, dec (p x)) x:
  count (toSubList A p) x = count A (proj1_sig x).
Proof.
  induction A.
  - reflexivity.
  - cbn. decide (p a).
    + simpl. dec. 
      * congruence.
      * now rewrite <- subtype_extensionality in e.
      * change a with (proj1_sig (exist (pure p) a (purify p0)))  in e. now rewrite subtype_extensionality in e.
      * exact IHA.        
    + destruct x.  cbn. dec.
      * subst a. now impurify p0.
      * exact IHA.
Qed. 

Lemma subType_enum_ok (X:finType) (p: X -> Prop) (_: forall x, dec (p x)) x:
  count (toSubList (elem X) p) x = 1.
Proof.
  rewrite toSubList_count. apply enum_ok.
Qed.

Instance finTypeC_sub (X:finType) (p: X -> Prop) (_:forall x, dec (p x)): finTypeC (EqSubType p).
Proof.
  econstructor.  apply subType_enum_ok.
Defined.

Canonical Structure finType_sub (X: finType) (p: X -> Prop) (_: forall x, dec (p x))   := FinType (EqSubType p).
Arguments finType_sub {X} p.

Lemma finType_sub_correct (X: finType) (p: X -> Prop) (_: forall x, dec (p x)) : subtype p = finType_sub p _.
Proof.
reflexivity.  
Qed.

Lemma finType_sub_enum (X: finType) (p: X -> Prop) (_: forall x, dec (p x)):
  toSubList (elem X) p= elem (finType_sub p _).
Proof.
reflexivity.  
Qed.
Set Printing Coercions.
Lemma tofinType_sub_correct (X: finType) (p: X -> Prop) (_: forall x, dec (p x)) :
  tofinType (subtype p) = finType_sub p _.
Proof.
  reflexivity.
Qed.

(** * finTypes from Lists 
Conversion of lists over eqTypes to finite types
*)

Lemma in_undup (X: eqType) (A: list X) x : x el A <-> x el (undup A).
Proof.
  now rewrite undup_id_equi.
Qed.

Lemma enum_ok_fromList (X: eqType) (A: list X) x : count (undup (toSubList A (fun x => x el A))) x = 1.
Proof.
  apply dupfreeCount.
  - apply dupfree_undup.
  - rewrite <- in_undup. apply countIn. rewrite toSubList_count.
    destruct x as [x p]. cbn. apply InCount. now impurify p.
Qed.

Instance fromListC (X: eqType) (A: list X) : finTypeC (EqSubType (fun x => x el A)).
Proof.
econstructor. intros [x p]. apply enum_ok_fromList.
Defined.

Canonical Structure finType_fromList (X: eqType) (A: list X) := FinType (EqSubType (fun x => x el A)).

Lemma finType_fromList_correct (X: eqType) (A: list X) :
  map (@proj1_sig _ _) (elem (finType_fromList A)) === A.
Proof.
  cbn. split.
  -  intros x H. destruct (in_map_iff (@proj1_sig _ _) (undup (toSubList A (fun x => x el A))) x) as [H0 _].
     specialize (H0 H). destruct H0 as [[y p] [E _]]. cbn in *. subst y. now impurify p.
  - intros x H. apply in_map_iff.
    eexists. Unshelve. Focus 2.
    + exists x. unfold pure. now dec.
    + cbn. split; auto. apply countIn with (A:= undup (toSubList A _)). rewrite enum_ok_fromList. omega.
Qed.


(** * Finite Closure Iteration *)
Section Fixedpoints.
  Variable X: Type.
  Variable f: X -> X.
  Definition fp x := f x = x.

  Lemma fp_trans x: fp x -> fp (f x).
  Proof.
    congruence.
  Qed.
  
  Lemma fInduction (p: X -> Prop) (x:X) (px: p x) (IHf: forall y, p y -> p (f y)) n: p (Nat.iter n f x).
  Proof.
    induction n.
    - exact px.
    -  firstorder.
  Qed.

Lemma fp_iter_trans x n: fp (Nat.iter n f x) -> forall m, m >= n -> fp (Nat.iter m f x).
Proof.
  intros F m H. induction m.
  - destruct n; auto. omega. 
  - decide (S m = n).
    + now rewrite e.
    + assert (m >= n) as G by omega.
      specialize (IHm G). simpl. now apply fp_trans.
Qed.

End Fixedpoints.

Definition admissible (X: eqType) f := forall A: list X,  fp f A \/ card (f A) > card A.
  

Lemma fp_card_admissible (X:eqType) f n:
  admissible f -> forall A: list X, fp f (Nat.iter n f A) \/ card (Nat.iter n f A) >= n.
 Proof.
   intros M A. induction n.
     - cbn in *. right. omega.
     - simpl in *. destruct IHn as [IHn | IHn] .
       + left.  now apply fp_trans.
       + destruct (M ((Nat.iter n f A))) as [M' | M'].
         * left.  now apply fp_trans.
         * right. omega. 
 Qed.

 Lemma fp_admissible (X:finType) (f: list X -> list X):
   admissible f -> forall A, fp f (Nat.iter (Cardinality X) f A).
 Proof.
   intros F A.
   destruct (fp_card_admissible (Cardinality X) F A) as [H | H].
   - exact H.
   - specialize (F (Nat.iter (Cardinality X) f A)).  destruct F as [F |F].
     + tauto.
     + pose proof (card_upper_bound (f (Nat.iter (Cardinality X) f A))). omega.
Qed. 

Section FiniteClosureIteration.
  Variable X : finType.
  Variable step:list X -> X -> Prop.
  Variable step_dec: forall A x, dec (step A x).

  
  Lemma pick A : {x | step A x /\ ~ (x el A)} + forall x, step A x -> x el A.
  Proof.
    decide (forall x, step A x -> x el A).
    - tauto.
    - left. destruct (DM_notAll _ (p:= fun x => step A x -> x el A)) as [H _].
      destruct (finType_cc _ (H n)) as [x H']. firstorder.
  Defined.

  Definition FCStep A :=
    match (pick A) with
    | inl L => match L with
                exist _ x _ => x::A end
    | inr _ => A end.

  Definition FCIter := Nat.iter (Cardinality X) FCStep.

Lemma FCStep_admissible: admissible FCStep.
Proof.
  intro A.  unfold fp. unfold FCStep. destruct (pick A) as [[y [S ne]] | S];auto.
  right. cbn. dec.
  - tauto.
  - omega.
Qed.

Lemma FCIter_fp A: fp FCStep (FCIter A).
Proof.
  unfold FCIter. apply fp_admissible. exact FCStep_admissible.
Qed.        

(* inclp A p means every x in A satisfies p *)

Lemma FCIter_ind (p: X -> Prop) A :  inclp A p ->  (forall A x , (inclp A p) -> (step A x -> p x)) -> inclp (FCIter A) p.
Proof.
  intros incl H. unfold FCIter. apply fInduction.
  - assumption. 
  - intros B H1 x E. unfold FCStep in E. destruct (pick B) as [[y [S nE]] | S].
    + destruct E as [E|E]; try subst x; eauto.
    + auto.
Qed. 

Lemma Closure x A: fp FCStep A -> step A x -> x el A.
Proof.
  intros F. unfold fp in F.  unfold FCStep in F. destruct (pick A) as [[y _] | S].
  - contradiction (list_cycle F).
  - exact (S x).
Qed.

Lemma Closure_FCIter x A: step (FCIter A) x -> x el (FCIter A).
Proof. apply Closure. apply FCIter_fp.
Qed.

Lemma preservation_step A: A <<= FCStep A.
Proof.
  intro H. unfold FCStep. destruct (pick A) as [[y [S ne]] | S]; cbn; tauto.
Qed.

Lemma preservation_iter A n: A <<= Nat.iter n FCStep A.
Proof.
  intros x E. induction n.
  - assumption.
  - simpl. now apply preservation_step.
Qed.

Lemma preservation_FCIter A: A <<= FCIter A. 
Proof.
 apply preservation_iter.
Qed.

Definition least_fp_containing f (B A: list X) := fp f B /\ A <<= B /\ forall B', fp f B' /\ A <<= B' -> B <<= B'.

Definition step_consistent:= forall A x, step A x -> forall A', A <<= A' -> step A' x.

Lemma step_iter_consistent: step_consistent -> forall A x n, step A x -> step (Nat.iter n FCStep A) x.
Proof.
  intros H A x n S. eapply H.
  - exact S.
  - apply preservation_iter.
Qed.



Lemma step_trans_fp_incl: step_consistent -> forall A B, fp FCStep B -> A <<= B -> forall n, Nat.iter n FCStep A <<= B.
Proof.
 intros ST A B F H n. apply fInduction.
  - exact H.
  - intros B' H'. unfold FCStep at 1. destruct (pick B') as [[y [S _]] | _].
    + specialize (ST  _ _ S _ H'). intros x [E |E].
      * subst x. now apply Closure.
      * auto.
    + exact H'.
Qed.

Lemma step_consistent_least_fp: step_consistent -> forall A, least_fp_containing FCStep (FCIter A) A.
Proof.
  intros ST A.  repeat split.
  - apply FCIter_fp.
  - apply preservation_FCIter.
  - intros B [H H']. now apply step_trans_fp_incl.
Qed.

  (** Dupfreeness of FCIter
- relict of an old proof
- might still be useful in concrete applications *)

Lemma dupfree_FCStep A: dupfree A -> dupfree (FCStep A).
Proof.
  intro DA. unfold FCStep. destruct (pick A) as [[y [S ne]] | S]; auto. now constructor.
Qed.

 Lemma dupfree_iterstep n A: dupfree A -> dupfree (Nat.iter n FCStep A).
 Proof.
   induction n.
   -  now cbn.
   - intro H. simpl. apply dupfree_FCStep; tauto.
 Qed.

 Lemma dupfree_FCIter A : dupfree A -> dupfree (FCIter A).
 Proof.
   apply dupfree_iterstep.
 Qed.

End FiniteClosureIteration.
Arguments FCIter {X} step {step_dec} x.
Arguments FCStep {X} step {step_dec} A.
Arguments pick {X} {step} {step_dec} A.


      