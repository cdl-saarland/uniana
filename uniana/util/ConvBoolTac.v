
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.EquivDec.

Lemma beq_true {A : Type} `{EqDec A} (a c : A) :
  (a ==b c) = true <-> (a === c).
Proof.
  unfold equiv_decb; destruct (a == c); firstorder auto with *.
Qed.

Lemma beq_false {A : Type} `{EqDec A} (a b : A) :
  (a ==b b) = false <-> (a =/= b).
Proof.
  unfold equiv_decb; destruct (a == b); firstorder auto with *.
Qed.

Lemma bne_true {A : Type} `{EqDec A} (a c : A) :
  (a <>b c) = true <-> (a =/= c).
Proof.
  unfold nequiv_decb, equiv_decb. rewrite negb_true_iff. destruct (a == c); firstorder auto with *.
Qed.

Lemma bne_false {A : Type} `{EqDec A} (a b : A) :
  (a <>b b) = false <-> (a === b).
Proof.
  unfold nequiv_decb, equiv_decb. rewrite negb_false_iff. destruct (a == b); firstorder auto with *.
Qed.

Definition to_bool {P Q : Prop} (x : {P} + {Q}) := if x then true else false.

Lemma to_bool_true (P : Prop) (x : {P} + {~ P}) : to_bool x = true <-> P.
Proof.
  destruct x; cbn; firstorder auto with *.
Qed.
    
Lemma to_bool_false (P : Prop) (x : {P} + {~P}) : to_bool x = false <-> ~ P.
Proof. 
  destruct x; cbn; firstorder auto with *.
Qed.

Ltac conv_bool := repeat match goal with
                         | [ H: context[_ ==b _ = true] |- _ ] => rewrite beq_true in H
                         | [ H: context[_ ==b _ = false] |- _ ] => rewrite beq_false in H
                         | [ H: context[_ <>b _ = true] |- _ ] => rewrite bne_true in H
                         | [ H: context[_ <>b _ = false] |- _ ] => rewrite bne_false in H
                         | [ H: context[_ || _ = true] |- _ ] => rewrite orb_true_iff in H
                         | [ H: context[_ || _ = false] |- _ ] => rewrite orb_false_iff in H
                         | [ H: context[_ && _ = true] |- _ ] => rewrite andb_true_iff in H
                         | [ H: context[_ && _ = false] |- _ ] => rewrite andb_false_iff in H
                         | [ H: context[to_bool _ = true] |- _ ] => rewrite to_bool_true in H
                         | [ H: context[to_bool _ = false] |- _ ] => rewrite to_bool_false in H
                         | [ H: context[negb (_ && _)] |- _ ] => rewrite negb_andb in H
                         | [ H: context[negb (_ || _ )] |- _ ] => rewrite negb_orb in H
                         | [ |- context[_ ==b _ = true]] => rewrite beq_true
                         | [ |- context[_ ==b _ = false]] => rewrite beq_false
                         | [ |- context[_ <>b _ = true]] => rewrite bne_true
                         | [ |- context[_ <>b _ = false]] => rewrite bne_false
                         | [ |- context[_ || _ = true]] => rewrite orb_true_iff
                         | [ |- context[_ || _ = false]] => rewrite orb_false_iff
                         | [ |- context[_ && _ = true]] => rewrite andb_true_iff
                         | [ |- context[_ && _ = false]] => rewrite andb_false_iff
                         | [ |- context[to_bool _ = true]] => rewrite to_bool_true
                         | [ |- context[to_bool _ = false]] => rewrite to_bool_false
                         | [ |- context[negb (_ && _)]] => rewrite negb_andb
                         | [ |- context[negb (_ || _ )]] => rewrite negb_orb
                         end.
