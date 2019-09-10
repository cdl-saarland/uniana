Require Import ListOrder.

Ltac find_in_splinter :=
  match goal with
    [ H : context C [splinter ?b ?l] |- ?a ∈ ?l]
    => lazymatch b with
        context C' [a] => clear - H; eapply splinter_incl;eauto;firstorder
      end
  end.

Ltac find_succ_rel :=
  match goal with
  | [H : splinter ?l1 ?l |- ?a ≻* ?b | ?l]
    => match l1 with
      | context C [?a']
        => unify a a';
          match l1 with
          | context C [?b']
            => unify b b';
              eapply (splinter_trans (l2:=l1));
              [|apply H]; solve [repeat (econstructor;eauto)]
          end
      end
  end.

Ltac resolve_succ_rt :=
  lazymatch goal with
  | [ Ha : context Ca [?a :: ?c :: _],
           Hb : context Cb [?b] |- ?a ≻* ?b | ?l ]
    => try find_succ_rel; eapply (succ_rt_trans (b:=c));
      [eauto|find_succ_rel|find_succ_rel]
  | [ |- ?a ≻* ?b ≻* ?c | ?l ] => eapply succ_rt_combine;resolve_succ_rt
  end.
