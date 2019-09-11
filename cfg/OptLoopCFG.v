Require Export LoopCFG.

Instance opt_loop_CFG' `(C : redCFG) (h : Lab)
  : let d := (@decision (@loop_head _ _ _ _ C h) (loop_head_dec _)) in
    let Lab' := @finType_sub_decPred Lab (@loop_nodes Lab edge root a_edge C h) in
    @redCFG (if d then Lab' else Lab)
            ((if d
                 return ((if d then Lab' else Lab)
                         -> (if d then Lab' else Lab) -> bool) then
                (@restrict_edge Lab edge (@loop_nodes Lab edge root a_edge C h))
              else
                edge))
            (match d
                   return (eqtype (type (if d then Lab' else Lab))) with
             | left H => (↓ purify_head H)

                 (*@finType_sub_elem Lab h (@loop_nodes Lab edge root a_edge C h)
                                           (or_introl (@loop_contains_self Lab edge root a_edge C h H)))*)
             | right _ => root
             end)
            ((if d as d
                 return ((if d then Lab' else Lab)
                         -> (if d then Lab' else Lab) -> bool) then
                (@restrict_edge Lab a_edge (@loop_nodes Lab edge root a_edge C h))
              else
                a_edge)).
Proof.
  intros.
  destruct d; eauto. 
Defined.

Definition opt_loop_CFG_type `(C : redCFG) (d : option {h : Lab | loop_head h})
  := (match d with
      | Some (exist _ h H) => loop_CFG_type H
      | None => Lab
      end). 

Instance opt_loop_CFG `(C : redCFG) (d : option {h : Lab | loop_head h})
  : @redCFG (opt_loop_CFG_type d)
            (match d
                   return ((opt_loop_CFG_type d) -> (opt_loop_CFG_type d) -> bool) with
             | Some (exist _ h H) => (@restrict_edge Lab edge (@loop_nodes Lab edge root a_edge C h))
             | None => edge
             end)
            (match d
                   return (eqtype (type (opt_loop_CFG_type d))) with
             | Some (exist _ h H) => (↓ purify_head H) 
             | None => root
             end)
            (match d
                   return ((opt_loop_CFG_type d) -> (opt_loop_CFG_type d) -> bool) with
             | Some (exist _ h H) => (@restrict_edge Lab a_edge (@loop_nodes Lab edge root a_edge C h))
             | None => a_edge
             end).
Proof.
  intros.
  destruct d; [destruct s|]; eauto.
Defined.

Lemma opt_loop_CFG_elem (* unused *)`{C : redCFG} (p : Lab)
      (d : option {h : Lab | loop_head h})
      (Hd : match d with
            | Some (exist _ h _) => loop_contains h p
            | None => True
            end)
  : opt_loop_CFG_type d.
Proof.
  destruct d;[|exact p].
  destruct s. eapply loop_CFG_elem; eauto.
Defined.

Arguments opt_loop_CFG {_ _ _ _} _.
