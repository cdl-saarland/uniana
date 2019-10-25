Require Export Tagged ImplodeCFG.

Section tcfg.
  Context `{C : redCFG}.

  Fixpoint impl_tlist (r : Lab) (l : list Coord) :=
    match l with
    | nil => nil
    | (q,j) :: l => match decision (deq_loop r q) with
                  | left H => (impl_of_original' (h:=r) (p:=q) (or_introl H), j) :: impl_tlist r l
                  | right H => match decision (exists e : Lab, exited q e /\ deq_loop r e) with
                              | left Q =>
                                (*
                                   ↓ this would be the sane way to do it, but it differs from
                                     the impl_list' implementation
                                match j with
                                (* we only want the first occurence of the head *)
                                | O :: j'
                                  => (impl_of_original' (or_intror Q), tl j) :: impl_tlist r l
                                | _
                                  => impl_tlist r l
                                end <-- this implementation gives disj_preservation in one direction
                                                       (in general!)
                                 *)
                                let head := (impl_of_original' (or_intror Q),tl j) :: impl_tlist r l in
                                match l with
                                | [] => head
                                | (q',_) :: _ =>
                                  if decision (loop_contains q q')
                                  then impl_tlist r l
                                  else head
                                end
                              | right Q => impl_tlist r l
                              end
                  end
    end.

  Lemma impl_list_impl_tlist h t
    : map fst (impl_tlist h t) = impl_list' h (map fst t).
  Admitted.

  Lemma impl_tlist_tpath (h p q : Lab) t i j
        (Hpath : TPath (p,i) (q,j) t)
        (Hp : implode_nodes C h p)
        (Hq : implode_nodes C h q)
    : exists t', @TPath _ _ _ _ (local_impl_CFG C h) (impl_of_original' Hp,i)
                   (impl_of_original' Hq,j) t'
            /\ ne_to_list t' = impl_tlist h t.
  Admitted.

(*  Lemma impl_tlist_disj1 h t1 t2
        (Hdisj : Disjoint t1 t2)
    : Disjoint (impl_tlist h t) (impl_tlist h t') *)
  Lemma impl_tlist_implode_nodes h p i t
        (Hel : (p,i) ∈ impl_tlist h t)
    : implode_nodes C h (`p).
  Admitted.
  
  Lemma impl_tlist_in h p i t
        (Hel : (p,i) ∈ (impl_tlist h t))
    : match decision (deq_loop h (`p)) with
      | left _ => (`p,i) ∈ t
      | _ =>  exists n, (`p,n :: i) ∈ t
      end.
  Admitted.  

  Lemma impl_tlist_length h p i t
        (Hel : (p,i) ∈ impl_tlist h t)
    : @depth _ _ _ _ (local_impl_CFG C h) p <= depth h.
    clear - Hel.
  Admitted.

  Lemma impl_tlist_skip h p i t
        (Himpl : impl_list'_cond1 h p (map fst t))
    : impl_tlist h ((p,i) :: t) = impl_tlist h t.
    clear - Himpl.
  Admitted.

  Lemma impl_tlist_cons h p i t
        (Himpl : impl_list'_cond2 h p (map fst t))
    : exists i', impl_tlist h ((p,i) :: t)
            = (impl_of_original' (impl_list'2_implode_nodes Himpl),i') :: impl_tlist h t.
    clear - Himpl.
  Admitted.

  Lemma impl_tlist_tag_prefix p t h i i'
        (Himpl : impl_list'_cond2 h p (map fst t))
        (Heq : impl_tlist h ((p,i) :: t)
               = (impl_of_original' (impl_list'2_implode_nodes Himpl),i') :: impl_tlist h t)
    : Prefix i' i.
    clear - Himpl Heq.
  Admitted.

  Lemma impl_tlist_incl (t t' : list Coord) h
        (Hincl : t ⊆ t')
    : impl_tlist h t ⊆ impl_tlist h t'.
    clear - Hincl.
  Admitted.
  
End tcfg.
