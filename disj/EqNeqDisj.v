Require Export NinR.

Require Export DisjPaths.

Section disj.

  Load X_notations.
  Load X_vars.

  Lemma lc_eq_disj
        (Hdep : depth s = depth q1)
        (Hjeq : j1 = j2)
    : Disjoint (map fst r1) (map fst r2).
  Proof.
    eapply TPath_CPath in Hpath1 as Hpath1'. cbn in Hpath1'.
    eapply local_impl_CFG_path with (h:=q1) in Hpath1';eauto.
    Unshelve. 2: eapply implode_nodes_root_inv. 2: eapply implode_nodes_self.
    destructH.
    eapply impl_list_disjoint;cycle -1.
    4: eapply dep_eq_impl_head_eq in Hdep;eauto; destruct Hdep as [_ Hdep];eauto.
    2,3: unfold last_common' in Hlc; destructH.
    2,3: match goal with
           [ Q : Postfix (?r :r: (?s,_)) _ |- CPath _ _ ((map fst ?r) >: ?s) ]
           => pose (QQ := Q)
         end.
    2,3: eapply postfix_path in QQ;eauto;
      eapply TPath_CPath in QQ; cbn in QQ; rewrite ne_map_nl_rcons in QQ; cbn in QQ;
        eauto.

    assert (forall p i, (p,i) ∈ r1 -> i = j1 /\ implode_nodes C q1 p
                                         \/ ~ implode_nodes C q1 p). admit.
    assert (forall p i, (p,i) ∈ r2 -> i = j1 /\ implode_nodes C q1 p
                                \/ ~ implode_nodes C q1 p) as Q. admit.
    
    intros x Hx1 Hx2.    
    unfold last_common' in Hlc. destructH.
    eapply in_map in Hx2. eapply impl_list_incl in Hx2. cbn in Hx2.
    eapply in_map_iff in Hx2.
    destruct Hx2.
    eapply in_map in Hx1. eapply impl_list_incl in Hx1. cbn in Hx1.
    eapply in_map_iff in Hx1.
    destruct Hx1.
    destruct H0. destruct H1.
    destruct x0,x1. cbn in H1,H0.
    specialize (H e0 t0) as Hx0.
    specialize (Q e t) as Hx1.
    exploit' Hx0. exploit' Hx1.
    destruct Hx0,Hx1;subst.
    - do 2 destructH. subst. eapply Hlc1;eauto.
    - destructH. contradiction.
    - destructH. contradiction.
    - (* now find a corresponding header for `x because of dominance *)
      (* eapply ex_entry in H2. *)
      admit.
  Admitted.
  
  Lemma lc_neq_disj
        (Hdep : depth s = depth q1)
        (Hjneq : j1 <> j2)
    : exists r', Prefix ((get_innermost_loop' q1) :: r') (map fst r2)
            /\ Disjoint (map fst r1) r'.
  Admitted.

End disj.
