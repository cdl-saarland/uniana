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
    eapply local_impl_CFG_path in Hpath1';eauto.
    Unshelve. 3: eapply implode_nodes_root_inv. 3: eapply implode_nodes_self.
    
    unfold Disjoint.
    (* 
     * Show 
     *)
  Admitted.
  
  Lemma lc_neq_disj
        (Hdep : depth s = depth q1)
        (Hjneq : j1 <> j2)
    : exists r', Prefix ((get_innermost_loop' q1) :: r') (map fst r2)
            /\ Disjoint (map fst r1) r'.
  Admitted.

End disj.
