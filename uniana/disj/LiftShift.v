Require Import EqNeqDisj CncLoop GetSucc.

(* move *)  

Ltac seapply H Q Q'
  := specialize Q as Q';
     eapply H in Q'.

Reserved Infix "-t>" (at level 50).

(** This typeclass serves as a proof environment for loopsplits **)
Class disjPaths `(C : redCFG)
      (q1 q2 s : Lab) (t1 t2 : list (Lab * Tag)) (r1 r2 : list (Lab * Tag)) (j1 j2 k i1 i2 : Tag)
      (e1 e2 qs1 qs2 : Lab) (js1 js2 : Tag) :=
  {
    Hlc : last_common' t1 t2 r1 r2 (s,k);
    Hpath1 : TPath (root,start_tag) (q1,j1) t1
    where "p --> q" := (edge__P p q);
    Hpath2 : TPath (root,start_tag) (q2,j2) t2
    where "pi -t> qj" := (tcfg_edge pi qj);
    Hedge1 : (q1,j1) -t> (e1,i1);
    Hedge2 : (q2,j2) -t> (e2,i2);
    Hsucc1 : (qs1, js1) ≻ (s, k) | (e1, i1) :: t1;
    Hsucc2 : (qs2, js2) ≻ (s, k) | (e2, i2) :: t2;
    Heq12 : eq_loop q1 q2
  }.

Class disjPathsE `(D : disjPaths) (h : Lab) :=
  {
    Hexit1 : exit_edge h q1 e1;
    Hexit2 : exit_edge h q2 e2;
  }.
        

Infix "-t>" := tcfg_edge.


Lemma disjPaths_sym `(D : disjPaths)
  : disjPaths C q2 q1 s t2 t1 r2 r1 j2 j1 k i2 i1 e2 e1 qs2 qs1 js2 js1.
Proof.
  destruct D.
  econstructor;eauto using last_common'_sym. symmetry. eauto.
Defined.

Lemma disjPaths_sym_iff `(C : redCFG) q1 q2 s t1 t2 r1 r2 j1 j2 k i1 i2 e1 e2 qs1 qs2 js1 js2
  : disjPaths C q1 q2 s t1 t2 r1 r2 j1 j2 k i1 i2 e1 e2 qs1 qs2 js1 js2
    <-> disjPaths C q2 q1 s t2 t1 r2 r1 j2 j1 k i2 i1 e2 e1 qs2 qs1 js2 js1.
Proof.
  split; intro; eapply disjPaths_sym; eauto.
Qed.

Lemma disjPathsE_sym `(D : disjPaths) (h : Lab) (D' : disjPathsE D h)
  : disjPathsE (disjPaths_sym D) h.
Proof.
  destruct D'.
  econstructor;eauto.
Qed.

Lemma disjPathsE_sym' `(D : disjPaths) (h : Lab) (D' : disjPathsE (disjPaths_sym D) h)
  : disjPathsE D h.
Proof.
  destruct D. cbn in D'. destruct D'. econstructor;eauto.
Qed.

Lemma q1_eq_q2 `(D : disjPathsE)
  : eq_loop q1 q2.
Proof.
  seapply eq_loop_exiting Hexit1 Hexit1'.
  seapply eq_loop_exiting Hexit2 Hexit2'.
  rewrite <-Hexit1', <-Hexit2'.
  reflexivity. 
Qed.

Hint Resolve Hlc Hpath1 Hpath2 Hexit1 Hexit2 Hsucc1 Hsucc2 q1_eq_q2 Heq12 : disjPaths.

Lemma q2_eq_q1 `(D : disjPathsE)
  : eq_loop q2 q1.
Proof.
  symmetry. eapply q1_eq_q2;eauto.
Qed.

Hint Resolve q2_eq_q1 : disjPaths.

Class impl_dP
      `(D : disjPaths)
      (q : Lab) (j : Tag)
      (q1' q2' e1' e2' s' : local_impl_CFG_type C q)
  :=
    {
      Hq1 : q1 = `q1';
      Hq2 : q2 = `q2';
      He1 : e1 = `e1';
      He2 : e2 = `e2';
      Hocnc : ocnc_loop s q (`s');
(*      Hndeq : ~ deq_loop q s;
      Hsdeq : deq_loop s q;
      Hdeq : deq_loop q q1;*)
      Hjeq : j = j1 \/ j = j2
    }. 

Lemma impl_dP_sym `(I : impl_dP)
  : impl_dP (disjPaths_sym D) j q2' q1' e2' e1' s'.
Proof.
  destruct I;econstructor;eauto.
(*  - eapply eq_loop2. 2:eauto. eapply Heq12. *)
  - destruct Hjeq0; eauto.
Qed.

Lemma deq_succ_implode `(C : redCFG) (p q r : Lab)
      (Hdeq : deq_loop r q)
      (Hedge : edge__P q p)
  : implode_nodes C r p.
Admitted.

(*Lemma ex_impl_dP `(D : disjPaths)*)

Lemma ex_impl_dP1 `(D : disjPaths)
      (Hndeq : ~ deq_loop q1 s)
  : exists q1' q2' e1' e2' s' : local_impl_CFG_type C q1,
    impl_dP D j1 q1' q2' e1' e2' s'.
Proof.
  assert (implode_nodes C q1 q1).
  { left. reflexivity. }
  assert (implode_nodes C q1 q2). 
  { left. eapply eq_loop2;eauto with disjPaths. reflexivity. }
  assert (implode_nodes C q1 e1).
  { eapply deq_succ_implode. 2: eapply Hedge1. reflexivity. }
  assert (implode_nodes C q1 e2).
  { eapply deq_succ_implode. 2: eapply Hedge2. destruct D. eapply Heq13. } 
  specialize (ex_ocnc_loop Hndeq) as Hocnc. destructH.
  assert (implode_nodes C q1 s').
  { right. eapply ocnc_loop_exit;eauto. }
  exists (impl_of_original' H),
  (impl_of_original' H0),
  (impl_of_original' H1),
  (impl_of_original' H2),
  (impl_of_original' H3).
  econstructor;cbn;eauto. (*reflexivity.*)
Qed.

Lemma ex_impl_dP `(D : disjPaths) q
      (Hndeq : ~ deq_loop q s)
      (Hdeq : deq_loop q q1)
  : exists q1' q2' e1' e2' s' : local_impl_CFG_type C q,
    impl_dP D j1 q1' q2' e1' e2' s'.
Proof.
  assert (implode_nodes C q q1).
  { left. auto. }
  assert (implode_nodes C q q2). 
  { left. eapply eq_loop2;eauto with disjPaths. }
  assert (implode_nodes C q e1).
  { eapply deq_succ_implode. 2: eapply Hedge1. auto. }
  assert (implode_nodes C q e2).
  { eapply deq_succ_implode. 2: eapply Hedge2. destruct D. rewrite <-Heq13. auto. } 
  specialize (ex_ocnc_loop Hndeq) as Hocnc. destructH.
  assert (implode_nodes C q s').
  { right. eapply ocnc_loop_exit;eauto. }
  exists (impl_of_original' H),
  (impl_of_original' H0),
  (impl_of_original' H1),
  (impl_of_original' H2),
  (impl_of_original' H3).
  econstructor;cbn;eauto. (*reflexivity.*)
Qed.

Definition t1' `{I : impl_dP} := impl_tlist q t1.
Definition t2' `{I : impl_dP} := impl_tlist q t2.

Definition r1' `{I : impl_dP} := impl_tlist q r1.
Definition r2' `{I : impl_dP} := impl_tlist q r2.

Definition qs1' `{I : impl_dP} := fst (get_succ (s', j) (e1', i1) t1').
Definition qs2' `{I : impl_dP} := fst (get_succ (s', j) (e2', i2) t2').

Definition rr1 `{I : impl_dP} := prefix_nincl (` qs1',j) r1.
Definition rr2 `{I : impl_dP} := prefix_nincl (` qs2',j) r2.
Definition tt1 `{I : impl_dP} := rr1 :r: (s,k) ++ prefix_nincl (s,k) t1.
Definition tt2 `{I : impl_dP} := rr2 :r: (s,k) ++ prefix_nincl (s,k) t2.

Definition qej1 `{I : impl_dP} := get_pred (s,k) (`qs1',j) t1.
Definition qej2 `{I : impl_dP} := get_pred (s,k) (`qs2',j) t2.

Definition qe1 `{I : impl_dP} := fst qej1.
Definition qe2 `{I : impl_dP} := fst qej2.
Definition n1 `{I : impl_dP} := hd 0 (snd qej1).
Definition n2 `{I : impl_dP} := hd 0 (snd qej2).

Definition h' `{I : impl_dP} := get_innermost_loop' (C := local_impl_CFG C q) q1'.

Section implDP.

  Context `{I : impl_dP}. 

  Lemma lift_disjPaths
    : disjPaths (local_impl_CFG C q) q1' q2' s' t1' t2' r1' r2' j1 j2 j i1 i2 e1' e2' qs1' qs2' j j.
  Proof.
  Admitted.

  Lemma lift_disjPathsE
    : disjPathsE lift_disjPaths h'.
  Proof.
  Admitted.

  Lemma disjPaths_shift_lt
        (Htaglt : n1 < n2)
    : disjPaths C qe1 qe2 s tt1 tt2 rr1 rr2 (n1 :: j) (n2 :: j)
                k j j (`qs1') (`qs2') qs1 qs2 js1 js2.
  Proof.
  Admitted.
  
  Lemma disjPathsE_shift_lt
        (Htaglt : n1 < n2)
    : disjPathsE (disjPaths_shift_lt Htaglt) (`s').
  Proof.
  Admitted.
  
  Lemma disjPaths_shift_eq 
        (Htageq : n1 = n2)
    : disjPaths C qe1 qe2 s tt1 tt2 rr1 rr2 (n1 :: j) (n2 :: j)
                k j j (`qs1') (`qs2') qs1 qs2 js1 js2.
  Proof.
  Admitted.

  Lemma disjPathsE_shift_eq 
        (Htageq : n1 = n2)
    : disjPathsE (disjPaths_shift_eq Htageq) (`s').
  Proof.
  Admitted.
  
End implDP.

Lemma qs1'_qs2' `(I : impl_dP)
  : qs1' (I:=I) = qs2' (I:=impl_dP_sym I).
Proof.
  unfold qs1', qs2', t1',t2'. reflexivity.
Qed.

Lemma qej1_qej2 `(I : impl_dP)
  : qej1 (I:=I) = qej2 (I:=impl_dP_sym I).
Proof.
  unfold qej1,qej2. rewrite qs1'_qs2'. reflexivity.
Qed.

Lemma n1_n2 `(I : impl_dP)
  : n1 (I:=I) = n2 (I:=impl_dP_sym I).
Proof.
  unfold n1,n2. rewrite qej1_qej2. reflexivity.
Qed.

Lemma n2_n1 `(I : impl_dP)
  : n2 (I:=I) = n1 (I:=impl_dP_sym I).
Proof.
  unfold n1,n2. rewrite qej1_qej2. reflexivity.
Qed.

Lemma disjPaths_shift_lt2 `(I : impl_dP)
      (Htaglt : n2 < n1)
  : disjPaths C qe1 qe2 s tt1 tt2 rr1 rr2 (n1 :: j) (n2 :: j)
              k j j (`qs1') (`qs2') qs1 qs2 js1 js2.
Proof.
  eapply disjPaths_sym.
  rewrite n1_n2. rewrite n2_n1.
  eapply disjPaths_shift_lt.
  rewrite <-n1_n2. rewrite <-n2_n1. eauto.
Defined.

Lemma disjPathsE_shift_lt2 `(I : impl_dP)
      (Htaglt : n2 < n1)
  : disjPathsE (disjPaths_shift_lt2 Htaglt) (`s').
Proof.
  econstructor. admit. admit.
Admitted.
