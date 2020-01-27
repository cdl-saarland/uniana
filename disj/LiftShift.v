Require Import EqNeqDisj CncLoop GetSucc.

(* move *)  
Fixpoint get_pred (A : eqType) (a e : A) (l : list A) : A :=
  match l with
  | [] => e
  | b :: l0 => if decision (a = b) then hd e l0 else get_pred a e l0
  end.

Ltac seapply H Q Q'
  := specialize Q as Q';
     eapply H in Q'.

Reserved Infix "-t>" (at level 50).

(** This typeclass serves as a proof environment for loopsplits **)
Class disjPaths `(C : redCFG)
      (q1 q2 s : Lab) (t1 t2 : list (Lab * Tag)) (r1 r2 : list (Lab * Tag)) (j1 j2 k : Tag)
      (e1 e2 h qs1 qs2 : Lab) (js1 js2 : Tag) :=
  {
    Hlc : last_common' t1 t2 r1 r2 (s,k);
    Hpath1 : TPath (root,start_tag) (q1,j1) t1;
    Hpath2 : TPath (root,start_tag) (q2,j2) t2
    where "pi -t> qj" := (tcfg_edge pi qj = true);
    Hexit1 : exit_edge h q1 e1;
    Hexit2 : exit_edge h q2 e2;
    Hsucc1 : (qs1, js1) ≻ (s, k) | (e1, tl j1) :: t1;
    Hsucc2 : (qs2, js2) ≻ (s, k) | (e2, tl j2) :: t2;
  }.

Infix "-t>" := tcfg_edge.


Lemma disjPaths_sym `(D : disjPaths)
  : disjPaths C q2 q1 s t2 t1 r2 r1 j2 j1 k e2 e1 h qs2 qs1 js2 js1.
Proof.
  destruct D.
  econstructor;eauto using last_common'_sym.
Qed.


Lemma q1_eq_q2 `(D : disjPaths)
  : eq_loop q1 q2.
Proof.
  seapply eq_loop_exiting Hexit1 Hexit1'.
  seapply eq_loop_exiting Hexit2 Hexit2'.
  rewrite <-Hexit1', <-Hexit2'.
  reflexivity. 
Qed.

Hint Resolve Hlc Hpath1 Hpath2 Hexit1 Hexit2 Hsucc1 Hsucc2 q1_eq_q2 : disjPaths.

Lemma q2_eq_q1 `(D : disjPaths)
  : eq_loop q2 q1.
Proof.
  symmetry. eapply q1_eq_q2;eauto.
Qed.

Hint Resolve q2_eq_q1 : disjPaths.

Class impl_dP
      `(D : disjPaths)
      (q : Lab) (j : Tag)
      (q1' q2' e1' e2' h' s' : local_impl_CFG_type C q)
  :=
    {
      Hq1 : q1 = `q1';
      Hq2 : q2 = `q2';
      He1 : e1 = `e1';
      He2 : e2 = `e2';
      Hh : h = `h';
      Hocnc : ocnc_loop s q (`s');
      Hndeq : ~ deq_loop q s;
      Hsdeq : deq_loop s q;
      Heq : eq_loop q q1;
      Hjeq : j = j1 \/ j = j2
    }. 

Lemma impl_dP_sym `(I : impl_dP)
  : impl_dP (disjPaths_sym D) j q2' q1' e2' e1' h' s'.
Proof.
  destruct I;econstructor;eauto.
  - transitivity (`q1');rewrite <-Hq3;eauto. eauto using q1_eq_q2.
  - destruct Hjeq0; eauto.
Qed.

Lemma ex_impl_dP1 `(D : disjPaths)
      (Hndeq : ~ deq_loop q1 s)
      (Hsdeq : deq_loop s q1)
  : exists q1' q2' e1' e2' h' s' : local_impl_CFG_type C q1,
    impl_dP D j1 q1' q2' e1' e2' h' s'.
Proof.
  assert (implode_nodes C q1 q1).
  { left. reflexivity. }
  assert (implode_nodes C q1 q2). 
  { left. eapply eq_loop2;eauto with disjPaths. reflexivity. }
  assert (implode_nodes C q1 e1).
  { left. eapply deq_loop_exited. eauto with disjPaths. }
  assert (implode_nodes C q1 e2).
  { left. eapply eq_loop1;[eapply q2_eq_q1;eauto|].
    eapply deq_loop_exited. eauto with disjPaths. }
  assert (implode_nodes C q1 h).
  { left. eapply eq_loop_exiting;eauto with disjPaths. }
  specialize (ex_ocnc_loop Hndeq Hsdeq) as Hocnc. destructH.
  assert (implode_nodes C q1 s').
  { right. eapply ocnc_loop_exit;eauto. }
  exists (impl_of_original' H),
  (impl_of_original' H0),
  (impl_of_original' H1),
  (impl_of_original' H2),
  (impl_of_original' H3),
  (impl_of_original' H4).
  econstructor;cbn;eauto. reflexivity.
Qed.


Definition t1' `{I : impl_dP} := impl_tlist q t1.
Definition t2' `{I : impl_dP} := impl_tlist q t2.

Definition r1' `{I : impl_dP} := impl_tlist q r1.
Definition r2' `{I : impl_dP} := impl_tlist q r2.

Definition qs1' `{I : impl_dP} := fst (get_succ (s', j) (e1', tl j1) t1').
Definition qs2' `{I : impl_dP} := fst (get_succ (s', j) (e2', tl j2) t2').

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

Section implDP.

  Context `{I : impl_dP}.

  Lemma lift_disjPaths
    : disjPaths (local_impl_CFG C q) q1' q2' s' t1' t2' r1' r2' j1 j2 j1 e1' e2' h' qs1' qs2' j1 j1.
  Proof.
  Admitted.

  Lemma disjPaths_shift_lt
        (Htaglt : n1 < n2)
    : disjPaths C qe1 qe2 s tt1 tt2 rr1 rr2 (n1 :: j) (n2 :: j)
                k (`qs1') (`qs2') (`s') qs1 qs2 js1 js2.
  Proof.
  Admitted.
  
  Lemma disjPaths_shift_eq 
        (Htageq : n1 = n2)
    (*(Hlatchp : CPath (`q2') (`h') (π ++ [`q2']))
        (Hlatchd : Disjoint (map fst r1) π)*)
    : (* qs1/2 & js1/2 are turned around because it makes reasoning in the appl. easier*)
      disjPaths C qe1 qe2 s tt1 tt2 rr1 rr2 (n1 :: j) (n2 :: j)
                k (`qs1') (`qs2') (`s') qs1 qs2 js1 js2.
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
              k (`qs1') (`qs2') (`s') qs1 qs2 js1 js2.
Proof.
  eapply disjPaths_sym.
  rewrite n1_n2. rewrite n2_n1.
  eapply disjPaths_shift_lt.
  rewrite <-n1_n2. rewrite <-n2_n1. eauto.
Qed.
