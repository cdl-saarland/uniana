Require Export Splits SplitsT NodeDisj TcfgDet TcfgReach.
Require Import Lia.

Section splits_sound.
Context `{C : redCFG}.

  Infix "-->" := edge__P.
  Infix "-h>" := head_rewired_edge (at level 70).

  Hint Resolve tcfg_edge_edge : tcfg.

  Lemma take_r_innermost q (j : Tag) h
    : innermost_loop h q -> | j | = depth q -> take_r (depth h) j = j.
  Proof.
    intros. replace (depth h) with (depth q).
    - rewrite <- H0. eapply take_r_self.
    - symmetry. eapply eq_loop_depth. eapply innermost_eq_loop. eassumption.
  Qed.

  Lemma find_last_exit p q u s k i l j r
        (Hedge : (s,k) -t> (u,l))
        (Dlen: | k | = depth s)
        (Hpath : TPath (u,l) (p,i) ((p,i) :: (q,j) :: r))
        (Hsinq : deq_loop s q)
        (Hndeq : ~ deq_loop q s)
        (Hallin : forall x : Lab, x ∈ map fst ((q, j) :: r) -> deq_loop x q)
    : exists e h qe r' r'' n (m : Tag), r = r'' ++ r'
                                   /\ eq_loop e q
                                   /\ loop_contains h s
                                   /\ exit_edge h qe e
                                   /\ take_r (depth h - 1) k = m
                                   /\ tl m = tl j
                                   /\ hd (s,k) r' = (qe, n :: m)
                                   /\ TPath (e,m) (p,i) ((p,i) :: (q,j) :: r'')
                                   /\ TPath (u,l) (e,m) ((e,m) :: r').
  Proof.
    revert dependent j.
    revert dependent i.
    revert dependent q.
    revert dependent p.
    specialize (well_founded_ind (R:=(@StrictPrefix' (Lab * Tag))) (@StrictPrefix_well_founded (Lab * Tag))
                                 (fun r => forall p q : Lab,
                                      deq_loop s q ->
                                      ~ deq_loop q s ->
                                      forall i j : Tag,
                                        TPath (u, l) (p, i) ((p, i) :: (q, j) :: r) ->
                                        (forall x : Lab, x ∈ map fst ((q, j) :: r) -> deq_loop x q) ->
                                        exists (e h qe : Lab) (r' r'' : list (Lab * Tag)) (n : nat) (m : Tag),
                                          r = r'' ++ r'
                                          /\ eq_loop e q
                                          /\ loop_contains h s
                                          /\ exit_edge h qe e
                                          /\ take_r (depth h - 1) k = m
                                          /\ tl m = tl j
                                          /\ hd (s, k) r' = (qe, n :: m)
                                          /\ TPath (e, m) (p, i) ((p, i) :: (q, j) :: r'')
                                          /\ TPath (u, l) (e, m) ((e, m) :: r'))) as WFind.
    eapply WFind.
    intros r' H p q Hsinq Hndeq i j Hpath Hallin.
    clear WFind.
    unfold TPath in Hpath.

    inv Hpath.
    rename H1 into Hpath. rename H4 into Edge1.
    eapply path_front in Hpath as Htmp; subst b.
    inv Hpath.
    - clear H Hallin.
      assert (Hcont' := Hndeq).
      do 2 (simpl_dec' Hcont').
      destruct Hcont' as [h' [Hcont' _]].
      edestruct loop_contains_innermost as [h Hinner]; try eassumption.
      clear h' Hcont'.
      assert (Hhscont : loop_contains h s) by firstorder.
      assert (Hexit : exit_edge h s q). {
        destruct Hedge. eauto using not_deq_edge_is_exit.
      }
      destruct k as [| n j']. {
        eapply loop_contains_depth_lt in Hhscont. rewrite <- Dlen in Hhscont. inv Hhscont.
      }
      replace j' with j in *.
      2: {
        eapply tag_exit_eq in Hexit; try eassumption. simpl in Hexit. eassumption.
      }
      exists q, h, s, [], [], n, j.
      do 4 (split; eauto; try reflexivity).
      split. {
        unfold take_r.
        replace (depth h - 1) with (length j).
        - rewrite take_tl. rewrite 2 rev_involutive. reflexivity.
          rewrite rev_length. reflexivity.
        - eapply eq_loop_exiting in Hexit. rewrite Hexit. rewrite <- Dlen. simpl. lia.
      }
      do 2 (split; [ reflexivity |]).
      split; repeat (econstructor; eassumption).
      econstructor; [ econstructor | eassumption ].
    - rename H1 into Hpath. rename H4 into Edge2.
      destruct b as [b m].
      destruct r' as [| x rb]; [ inv Hpath |].
      eapply path_front in Hpath as Htmp; subst x.
      assert (Hdeqbq : deq_loop b q). {
        eapply Hallin. simpl. eauto.
      }
      assert (Hnoentry : ~ entry_edge b q). {
        intro Hent. destruct Hent as [Hhead [Hent _]].
        apply Hent. unfold deq_loop in Hallin. eapply Hallin.
        simpl. eauto. eauto using loop_contains_self.
      }
      decide (eq_loop q b) as [ Heqqb | Hneqqb ].
      + (* this is the case where q's loop is equal to b's loop. we then can use the induction hypo. *)
        clear Hdeqbq.
        assert (Hprefix : StrictPrefix' rb ((b, m) :: rb)) by (repeat econstructor).
        edestruct H as [e [h [qe [r' [r'' [n' [m' [Hcons [Heq [Hcont [Hexit [Hk [Htail [Hhd [Hp1 Hp2]]]]]]]]]]]]]]].
        * eapply Hprefix.
        * rewrite Heqqb in Hsinq. eapply Hsinq.
        * symmetry in Heqqb. eauto using eq_loop1.
        * econstructor. eapply Hpath. eassumption.
        * intros. eapply eq_loop2. eassumption. eapply Hallin. simpl. eauto.
        * clear H.
          exists e, h, qe, r'. eexists. exists n', m'.
          split. {
            rewrite Hcons. eapply app_comm_cons.
          }
          split. {
            rewrite Heqqb. eassumption.
          }
          do 3 (split; [ eassumption |]).
          split. {
            rewrite Htail.
            destruct Edge2 as [Edge2 Heff].
            unfold eff_tag in Heff. decide (b --> q); [| contradiction ].
            destruct (edge_Edge e0).
            - inv Heff. reflexivity.
            - destruct m; inv Heff. reflexivity.
            - exfalso. eauto.
            - exfalso. destruct e1 as [h' Hexit']. destruct Hexit'. eapply H0.
              rewrite Heqqb. eassumption.
          }

          split; [ eassumption |].
          split; [| eassumption ].
          econstructor; eassumption.
      + (* in this case, we exit a loop from b to q. *)
        assert (Hexit : eexit_edge b q). {
          destruct Edge2 as [He Heff].
          eapply edge_Edge in He.
          inv He.
          - destruct H0 as [H0 _]. symmetry in H0. contradiction.
          - eapply back_edge_eq_loop in H0. symmetry in H0. contradiction.
          - contradiction.
          - eassumption.
        }
        destruct Hexit as [h Hexit].
        (* now, we get two sub-cases:
           from b to q we exit a loop that does not or does contain s *)
        decide (forall x, x ∈ map fst ((b,m) :: rb :r: (s,k)) -> loop_contains h x) as [Hallinh | Hnallinh].
        * clear H.
          assert (Hconts : loop_contains h s). {
            eapply Hallinh. right. rewrite map_app. eapply in_or_app. right. simpl. eauto.
          }
          edestruct (tag_exit_eq' Edge2 Hexit) as [n Hn].
          rewrite Hn in *.
          exists q, h, b, ((b, n :: j) :: rb), [], n, j.
          do 4 (split; [ try reflexivity; eauto |]).
          split. {
            replace j with (take_r (depth h - 1) m).
            - eapply tpath_tag_take_r_eq.
              + eapply path_app.
                1: eapply PathSingle. eassumption.
                rewrite Hn. eassumption.
              (* eapply path_app. eapply Hpath. eassumption. eapply PathSingle. *)
              + intros x Hxin. eapply Hallinh. rewrite Hn in Hxin. eassumption.
              + reflexivity.
            - eapply eq_loop_exiting in Hexit. rewrite Hexit.
              replace (depth b) with (| m |).
              * rewrite Hn. simpl. rewrite Nat.sub_0_r. rewrite take_r_cons_drop; [| constructor ].
                rewrite take_r_self. reflexivity.
              * eapply path_rcons in Hedge;eauto. subst m.
                eapply tag_depth_unroot in Hedge;eauto.
          }
          do 2 (split; try reflexivity).
          split.
          ++ econstructor; [ econstructor | eassumption ].
          ++ econstructor; eassumption.
        * (* this is the other case where not all nodes lie in h.
             x is some node not in h. with that we can make sure that a header instance of h
             is on the path. this header has a pre-header from which we apply the ind. hypo. *)
          simpl_dec' Hnallinh.
          destruct Hnallinh as [x Hx].
          simpl_dec' Hx.
          destruct Hx as [Hxin Hxncont].
          destruct (in_fst Hxin) as [o Hxoin].
          eapply exit_edge_innermost in Hexit as Hinner.
          eapply path_from_elem in Hxoin.
          2: eauto.
          2: { rewrite app_comm_cons. eauto using path_rcons. }
          destruct Hxoin as [t [Ht Htpost]].
          eapply ex_entry_innermost in Hinner. 3,4:eauto.
          2: {
            eapply path_rcons in Hedge;eauto.
            eapply path_contains_back in Ht.
            eapply postfix_incl in Htpost. eapply Htpost in Ht.
            eapply path_to_elem in Ht;eauto.
            destructH.
            eapply tag_depth_unroot;eauto.
          }
          (* here we got the header *)

          eapply path_to_elem in Hinner as Hfrom; eauto.
          destruct Hfrom as [xh [Hxh Hxh_pre]].
          edestruct ex_pre_header as [preh [Hpreh_in [Hpreh_edge Hentry]]]; try eassumption.
          destruct Hexit. eauto using loop_contains_loop_head.

          (* Show that the pre-header is in the initial trace rb *)
          assert (Hpreinrb : (preh,tl m) ∈ ((b,m) :: rb)). {
            enough (Hpreinrbs : (preh, tl m) ∈ ((b,m) :: rb :r: (s,k))).
            - enough (Hpres : preh <> s).
              + rewrite app_comm_cons in Hpreinrbs. eapply in_app_or in Hpreinrbs. inv Hpreinrbs; try eassumption.
                inv H0; try easy. inv H1; try easy.
              + intro. subst preh. eapply Hndeq. enough (eq_loop q s).
                * symmetry in H0. eauto using eq_loop1, deq_loop_refl.
                * eauto using enter_exit_same.
            - eapply in_postfix_in. eapply in_prefix_in. eapply Hpreh_in. eassumption. eassumption.
          }
          (* remove intermediate results on x *)
          clear x o xh Hxin Hxncont Ht Hxh Hxh_pre Hpreh_in.

          (* the preheader is in the same loop as q. this is what we need. *)
          assert (Hpreeqq : eq_loop q preh) by (eauto using enter_exit_same).

          (* Now we can show that there is a strict prefix from u to the pre-header on which
             we can apply the induction hypothesis *)
          destruct (prefix_in_list Hpreinrb) as [pre Hpre].

          (* now we apply the induction hypothesis on the prefix path pre *)
          destruct (H pre) with (p := h) (q := preh) (i := (0 :: tl m)) (j := (tl m))
            as [e [h' [qe [toexit [fromexit [n' [m' [Hcons [Heq [Hcont [Hexit' [Hk [Htail [Hhd [Hfromexit Htoexit]]]]]]]]]]]]]]]; clear H.
          -- econstructor. eassumption.
          -- rewrite Hpreeqq in Hsinq. eapply Hsinq.
          -- intro. eapply Hndeq. eapply eq_loop1. symmetry in Hpreeqq. eassumption. eassumption.
          -- econstructor; [| eassumption ]. eapply path_prefix_path; try intros; eauto.
          -- intros y Hyin. rewrite <- Hpreeqq. eapply Hallin.
             rewrite map_cons. right. destruct (in_fst Hyin) as [v Hv]. replace y with (fst (y, v)) by eauto.
             eapply in_map. eapply in_prefix_in; eassumption.
          -- eapply prefix_eq in Hpre as Htmp.
             destruct Htmp as [rest Hrest].

             (* ok. here we have the following paths:
                (u,l) -toexit-> (e,m') -fromexit-> (preh,tl m) -rest-> (b,m)
                |<------r'-------->|<---------------r''-------------------->|
             *)
             exists e, h', qe, toexit, (rest ++ (preh, tl m) :: fromexit), n', m'.
             split. {
               rewrite <- app_assoc. rewrite <- app_comm_cons. unfold Tag. unfold Tag in Hcons. rewrite <- Hcons.
               eassumption.
             }
             split. { rewrite Heq. rewrite Hpreeqq. reflexivity. }
             do 3 (split; try eassumption).
             split; [ erewrite (tag_exit_eq Edge2); try eassumption |].
             split; [ eassumption |].
             split; [| eassumption ].

             decide (toexit = []).
             ++ subst toexit. rewrite app_nil_r in Hcons. subst pre.
                rewrite Hrest in Hpath. inv_path Htoexit.
                do 2 (econstructor; try eassumption).
             ++ rewrite Hcons in Hrest. rewrite app_comm_cons in Hrest. rewrite app_assoc in Hrest.
                rewrite Hrest in Hpath. eapply path_app_inv in Hpath.
                destruct Hpath as [_ [tgt [_ Hres]]].
                2,3: intros; eauto.
                2: { intro. symmetry in H. eapply app_cons_not_nil. eassumption. }
                destruct tgt as [_e _m'].
                do 2 (econstructor; try eassumption).
                eapply path_back' in Hres as Htmp. eapply path_back' in Hfromexit.
                rewrite hd_rev_app_eq with (d := (p,i)) in Htmp.
                rewrite hd_rev_cons_eq with (d := (p,i)) in Hfromexit.
                unfold Tag in Htmp, Hfromexit. rewrite <- Htmp in Hfromexit.
                inv Hfromexit. eassumption.
  Qed.

  Lemma split_DiamondPaths s u1 u2 p1 p2 q1 q2 k i l1 l2 j1 j2 r1 r2
       (Hndeq : ~ deq_loop q1 s)
       (Htagle : j1 ⊴ j2)
       (D : DiamondPaths s u1 u2 p1 p2 q1 q2 k i l1 l2 j1 j2 ((q1,j1) :: r1) ((q2,j2) :: r2))
   : exists r1' r2' r1'' r2'' e1 e2 n1 n2 q1' q2',
     r1 = r1'' ++ r1'
     /\ r2 = r2'' ++ r2'
     /\ DiamondPaths s u1 u2 e1 e2 q1' q2' k j1 l1 l2 (n1 :: j1) (n2 :: j1) r1'  r2'
     /\ TeqPaths e1 e2 q1 q2 j1 j1 j1 j2 r1'' r2''
     /\ eexit_edge q1' e1
     /\ eexit_edge q2' e2.
 Proof.
   destruct (find_last_exit Dsk1 Dlen Dpath1 (s_deq_q D) Hndeq) as [e1 [h1 [qe1 [r1' [r1'' [n1 [m1 P1]]]]]]].
   1: {eapply DiamondPaths_sym in D. intros. rewrite <- Dloop. eapply r2_incl_head_q; eassumption. }
   edestruct (find_last_exit Dsk2 Dlen Dpath2) as [e2 [h2 [qe2 [r2' [r2'' [n2 [m2 P2]]]]]]].
   1: { eapply DiamondPaths_sym in D. eauto using s_deq_q. }
   1: { intro. eapply Hndeq. specialize Dloop. intros Dloop. symmetry in Dloop. eauto using eq_loop1. }
   1: { intros. rewrite <- Dloop. eapply r2_incl_head_q; eassumption. }

   destruct P1 as [Hconc1 [Heq1 [Hcont1 [Hexit1 [Htag1 [Htl1 [Hhd1 [Hp1 Hp1']]]]]]]].
   destruct P2 as [Hconc2 [Heq2 [Hcont2 [Hexit2 [Htag2 [Htl2 [Hhd2 [Hp2 Hp2']]]]]]]].

   assert (Heq : eq_loop e1 e2). {
     rewrite Heq1. rewrite Heq2. eapply Dloop.
   }

   replace h2 with h1 in *.
   2: {
     enough (eq_loop qe1 qe2).
     - eauto using innermost_unique', exit_edge_innermost.
     - eauto using exit_edges_loop_eq.
   }

   assert (Edge1 : (q1, j1) -t> (p1, i)). {
     inv Hp1. eapply path_front in H0. subst b. assumption.
   }
   assert (Edge2 : (q2, j2) -t> (p2, i)). {
     inv Hp2. eapply path_front in H0. subst b. assumption.
   }

   replace m2 with m1 in *.
   - replace j1 with m1 in *.
     + exists r1', r2', r1'', r2'', e1, e2, n1, n2, qe1, qe2.
       do 2 (split; [ firstorder |]).

       (* Diamond Paths *)
       split. {
         destruct D.
         econstructor; try eassumption.
         - unfold Disjoint in *. intro. intros. intro. eapply Ddisj.
           rewrite Hconc1. eapply in_cons. eauto using in_or_app.
           rewrite Hconc2. eauto using in_cons, in_or_app.
         - rewrite <- Heq1 in Dloop. rewrite <- Heq2 in Dloop.
           eauto using exit_edges_loop_eq.
       }

       (* TeqPaths *)
       split. {
         econstructor; try eauto.
         - inv Hp1. unfold TPath. eapply path_front in H0 as H0'. subst. eassumption.
         - inv Hp2. unfold TPath. eapply path_front in H0 as H0'. subst. eassumption.
         - unfold Disjoint in *. intros. intro. eapply Ddisj.
           + rewrite Hconc1. rewrite app_comm_cons. eauto using in_or_app.
           + rewrite Hconc2. rewrite app_comm_cons. eauto using in_or_app.
         - rewrite <- Heq1. rewrite <- Heq2. eassumption.
         - erewrite j_len1, j_len2; try eassumption.
           rewrite <- Heq1, <- Heq2. eauto using eq_loop_depth.
         - eauto using j_len1.
       }

       split; exists h1; eauto.
     + clear Htag1 Htag2.
       inv_path Hp1. inv H; [ reflexivity |].
       assert (e_len1 : | m1 | = depth e1).
       {
         eapply tag_depth_unroot;eauto. eapply u_len1. eauto.
       }
       destruct (ex_innermost_loop q1) as [Hqinner | Hnqinner].
       * destruct Hqinner as [h' Hqinner']. simpl in Hqinner'.
         rewrite <- (@take_r_innermost q1 j1 h' Hqinner' (j_len1 D)).
         rewrite <- (@take_r_innermost e1 m1 h'); [ | rewrite Heq1 | ]; try eassumption.
         assert (Hdeq_q1h' : deq_loop q1 h'). { destruct Hqinner'. eauto using loop_contains_deq_loop. }
         assert (Hdeq_sh' : deq_loop s h'). {
           eapply deq_loop_trans. eapply s_deq_q. eassumption. eapply loop_contains_deq_loop.
           destruct Hqinner'. eassumption.
         }
         eapply innermost_eq_loop in Hqinner'. rewrite Hqinner'.
         setoid_rewrite take_r_geq at 2.
         2: { erewrite j_len1;eauto. }
         eapply tag_eq1;eauto.
         right. rewrite map_app. eapply in_or_app. left. eapply path_contains_back in H2.
         eapply in_map with (f:=snd) in H2. cbn in H2. eassumption.
       * simpl in Hnqinner.
         enough (Hdepq : depth q1 = 0).
         -- assert (Hdepe : depth e1 = 0). { rewrite Heq1. eassumption. }
            rewrite <- (j_len1 D) in Hdepq. rewrite <- e_len1 in Hdepe.
            destruct j1, m1; try inv Hdepq; try inv Hdepe. reflexivity.
         -- eapply depth_zero_iff. intros. eapply loop_contains_innermost in H.
            destruct H as [h' Hinner']. eapply (Hnqinner h'). eassumption.
   - rewrite Htag1 in Htag2. eassumption.
 Qed.

 Lemma inhom_loop_exits_step_lt
       (s u1 u2 q1 q2 e1 e2 : Lab)
       (k l1 l2 i : Tag)
       (m n1 n2 : nat)
       (IHm : forall (q1 q2 e1 e2 : Lab) (r1 r2 : list (Lab * Tag)) (n1 n2 : nat) (i : Tag),
           DiamondPaths s u1 u2 e1 e2 q1 q2 k i l1 l2 (n1 :: i) (n2 :: i) r1 r2 ->
           m = depth s - depth q1 ->
           exists r1' r2' : list Lab,
             HPath u1 e1 (e1 :: r1') /\
             HPath u2 e2 (e2 :: r2') /\ Disjoint r1' r2' /\ r1' <<= map fst r1 /\ r2' <<= map fst r2)
       (r1 r2 : list (Lab * Tag))
       (D : DiamondPaths s u1 u2 e1 e2 q1 q2 k i l1 l2 (n1 :: i) (n2 :: i) ((q1, n1 :: i) :: r1)
                         ((q2, n2 :: i) :: r2))
       (Heqm : S m = depth s - depth q1)
       (Hqs : ~ deq_loop q1 s)
       (Hlt : n1 < n2)
   : exists r1' r2' : list Lab,
     HPath u1 e1 (e1 :: r1') /\
     HPath u2 e2 (e2 :: r2') /\
     Disjoint r1' r2' /\
     r1' <<= map fst ((q1, n1 :: i) :: r1) /\ r2' <<= map fst ((q2, n2 :: i) :: r2).
 Proof.
   eapply split_DiamondPaths in D as Dsplit;eauto.
   2: { eapply le_cons_tagle. lia. }
   destructH.
   subst r1 r2.
   eapply IHm in Dsplit1 as Hinhom.
   2: {
     enough (depth q1' = S (depth q1)).
     - clear - Heqm H.
       rewrite H. lia.
     - copy Dsplit4 Hexit.
       eapply depth_exit in Dsplit4. rewrite Dsplit4. f_equal. eapply eq_loop_depth.
       destruct Hexit.
       eapply u1_exit_eq_q;eauto.
   }
   destructH.
   assert ((q1, n1 :: i) -t> (e1, i)) as Hedge1.
   { destruct D. inv_path Dpath1;eauto. }
   assert ((q2, n2 :: i) -t> (e2, i)) as Hedge2.
   { destruct D. inv_path Dpath2;eauto. }
   eapply teq_node_disj_prefix_hpath in Dsplit3 as Dinst;eauto.
   destructH.
   exists (r1'1 ++ tl (e0 :: r1'0)), (r2'1 ++ tl (e3 :: r2'0)).
   split_conj.
   - rewrite app_comm_cons. eapply path_app';eauto.
   - rewrite app_comm_cons. eapply path_app';eauto.
   - cbn.
      eapply disjoint_app_app;eauto.
     + intros x Hx.
       intro N.
       destruct Dsplit4.
       destruct r1'1;[contradiction|].
       inv_path Dinst0.
       eapply head_rewired_final_exit_elem;eauto.
       eapply r2_incl_head_q;eauto.
       eapply exit_edge_innermost in H. destruct H. auto.
     + eapply Disjoint_sym.
       intros x Hx.
       intro N.
       destruct Dsplit6.
       destruct r2'1;[contradiction|].
       inv_path Dinst2.
       eapply head_rewired_final_exit_elem;eauto.
       eapply r1_incl_head_q;eauto.
       eapply exit_edge_innermost in H. rewrite <-Dloop in H. destruct H. auto.
   - cbn. rewrite map_app. rewrite app_comm_cons.
     eapply incl_app_app;eauto.
   - cbn. rewrite map_app. rewrite app_comm_cons.
     eapply incl_app_app;eauto.
 Qed.

 Lemma inhom_loop_exits (s u1 u2 q1 q2 e1 e2 : Lab) r1 r2 (k i l1 l2 : Tag) (n1 n2 : nat)
        (D : DiamondPaths s u1 u2 e1 e2 q1 q2 k i l1 l2 (n1 :: i) (n2 :: i) r1 r2)
    : exists r1' r2', HPath u1 e1 (e1 :: r1') /\ HPath u2 e2 (e2 :: r2')
                 /\ Disjoint r1' r2'
                 /\ r1' ⊆ map fst r1 /\ r2' ⊆ map fst r2.
 Proof.
   remember (depth s - depth q1) as m.
   revert q1 q2 e1 e2 r1 r2 n1 n2 i D Heqm.
   induction m;intros.
   - assert (depth s = depth q1) as Hseqq.
     {
       enough(depth q1 <= depth s);[lia|].
       eapply deq_loop_depth. eauto using s_deq_q.
     }
     assert (deq_loop q1 s) as Hdeq.
     { eapply deq_loop_depth_eq;eauto using s_deq_q. }
     specialize (Nat.lt_trichotomy n1 n2) as Htri. destruct Htri as [Hlt|[Heq|Hlt]];cycle 1.
     + subst n2. eapply node_disj_hpath in D as Hndisj;eauto.
     + eapply DiamondPaths_sym in D.
       eapply node_disj_prefix_hpath in D as Hndisj;eauto.
       2: eapply eq_loop1;eauto;symmetry; eauto using Dloop.
       destructH.
       exists r2', r1'.
       split_conj;eauto.
       eapply Disjoint_sym;eauto.
     + eapply node_disj_prefix_hpath in D as Hndisj;eauto.
   - destruct r1,r2. (* all nil cases can be contradicted *)
     1-3: exfalso;destruct D; cbn in Dqj1,Dqj2.
     1,2: inv Dqj1. 1,3: inv Dqj2.
     1-3: tryif lia then idtac else rewrite Dloop in Heqm;lia.
     diamond_subst_qj D.
     assert (~ deq_loop q1 s) as Hqs.
     { intro N. eapply deq_loop_depth in N. lia. }
     specialize (Nat.lt_trichotomy n1 n2) as [Hlt|[Hlt|Hlt]].
     + eapply inhom_loop_exits_step_lt;eauto.
     + eapply split_DiamondPaths in D as Dsplit;eauto.
       2: { eapply le_cons_tagle. lia. }
       destructH.
       subst r1 r2 n2.
       eapply IHm in Dsplit1 as Hinhom.
       2: {
         enough (depth q1' = S (depth q1)).
         - clear - Heqm H.
           rewrite H. lia.
         - copy Dsplit4 Hexit.
           eapply depth_exit in Dsplit4. rewrite Dsplit4. f_equal. eapply eq_loop_depth.
           destruct Hexit.
           eapply u1_exit_eq_q;eauto.
       }
       destructH.
       assert ((q1, n1 :: i) -t> (e1, i)) as Hedge1.
       { destruct D. inv_path Dpath1;eauto. }
       assert ((q2, n1 :: i) -t> (e2, i)) as Hedge2.
       { destruct D. inv_path Dpath2;eauto. }
       eapply teq_node_disj_hpath in Dsplit3 as Dinst;eauto.
       destructH.
       exists ((q1 :: r1'1) ++ tl (e0 :: r1'0)), ((q2 :: r2'1) ++ tl (e3 :: r2'0)).
       split_conj.
       -- rewrite app_comm_cons. eapply path_app';eauto.
       -- rewrite app_comm_cons. eapply path_app';eauto.
       -- cbn.
          do 2 rewrite app_comm_cons.
          eapply disjoint_app_app;eauto.
          ++ intros x Hx.
             intro N.
             destruct Dsplit4.
             inv_path Dinst0.
             eapply head_rewired_final_exit_elem;eauto.
             eapply r2_incl_head_q;eauto.
             eapply exit_edge_innermost in H. destruct H. auto.
          ++ eapply Disjoint_sym.
             intros x Hx.
             intro N.
             destruct Dsplit6.
             inv_path Dinst2.
             eapply head_rewired_final_exit_elem;eauto.
             eapply r1_incl_head_q;eauto.
             eapply exit_edge_innermost in H. rewrite <-Dloop in H. destruct H. auto.
       -- cbn. rewrite map_app. rewrite app_comm_cons.
      rewrite app_comm_cons. eapply incl_app_app;eauto.
   -- cbn. rewrite map_app. rewrite app_comm_cons.
      rewrite app_comm_cons. eapply incl_app_app;eauto.
     + copy D D'.
       eapply DiamondPaths_sym in D.
       eapply inhom_loop_exits_step_lt in D.
       * destructH. repeat eexists;eauto. eapply Disjoint_sym;eauto.
       * intros.
         enough (exists r2' r1' : list Lab,
                    HPath u1 e3 (e3 :: r2')
                    /\ HPath u2 e0 (e0 :: r1')
                    /\ Disjoint r2' r1'
                    /\ r2' <<= map fst r3
                    /\ r1' <<= map fst r0).
         { clear - H1. firstorder. }
         eapply IHm.
         -- eapply DiamondPaths_sym. exact H.
         -- destruct H. rewrite <-Dloop. eauto.
       * rewrite <-Dloop. eauto.
       * intro N. eapply eq_loop1 in N;[eauto|symmetry;eauto]. eapply Dloop.
       * eauto.
 Qed.


  Lemma contract_one_empty s u2 p i q2 r2 k l2
        (Hin2 : Path tcfg_edge (u2, l2) (p, i) ((p, i) :: (q2, k) :: r2))
        (Hin4 : (s, k) -t> (u2, l2))
        (Hqp1 : (s, k) -t> (p, i))
        (D : DiamondPaths s p u2 p p s q2 k i i l2 k k [] ((q2, k) :: r2))
    : exists (π ϕ : list Lab) (u u' : Lab),
      HPath u p π /\
      HPath u' p ϕ /\ Disjoint (tl π) (tl ϕ) /\ s --> u /\ s --> u' /\ (tl π <> [] \/ tl ϕ <> []).
  Proof.
    eapply TPath_CPath in Hin2. cbn in Hin2. inv_path Hin2.
    eapply contract_cpath' in H.
    - cbn in Hin2. destructH.
      exists (p :: ϕ), [p], u2, p.
      split_conj.
      + econstructor;eauto. unfold head_rewired_edge. left;split;eauto.
        intros N. eapply no_back2;eauto. cbn. left; eauto.
        rewrite Dloop. eapply loop_contains_self;eauto.
      + econstructor.
      + cbn. unfold Disjoint. firstorder.
      + destruct Hin4;eauto.
      + destruct Hqp1;eauto.
      + cbn. left. inv_path H1; congruence.
    - cbn. rewrite <-Dloop. eapply u2_deq_q; eauto. congruence.
    - cbn. intros. rewrite <-Dloop. eapply no_back2;eauto.
      right. cbn. auto.
  Qed.

  Theorem splits_sound p
    : splitsT p ⊆ splits p.
  Proof.
    intros s Hin.
    eapply splitsT_spec in Hin.
    destructH.
    (* contradict π and ϕ (the paths from (u,l) to (p,i)) being empty *)
    destruct π as [|pi1 r1]; destruct ϕ as [|pi2 r2]; cbn in Hin1, Hin5.
    1: tauto.
    1: inversion Hin0.
    1: inversion Hin2.
    unfold TPath in Hin0. path_simpl' Hin0.
    unfold TPath in Hin2. path_simpl' Hin2.
    eapply edge_path_hd_edge in Hin0 as Hqp1;eauto.
    eapply edge_path_hd_edge in Hin2 as Hqp2;eauto.
    rewrite hd_map_fst_snd in Hqp1, Hqp2.
    set (q1 := hd s (map fst r1)) in *.
    set (q2 := hd s (map fst r2)) in *.
    set (j1 := hd k (map snd r1)) in *.
    set (j2 := hd k (map snd r2)) in *.
    specialize (two_edge_exit_cases) with (q1:=q1) (q2:=q2) (p:=p) as Hcase.
    exploit Hcase.
    1: eapply TPath_CPath in Hin0.
    2: eapply TPath_CPath in Hin2.
    1,2: cbn in Hin0,Hin2.
    1: eapply edge_path_hd_edge in Hin0;subst q1;eauto.
    2: eapply edge_path_hd_edge in Hin2;subst q2;eauto.
    1,2: destruct Hin3,Hin4;eauto.
    eassert (DiamondPaths s u1 u2 p p q1 q2 k i l1 l2 j1 j2 (r1) (r2)) as D.
    {
      econstructor. 3: eapply Hin0. 3: eapply Hin2.
      all:cbn;eauto.
      1,2: subst q1 q2 j1 j2;eapply hd_map_fst_snd.
      destruct Hcase.
      - destructH. eapply eq_loop_exiting in H0. eapply eq_loop_exiting in H1.
        rewrite <-H0. rewrite <-H1. reflexivity.
      - destructH.
        eapply nexit_injective in H0;eauto. subst j1 j2.
        eapply tcfg_edge_eq_loop;eauto. rewrite <-H0. eauto.
    }
    destruct Hcase.
    - destructH.
      eapply tag_exit_eq' in H0 as Hn1;eauto. destruct Hn1 as [n1 Hn1].
      eapply tag_exit_eq' in H1 as Hn2;eauto. destruct Hn2 as [n2 Hn2].
      subst j1 j2. rewrite Hn1 in D. rewrite Hn2 in D.
      eapply inhom_loop_exits in D as Hinhom.
      destructH.
      eapply splits_spec.
      exists (p :: r1'), (p :: r2'), u1, u2.
      split_conj;eauto;cbn.
      1,2: destruct Hin3,Hin4;eauto.
      destruct r1';[|left;congruence].
      destruct r2';[|right;congruence].
      exfalso.
      eapply path_single in Hinhom0. destruct Hinhom0 as [Hinhom0 _]. subst u1.
      eapply path_single in Hinhom2. destruct Hinhom2 as [Hinhom2 _]. subst u2.
      eapply tcfg_edge_det in Hin3;eauto. subst l2.
      inv_path Hin0; inv_path Hin2.
      + tauto.
      + subst q1. destruct r2;[inv H|].
        eapply tcfg_fresh in Hin2.
        3:cbn;lia.
        2:eapply i_len1;eauto.
        eapply Taglt_irrefl;eassumption.
      + subst q2. destruct r1;[inv H|].
        eapply tcfg_fresh in Hin0.
        3:cbn;lia.
        2:eapply i_len1;eauto.
        eapply Taglt_irrefl;eassumption.
      + eapply Hin1.
        1,2: eapply path_contains_back;eauto.
    - destructH.
      subst q1 q2 j1 j2.
      eapply nexit_injective in H0;eauto.
      rewrite <-hd_map_fst_snd in Hqp1,Hqp2.
      destruct r1 as [|[q1 j1] r1]; destruct r2 as [|[q2 j2] r2];
        unfold hd in Hqp1,Hqp2.
      + tauto.
      + cbn in D,H0. subst j2.
        eapply splits_spec. eapply path_single in Hin0. destruct Hin0. inversion H. subst.
        clear H0 H1 Hin1 Hin3 Hin5 H. clear Hqp2.
        eapply contract_one_empty;eauto.
      + eapply DiamondPaths_sym in D.
        cbn in D,H0. subst j1.
        eapply splits_spec. eapply path_single in Hin2. destruct Hin2. inversion H. subst.
        eapply contract_one_empty;eauto.
      + cbn in H0. subst j2.
        decide (deq_loop q1 s).
        * eapply (diamond_teq) in D as T;eauto. 2: reflexivity.
          eapply teq_node_disj_hpath in T as Hdisj;eauto.
          destructH.
          eapply splits_spec.
          repeat eexists;split_conj.
          1: eapply Hdisj0. 1: eapply Hdisj2.
          all: cbn;eauto.
          1,2: destruct Hin3,Hin4;eauto.
          left. congruence.
        * eapply split_DiamondPaths in D;eauto. 2: reflexivity.
          destructH. subst r1 r2.
          eapply inhom_loop_exits in D1 as Hinhom.
          eapply splits_spec.
          destructH.
          eapply teq_node_disj_hpath in D3 as Dinst;eauto.
          destructH.
          exists ((p :: q1 :: r1'1) ++ tl (e1 :: r1'0)), ((p :: q2 :: r2'1) ++ tl (e2 :: r2'0)), u1, u2.
          split_conj. 4,5: destruct Hin3,Hin4;eauto.
          -- eapply path_app';eauto.
          -- eapply path_app';eauto.
          -- cbn.
             do 2 rewrite app_comm_cons.
             eapply disjoint_app_app;eauto.
             ++ intros x Hx.
                intro N.
                destruct D4.
                inv_path Dinst0.
                eapply head_rewired_final_exit_elem.
                1: eapply H0.
                1,2: eauto.
                eapply r2_incl_head_q;eauto.
                eapply exit_edge_innermost in H. destruct H. auto.
             ++ eapply Disjoint_sym.
                intros x Hx.
                intro N.
                destruct D6.
                inv_path Dinst2.
                eapply head_rewired_final_exit_elem;eauto.
                eapply r1_incl_head_q;eauto.
                eapply exit_edge_innermost in H. rewrite <-Dloop in H. destruct H. auto.
          -- cbn. left. congruence.
  Qed.

End splits_sound.
