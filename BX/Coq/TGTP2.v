From bx_plugin.Coq Require Export TGTP.
Require Import Lia.


Lemma TgetTputPIandPT_VD : [PI &&& PT ===>pg VD].
Proof.
  move => S V l hs hv gt pt PI PT s s' s'' v v' [H1 H2];
  apply (PI s'' s'' v v');
  firstorder.
Qed.

Lemma TgetTputSGPandPI_PP : [SGP &&& PI ===>pg PP].
Proof.
  move => S V l hs hv gt pt HSGP HPI s s' s'' v v' [H1 H2].
  unfold GetTotal in gt.
  unfold PutTotal in pt.
  unfold SGP in HSGP.
  unfold PI in HPI.
  case (p_get hv s'') eqn:Hp.
  apply HSGP.
  apply (HSGP s' s'' v0 ) in Hp as Hp2.
  assert (He : v' = v0).
  apply (HPI s' s'' v' v0). split. auto. auto.
  rewrite He. apply Hp.
  firstorder.
Qed.

Lemma TgetTputSGPandGS_PG : [SGP &&& GS ===>pg PG].
Proof.
  move => S V hs hv l gt pt SGP GS s s' v H;
  case (GS v) => [s'' H1];
  apply (SGP s s'' v) in H1 as H2;
  rewrite H in H2;
  inversion H2;
  firstorder.
Qed.

Lemma TgetTputSGPandGS_PP : [SGP &&& GS ===>pg PP].
Proof.
  move => S V hs hv l gt pt  HSGP HGS s s' s'' v v' [H1 H2];
  case (HGS v') => [s''' H3].
  apply (HSGP s' s''' v') in H3 as H4;
  rewrite H2 in H4; inversion H4;
  apply HSGP; firstorder.
Qed.

Lemma TgetTputWSSandVD_PT : [WSS &&& VD ===>pg PT].
Proof.
  move => S V hs hv l gt pt  WSS VD s s' v H;
  case (WSS s' s v) => [v' H1];
  move :(H1 H) => H2;
  have H3 : v = v';
  move : (VD s s' s' v v');
  firstorder;
  rewrite H3;
  apply H2.
Qed.

Lemma TgetTputPGPandPP_WPG : [PGP &&& PP ===>pg WPG].
Proof.
  move => S V hs hv l gt pt PGP PP s s' v v' [H1 H2];
  apply (PP s s' s' v v');
  split;
  firstorder;
  apply (PGP s s' v v');
  firstorder.
Qed.

Lemma TgetTputPGPandPG_PT : [PGP &&& PG ===>pg PT].
Proof.
  move => S V hs hv l gt pt PGP PG s s' v H1;
  apply PG in H1 as H2;
  move : (PGP s s' v v) => H3;
  have H4 := H3 (conj H1 H2);
  apply H4.
Qed.

Lemma TgetTputPGPandVD_PG : [PGP &&& VD ===>pg PG].
Proof.
  move => S V hs hv l gt pt PGP VD s s' v H;
  case (p_get l s') eqn:H1.
  have H2 := (PGP s s' v v0) (conj H H1);
  have H3 := (VD s s' s' v v0) (conj H H2);
  rewrite H3; reflexivity.
  exfalso; apply (gt s'); firstorder.
Qed.

Lemma TgetTputGPandPP_UD : [GP &&& PP ===>pg UD].
Proof.
  move => S V hs hv l gt pt HGP HPP s s' v v' [H1 H2];
  apply HGP in H2.
  case (p_put l (s',v')) eqn:H3.
  have H4 := (HPP s s' s0 v v') (conj H1 H3).
  rewrite H2 in H4. firstorder.
  firstorder.
Qed.

Lemma TgetTputPGandGI_SGP : [PG &&& GI ===>pg SGP].
Proof.
  move => S V hs hv l gt pt HPG HGI s s' v H;
  case (p_put l (s,v)) eqn : H1.
  have H2 := (HGI s0 s' v). unfold PG in HPG.
  apply (HPG s s0 v) in H1. firstorder. rewrite H0. reflexivity.
  exfalso; apply (pt s v); firstorder.
Qed.

Lemma TgetTputUDandVD_WPG : [UD &&& VD ===>pg WPG].
Proof.
  move => S V hs hv l gt PT HUD HVD s s' v v' [H1 H2];
  case (p_put l (s',v')) eqn:Hp.
  move : (HUD s' s0 v' v') => H3;
  have H4 := H3 (conj Hp H2).
  move : (HVD s s0 s' v v') => H5;
  have H6 := H5 (conj H1 H4).
  rewrite <- H6; apply H1.
  firstorder.
Qed.

Lemma TgetTputUDandPP_PT : [UD &&& PP ===>pg PT].
Proof.
  move => S V hs hv l gt TG HUD HPP s s' v H.
  case (p_get l s) eqn:Hp.
  move : (HUD s s' v v0) => H1;
  have H2 := H1 (conj H Hp);
  apply (HPP s' s s' v0 v);
  firstorder. firstorder.
Qed.

Lemma TgetTputGPG_GI_GS_PP_notSGP : ~[GPG &&& GI &&& GS &&& PP ===>pg SGP].
Proof.
  move => H.
  bx_test[tg;tp;gpg;gi;gs;pp;notsgp].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gpg. by move => [] [] [];firstorder.
  have_gi. by move => [] [] [];firstorder.
  have_gs. rewrite / GS;case => /=. exists true;firstorder. exists false;firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notsgp. unfold SGP. 
  by move => HW;move : (HW false true true erefl).
  apply HnotSGP. apply H. firstorder. firstorder. apply HTG. apply HTP. 
  apply HGPG. apply HGI. apply HGS. apply HPP.
Qed.

Lemma TgetTputPG_PP_notPS : ~[PG &&& PP ===>pg PS].
Proof.
  move => H.
  bx_test[tg;tp;pg;pp;notps].
  have_tg. by move => [].
  have_tp. by move => [] [].  have_pg. by move => [] [] [].  have_pp. by move => [] [] [] [] [];firstorder.
  have_notps. unfold PS.
  by move => HW;move:(HW aa) => [s' [v HJ]];case s',v.
  apply HnotPS. apply H. firstorder. firstorder. apply HTG. apply HTP.
  apply HPG. apply HPP.
Qed.

Lemma TgetTputGI_PI_GS_PP_notPS : ~[GI &&& PI &&& GS &&& PP ===>pg PS].
Proof.
  move => H. set(Ss := nat); set(Vv := nat).
  set (l :=
  @mkLens nat nat
  (fun n => Some n)
  (fun '(s,v) => Some (S v))).  
  have HPS : GetTotal Ss Vv l -> PutTotal Ss Vv l -> GI Ss Vv l -> PI Ss Vv l -> GS Ss Vv l -> PP Ss Vv l -> PS Ss Vv l := H Ss Vv _ _ l.
  have HTG : GetTotal Ss Vv l. by move => [].
  have HTP : PutTotal Ss Vv l. by move => [] [].
  have HGI : GI Ss Vv l. move => s s' v [H1 H2].
  injection H1. move => e1.
  injection H2. move => e2. rewrite e1; rewrite <- e2; reflexivity.  
  have HPI : PI Ss Vv l. move => s s' v v' [H1 H2].
  injection H1. move => e1.
  injection H2. move => e2. rewrite <- e1 in e2. injection e2. move => e3. firstorder.
  have HGS : GS Ss Vv l. unfold GS.  move => v. exists v. reflexivity.
  have HPP : PP Ss Vv l. move => s s' s'' v v' [H1 H2].
  injection H1. move => e1.
  injection H2. move => e2. rewrite <- e2. reflexivity.
  have HnotPS : ~ PS Ss Vv l. unfold PS.
  move => HW. destruct (HW 0) as [s' [v Heq]]. discriminate.
  apply HnotPS. apply H. apply (inhabited_nat). apply (inhabited_nat). apply HTG. apply HTP.
  apply HGI. apply HPI. apply HGS. apply HPP.
Qed.

Lemma TgetTputPGP_GI_GS_PP_notPS : ~[PGP &&& GI &&& GS &&& PP ===>pg PS].
Proof.
  move => H. set(Ss := nat); set(Vv := nat).
  set (l :=
  @mkLens nat nat
  (fun n => Some n)
  (fun '(s,v) => Some 0)).
  have HPS : GetTotal Ss Vv l -> PutTotal Ss Vv l -> PGP Ss Vv l -> GI Ss Vv l -> GS Ss Vv l -> PP Ss Vv l -> PS Ss Vv l := H Ss Vv _ _ l.
  have HTG : GetTotal Ss Vv l. by move => [].
  have HTP : PutTotal Ss Vv l. by move => [] [].
  have HGI : GI Ss Vv l. move => s s' v [H1 H2].
  injection H1. move => e1.
  injection H2. move => e2. rewrite e1; rewrite <- e2; reflexivity.  
  have HPGP : PGP Ss Vv l. move => s s' v v' [H1 H2].
  injection H1. move => e1.
  injection H2. move => e2. rewrite <- e1. reflexivity.  
  have HGS : GS Ss Vv l. unfold GS.  move => v. exists v. reflexivity.
  have HPP : PP Ss Vv l. move => s s' s'' v v' [H1 H2].
  injection H1. move => e1.
  injection H2. move => e2. rewrite <- e2. reflexivity.
  have HnotPS : ~ PS Ss Vv l. unfold PS.
  move => HW. destruct (HW 1) as [s' [v Heq]]. discriminate.  
  apply HnotPS. apply H. apply (inhabited_nat). apply (inhabited_nat). apply HTG. apply HTP.
  apply HPGP. apply HGI. apply HGS. apply HPP.
Qed.

Lemma TgetTputPS_PG_PT_notUD : ~[PS &&& PG &&& PT ===>pg UD].
Proof.
  move => H.
  bx_test[tg;tp;ps;pg;pt;notud].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_ps. move => s. case s. exists (aa);exists (false); reflexivity.
  exists (aa);exists(true);reflexivity. exists(bb);exists(false);reflexivity.
  have_pg. by move => [] [] [].
  have_pt. by move => [] [] [];firstorder.
  have_notud. unfold UD.
  by move => HW; move : (HW aa bb true false (conj erefl erefl)).
  apply HnotUD. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HPS. apply HPG. apply HPT.
Qed.

Lemma TgetTputWPG_GPG_GI_GS_PT_notUD : ~[WPG &&& GPG &&& GI &&& GS &&& PT ===>pg UD].
Proof.
  move => H.
  bx_test[tg;tp;wpg;gpg;gi;gs;pt;notud].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_wpg. by move => [] [] [] [];firstorder.
  have_gpg. by move => [] [] [];firstorder.
  have_gi. by move => [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder. exists false;firstorder.
  have_pt. by move => [] [] [];firstorder.
  have_notud. unfold UD.
  by move => HW; move : (HW false true true false (conj erefl erefl)).
  apply HnotUD. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HWPG. apply HGPG. apply HGI. apply HGS. apply HPT.
Qed.

Lemma TgetTputGPG_GI_GS_PT_notWPG : ~[GPG &&& GI &&& GS &&& PT ===>pg WPG].
Proof.
  move => H.
  bx_test[tg;tp;gpg;gi;gs;pt;notwpg].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gpg. by move => [] [] [];firstorder.
  have_gi. by move => [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists bb; firstorder. exists aa;firstorder. exists cc;firstorder.
  have_pt. by move => [] [] [].
  have_notwpg. unfold WPG.
  by move => HW; move : (HW aa bb cc aa (conj erefl erefl)).
  apply HnotWPG. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HGPG. apply HGI. apply HGS. apply HPT.
Qed.

Lemma TgetTputGPG_GI_PI_GS_notWPG : ~[GPG &&& GI &&& PI &&& GS ===>pg WPG].
Proof.
  move => H.
  bx_test[tg;tp;gpg;gi;pi;gs;notwpg].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gpg. by move => [] [] [];firstorder.
  have_gi. by move => [] [] [];firstorder.
  have_pi. by move => [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists cc; firstorder.  exists bb;firstorder. exists aa;firstorder.
  have_notwpg. unfold WPG.
  by move => HW; move : (HW bb aa aa cc(conj erefl erefl)).
  apply HnotWPG. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HGPG. apply HGI. apply HPI. apply HGS.
Qed.

Lemma TgetTputPS_GI_PI_GS_PP_notWPG : ~[PS &&& GI &&& PI &&& GS &&& PP ===>pg WPG].
Proof.
  move => H.
  bx_test[tg;tp;ps;gi;pi;gs;pp;notwpg].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_ps. move => s. case s. exists (false);exists(true);reflexivity.
  exists(true);exists(false);reflexivity.
  have_gi. by move => [] [] [];firstorder.
  have_pi. by move => [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists false; firstorder.  exists true;firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notwpg. unfold WPG.
  by move => HW; move : (HW true true true false (conj erefl erefl)).
  apply HnotWPG. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HPS. apply HGI. apply HPI. apply HGS. apply HPP.
Qed.

Lemma TgetTputPS_GPG_PI_GS_PP_notWPG : ~[PS &&& GPG &&& PI &&& GS &&& PP ===>pg WPG].
Proof.
  move => H.
  bx_test[tg;tp;ps;gpg;pi;gs;pp;notwpg].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_ps. move => s. case s.  exists (AA);exists(true);reflexivity. exists(AA);exists(false);reflexivity.
exists(CC);exists(true);reflexivity. exists(CC);exists(false);reflexivity.
  have_gpg. by move => [] [] [];firstorder.
  have_pi. by move => [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists AA; firstorder.  exists DD;firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notwpg. unfold WPG.
  by move => HW; move : (HW BB BB false true (conj erefl erefl)).
  apply HnotWPG. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HPS. apply HGPG. apply HPI. apply HGS. apply HPP.
Qed.

Lemma TgetTputUD_GI_GS_notGPG : ~[UD &&& GI &&& GS ===>pg GPG].
Proof.
  move => H.
  bx_test[tg;tp;ud;gi;gs;notgpg].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_ud. by move => [] [] [] [];firstorder.
  have_gi. by move => [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists false; firstorder.  exists true;firstorder.
  have_notgpg. unfold GPG.
  by move => HW; move : (HW false true true (conj erefl erefl)).
  apply HnotGPG. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HUD. apply HGI. apply HGS.
Qed.

Lemma TgetTputPGP_GI_GS_PP_notGPG : ~[PGP &&& GI &&& GS &&& PP ===>pg GPG].
Proof.
  move => H.
  bx_test[tg;tp;pgp;gi;gs;pp;notgpg].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_pgp. by move => [] [] [] [];firstorder.
  have_gi. by move => [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notgpg. unfold GPG.
  by move => HW; move : (HW false true false (conj erefl erefl)).
  apply HnotGPG. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HPGP. apply HGI. apply HGS. apply HPP.
Qed.

Lemma TgetTputPGP_GI_PI_GS_notGPG : ~[PGP &&& GI &&& PI &&& GS ===>pg GPG].
Proof.
  move => H. set(Ss := nat); set(Vv := nat).
  set (l :=
  @mkLens nat nat
  (fun s => Some s)
  (fun '(s, v) =>
    match Nat.odd s with
    | true => Some (2 * v)
    | false =>
        match Nat.eqb s v, Nat.eqb (s / 2) v with
        | true, _ => Some s
        | false, true => Some (2 * s)
        | false, false => Some (2 * v)
        end
    end)).
  have HTG : GetTotal Ss Vv l. by move => [].
  have HTP : PutTotal Ss Vv l. move => s v /=. case (Nat.odd s) => //. case: (Nat.eqb s v) => //. case: (s / 2 =? v) => //.
  have HPGP : PGP Ss Vv l. unfold PGP. move => s s' v v' [H1 H2].
  case: H2 => <-. have Hodd2 : forall x, Nat.odd (2 * x) = false.
  move=> x. rewrite Nat.mul_comm. elim: x => // x' IH /=.
  have Heqb : forall x, (x =? x) = true.  elim=> // x' IH /=.
  move :H1. simpl. case Hodd: (Nat.odd s).
  move=> [<-] /=. by rewrite Hodd2 Heqb.
  case: (Nat.eqb s v). move=> [<-] /=. by rewrite Hodd Heqb.
  case: (s / 2 =? v). move=> [<-] /=. by rewrite Hodd2 Heqb.
  move=> [<-] /=. by rewrite Hodd2 Heqb.  
  have HGI : GI Ss Vv l. move => s s' v [H1 H2].
  injection H1. move => e1. injection H2. move => e2.
  rewrite <- e1 in e2. rewrite e2. reflexivity.
  have HPI : PI Ss Vv l. move => s s' v v'. simpl.
  case: (Nat.odd s). move=> [<-] [Eq]. lia.
  case Heqv: (s =? v). move=> [Eq_s Eq_v']. injection Eq_s => Eq_s'. subst s'.
  apply Nat.eqb_eq in Heqv. subst v.
  replace ((Nat.divmod s 1 0 1).1) with (s / 2) in Eq_v' by reflexivity.
  case Heqv': (s =? v') in Eq_v'. apply Nat.eqb_eq in Heqv'. apply Heqv'.
  case Heq_s2v': (s / 2 =? v') in Eq_v'. injection Eq_v' => Heq. have Hs : s = 0. lia.
  subst s. simpl in Heqv',Heq_s2v'. rewrite Heq_s2v' in Heqv'. discriminate.
  injection Eq_v' => Heq. subst s. apply Nat.eqb_neq in Heq_s2v'.
  exfalso. apply : Heq_s2v'. replace (v' + (v' + 0)) with (v' * 2) by lia.
  apply: Nat.div_mul => //.
  move=> [Eq_v Eq_v'].
  replace ((Nat.divmod s 1 0 1).1) with (s / 2) in Eq_v by reflexivity.
  replace ((Nat.divmod s 1 0 1).1) with (s / 2) in Eq_v' by reflexivity.
  case Heq_s2v: (s / 2 =? v) in Eq_v. case Heqv': (s =? v') in Eq_v'.
  rewrite -Eq_v' in Eq_v. injection Eq_v => Hs2.
  have Hs : s = 0 by lia. subst s.
  simpl in Heqv, Heq_s2v. rewrite Heq_s2v in Heqv. discriminate.
  apply Nat.eqb_eq in Heq_s2v. case Heq_s2v': (s / 2 =? v') in Eq_v'.
  apply Nat.eqb_eq in Heq_s2v'. lia.
  rewrite -Eq_v in Eq_v'. injection Eq_v' => H_2s_2v'. apply Nat.eqb_neq in Heqv'. lia.
  injection Eq_v => H_s'. subst s'.
  case Heqv': (s =? v') in Eq_v'. injection Eq_v' => Eq_s.
  apply Nat.eqb_neq in Heq_s2v. subst s.
  replace (v + (v + 0)) with (v * 2) in Heq_s2v by lia.
  rewrite Nat.div_mul // in Heq_s2v.
  case Heq_s2v': (s / 2 =? v') in Eq_v'.
  injection Eq_v' => Eq_2s. apply Nat.eqb_neq in Heqv. lia.
  injection Eq_v' => Eq_2v'. lia.  
  have HGS : GS Ss Vv l. rewrite / GS ;case => /=. exists 0; firstorder. move => n; exists (S n);reflexivity.
  have HnotGPG : ~ GPG Ss Vv l. move => HW.
  have H_eval : p_get l 1 = Some 1 /\ p_put l (1, 1) = Some 2 by split.
  have H_false := HW 1 2 1 H_eval. discriminate H_false.
  apply HnotGPG. apply H. apply (inhabited_nat). apply (inhabited_nat). apply HTG. apply HTP. apply HPGP. apply HGI. apply HPI. apply HGS.
Qed.

Lemma TgetTputPS_GI_PI_GS_PP_notGPG : ~[PS &&& GI &&& PI &&& GS &&& PP ===>pg GPG].
Proof.
  move => H.
  bx_test[tg;tp;ps;gi;pi;gs;pp;notgpg].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_ps. move => s. case s.
  exists true;exists false; reflexivity.
  exists true;exists true;reflexivity.
  have_gi. by move => [] [] [];firstorder.
  have_pi. by move => [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notgpg.
  by move => HW; move : (HW false true false (conj erefl erefl)).
  apply HnotGPG. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HPS. apply HGI. apply HPI. apply HGS. apply HPP.
Qed.

Lemma TgetTputPS_GI_PI_GS_PP_notPGP : ~[PS &&& GI &&& PI &&& GS &&& PP ===>pg PGP].
Proof.
  move => H.
  bx_test[tg;tp;ps;gi;pi;gs;pp;notpgp].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_ps. move => s. case s.
  exists true ; exists true ;reflexivity.
  exists true ;exists false ;reflexivity.
  have_gi. by move => [] [] [];firstorder.
  have_pi. by move => [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists false; firstorder.  exists true;firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notpgp.
  by move => HW; move : (HW false false false true (conj erefl erefl)).
  apply HnotPGP. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HPS. apply HGI. apply HPI. apply HGS. apply HPP.
Qed.

Lemma TgetTputPS_GPG_PI_GS_PP_notPGP : ~[PS &&& GPG &&& PI &&& GS &&& PP ===>pg PGP].
Proof.
  move => H.
  bx_test[tg;tp;ps;gpg;pi;gs;pp;notpgp].
  have_tg. by move => [];firstorder.
  have_tp. by move => [] [];firstorder.
  have_ps. move => s. case s.
  exists AA ;exists false ;reflexivity.
  exists BB ;exists true;reflexivity.
  exists CC ;exists true;reflexivity.
  exists DD ;exists false;reflexivity.  
  have_gpg. by move => [] [] [];firstorder.
  have_pi. by move => [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists CC; reflexivity.  exists AA;firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notpgp.
  by move => HW; move : (HW CC DD false true  (conj erefl erefl)).
  apply HnotPGP. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HPS. apply HGPG. apply HPI. apply HGS. apply HPP.
Qed.

Lemma TgetTputUD_PI_notWSS : ~[UD &&& PI ===>pg WSS].
Proof.
  move => H.
  bx_test[tg;tp;ud;pi;notwss].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_ud. by move => [] [] [] [];firstorder.
  have_pi. by move => [] [] [] [];firstorder.
  have_notwss. unfold WSS.
  move => HW. have [v Himp] := HW CC DD true.
  have H_eval : p_put l (DD, true) = Some CC by reflexivity.
  have H_false := Himp H_eval. destruct v;discriminate.
  apply HnotWSS. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HUD. apply HPI.
Qed.

Lemma TgetTputUD_GI_GS_notWSS : ~[UD &&& GI &&& GS ===>pg WSS].
Proof.
  move => H.
  bx_test[tg;tp;ud;gi;gs;notwss].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_ud. by move => [] [] [] [];firstorder.
  have_gi. by move => [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_notwss. unfold WSS.
  move => HW. have [v Himp] := HW false true true.
  have H_eval : p_put l (true, true) = Some false by reflexivity.
  have H_false := Himp H_eval. destruct v;discriminate.  
  apply HnotWSS. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HUD. apply HGI. apply HGS.
Qed.

Lemma TgetTputPS_GI_VD_GS_notWSS : ~[PS &&& GI &&& VD &&& GS ===>pg WSS].
Proof.
  move => H.  set(Ss := nat); set(Vv := nat).
  set (l :=
  @mkLens nat nat
  (fun s => Some s)
  (fun '(s, v) =>
    match Nat.odd s with
    | true => Some (2 * v)
    | false => Some (2 * v + 1)
    end)).
  have HTG : GetTotal Ss Vv l . by move => [];firstorder.
  have HTP : PutTotal Ss Vv l. move => s v /=. case (Nat.odd s) => //.          
  have HPS : PS Ss Vv l. move => s /=.  have Hmod : s mod 2 = 0 \/ s mod 2 = 1.
  elim:s. left. auto.  move => n H1. case H1. move => _. have Hneq : 2 <> 0 by discriminate.
  have Hbound := Nat.mod_upper_bound (S n) 2 Hneq.
  inversion Hbound; subst. right. rewrite H2. firstorder.
  inversion Hbound; subst. right. rewrite H3. firstorder.
  destruct (S n mod 2) as [| [| k]]. left. reflexivity. right. reflexivity.
  inversion H2. inversion H4. move => _. have Hneq : 2 <> 0 by discriminate.
  have Hbound := Nat.mod_upper_bound (S n) 2 Hneq.
  case (S n mod 2) as [| [| k]].
  left. reflexivity. right. reflexivity.
  exfalso. inversion Hbound as [|? Hle1].
  inversion Hle1 as [|? Hle2].   inversion Hle2.
  case Hmod as [H0 | H1]. exists 1,(s/2). f_equal. simpl.
  change ((Nat.divmod s 1 0 1).1) with (s / 2).
  change (s / 2 + (s / 2 + 0)) with (2 * (s / 2)).
  have Hneq : 2 <> 0 by discriminate.
  have Hdiv := Nat.div_mod s 2 Hneq.
  rewrite H0 Nat.add_0_r in Hdiv. symmetry. auto.
  exists 0, (s / 2). f_equal.
  change ((Nat.divmod s 1 0 1).1) with (s / 2).
  change (s / 2 + (s / 2 + 0) + 1) with (2 * (s / 2) + 1).
  have Hneq : 2 <> 0 by discriminate.
  have Hdiv := Nat.div_mod s 2 Hneq.
  rewrite H1 in Hdiv.
  symmetry. simpl. rewrite {1} Hdiv. reflexivity.  
  have HGI : GI Ss Vv l. move => s s' v [H1 H2]. inversion H1. inversion H2. reflexivity.
  have HVD : VD Ss Vv l. move => s s' s'' v v' [H1 H2]. inversion H1. inversion H2.
  change (v + (v + 0)) with (2 * v) in H3.  change (v' + (v' + 0)) with (2 * v') in H4.
  case: (Nat.odd s) H3 => H3. case: (Nat.odd s') H4 => H4. injection H3. injection H4 => Heq.
  move => HN. rewrite <- HN in Heq.
  change (v' + (v' + 0)) with (2 * v') in Heq.
  change (v + (v + 0)) with (2 * v) in Heq.
  have Hdiv := f_equal Nat.div2 Heq. rewrite !Nat.div2_double in Hdiv. auto.
  injection H3. injection H4 => Heq.
  have Hdiv : Nat.div2 (2 * v' + 1) = Nat.div2 (2 * v).
  rewrite Heq. inversion H3. inversion H4. auto.
  rewrite Nat.add_1_r Nat.div2_succ_double Nat.div2_double in Hdiv.
  symmetry. exact Hdiv.
  case: (Nat.odd s') H4 => H4 ; injection H3 ; injection H4 => Heq.
  have Hdiv : Nat.div2 (2 * v') = Nat.div2 (2 * v + 1).
  inversion H3. injection H4. move => _.  rewrite H5. auto.
  rewrite Nat.add_1_r Nat.div2_succ_double Nat.div2_double in Hdiv. move => _. auto.
  move => HN. injection H3 => H3'. injection H4 => H4'.
  have Hdiv : Nat.div2 (2 * v + 1) = Nat.div2 (2 * v' + 1).
  rewrite H3' H4'. reflexivity.
  rewrite !Nat.add_1_r !Nat.div2_succ_double in Hdiv.  exact Hdiv.
  have HGS : GS Ss Vv l. rewrite / GS ;case => /=. exists 0; firstorder.
  move => n. exists (S n). reflexivity.
  have HnotWSS : ~ WSS Ss Vv l. move => HP.
  case (HP 1 0 0) => v Hv. have H1 : p_put l (0, 0) = Some 1 by reflexivity.
  have H2 := Hv H1. simpl in H2. injection H2 => Heq. clear Hv H1 H2.
  case: v Heq => [| v'] Heq. discriminate. inversion Heq as [H0]. clear Heq.
  case: v' H0 => [| v''] H0 ; discriminate H0.
  apply HnotWSS. apply H. apply (inhabited_nat). apply (inhabited_nat). apply HTG. apply HTP. apply HPS. apply HGI. apply HVD. apply HGS.
Qed.

Lemma TgetTputUD_PI_PP_notGI : ~[UD &&& PI &&& PP ===>pg GI].
Proof.
  move => H.
  bx_test[tg;tp;ud;pi;pp;notgi].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_ud. by move => [] [] [] [];firstorder.
  have_pi. by move => [] [] [] [];firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notgi. by move => HW; move : (HW AA BB true (conj erefl erefl)).
  apply HnotGI. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HUD. apply HPI. apply HPP.
Qed.

Lemma TgetTputGPG_GI_PI_GS_notVD : ~[GPG &&& GI &&& PI &&& GS ===>pg VD].
Proof.
  move => H.
  bx_test[tg;tp;gpg;gi;pi;gs;notvd].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gpg. by move => [] [] [];firstorder.
  have_gi. by move => [] [] [];firstorder.
  have_pi. by move => [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists cc; firstorder.  exists aa;firstorder. exists bb;firstorder.
  have_notvd.
  by move => HW; move : (HW aa bb bb aa cc (conj erefl erefl)).
  apply HnotVD. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HGPG. apply HGI. apply HPI. apply HGS.
Qed.

Lemma TgetTputSGP_PP_notPI : ~[SGP &&& PP ===>pg PI].
Proof.
  move => H.
  bx_test[tg;tp;sgp;pp;notpi].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_sgp. by move => [] [] [].
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notpi.
  by move => HW; move : (HW false false aa bb (conj erefl erefl)).
  apply HnotPI. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HSGP. apply HPP.
Qed.

Lemma TgetTputGPG_GI_GS_PP_notPI : ~[GPG &&& GI &&& GS &&& PP ===>pg PI].
Proof.
  move => H.
  bx_test[tg;tp;gpg;gi;gs;pp;notpi].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gpg. by move => [] [] [];firstorder.
  have_gi. by move => [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notpi. unfold PI.
  by move => HW; move : (HW false false false true (conj erefl erefl)).
  apply HnotPI. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HGPG. apply HGI. apply HGS. apply HPP.
Qed.

Lemma TgetTputSGP_PP_notGS : ~[SGP &&& PP ===>pg GS].
Proof.
  move => H.
  bx_test[tg;tp;sgp;pp;notgs].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_sgp. by move => [] [] [].
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notgs.
  move => HW. case : (HW bb) => s.
  case: s ;discriminate.
  apply HnotGS. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HSGP. apply HPP.
Qed.

Lemma TgetTputGPG_GI_PI_notGS : ~[GPG &&& GI &&& PI ===>pg GS].
Proof.
  move => H. set(Ss := nat); set(Vv := nat).
  set (l :=
  @mkLens nat nat
  (fun s => Some (S s))
  (fun '(s, v) =>
    match Nat.eqb v (S s) with
    | true => Some s
    | false =>
        match Nat.eqb v s with
        | true => Some (S s)
        | false => Some v
        end
    end)).
  have HTG : GetTotal Ss Vv l. by move => [].
  have HTP : PutTotal Ss Vv l. move => s v /=. case (Nat.eqb v (S s)) => //. case (v =? s) => //.
  have HGPG : GPG Ss Vv l. move => s s' v [H1 H2]. inversion H1. inversion H2.
  rewrite H3 in H4. rewrite Nat.eqb_refl in H4.
  inversion H4; subst. reflexivity.
  have HGI : GI Ss Vv l. move => s s' v [H1 H2].
  inversion H1. inversion H2. rewrite <- H3 in H4. injection H4. move => H5. auto.
  have HPI : PI Ss Vv l. move => s s' v v' [H1 H2].
  destruct (v =? S s) eqn:Ev1. apply Nat.eqb_eq in Ev1. subst v. 
  inversion H1. destruct (v' =? S s) eqn:Ev'1.
  apply Nat.eqb_eq in Ev'1. subst v'. reflexivity.
  destruct (v' =? s) eqn:Ev'2. inversion H2. exfalso. rewrite Ev'1 in H4.
  rewrite Ev'2 in H4. rewrite Nat.eqb_refl in H3. inversion H3;subst s'.
  inversion H4. exact (Nat.neq_succ_diag_l s H5).
  rewrite Nat.eqb_refl in H3. inversion H3;subst s'.
  inversion H2. rewrite Ev'1 in H4. rewrite Ev'2 in H4.
  inversion H4;subst v'. rewrite Nat.eqb_refl in Ev'2. discriminate Ev'2.
  inversion H1. inversion H2. rewrite Ev1 in H3. destruct (v =? s) eqn:Ev2.
  inversion H3;subst s'. destruct (v' =? S s) eqn:Ev'1.
  inversion H4. exfalso. symmetry in H5. exact (Nat.neq_succ_diag_l s H5). 
  apply Nat.eqb_eq in Ev2. subst v. destruct (v' =? s) eqn:Ev'2.
  apply Nat.eqb_eq in Ev'2. subst v'. reflexivity.
  inversion H4;subst v'. rewrite Nat.eqb_refl in Ev'1. discriminate Ev'1.
  inversion H3;subst s'. destruct (v' =? S s) eqn:Ev'1.
  inversion H4;subst v. rewrite Nat.eqb_refl in Ev2. discriminate Ev2.
  destruct (v' =? s) eqn:Ev'2. inversion H4; subst v.
  rewrite Nat.eqb_refl in Ev1. discriminate Ev1. inversion H4. reflexivity.  
  have HnotGS : ~ GS Ss Vv l.
  move => HW. case : (HW 0) => s. case: s ;discriminate.
  apply HnotGS. apply H. apply (inhabited_nat). apply (inhabited_nat). apply HTG. apply HTP. apply HGPG. apply HGI. apply HPI.
Qed.

Lemma TgetTputPS_GI_PI_PP_notGS : ~[PS &&& GI &&& PI &&& PP ===>pg GS].
Proof.
  move => H. set(Ss := nat); set(Vv := nat).
  set (l :=
  @mkLens nat nat
  (fun s => Some (S s))
  (fun '(s, v) => Some v)).
  have HTG : GetTotal Ss Vv l. by move => [].
  have HTP : PutTotal Ss Vv l. by move => [] [].
  have HPS : PS Ss Vv l. move => s. exists 0,s. reflexivity.
  have HGI : GI Ss Vv l. move => s s' v [H1 H2].
  inversion H1. inversion H2. rewrite <- H3 in H4. injection H4. move => H5. auto.
  have HPI : PI Ss Vv l. move => s s' v v' [H1 H2]. inversion H1. inversion H2. reflexivity.
  have HPP : PP Ss Vv l. move => s s' s'' v v' [H1 H2]. inversion H1. inversion H2. reflexivity.
  have HnotGS : ~ GS Ss Vv l. move => HW. case: (HW 0) => s. case : s ;discriminate. 
  apply HnotGS. apply H. apply (inhabited_nat). apply (inhabited_nat). apply HTG. apply HTP. apply HPS. apply HGI. apply HPI. apply HPP.
Qed.

Lemma TgetTputPS_GPG_PI_PP_notGS : ~[PS &&& GPG &&& PI &&& PP ===>pg GS].
Proof.
  move => H.
  bx_test[tg;tp;ps;gpg;pi;pp;notgs].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_ps. move => s/=. case s. exists true,true;reflexivity. exists true,false;reflexivity.
  have_gpg. by move => [] [] [];firstorder.
  have_pi. by move => [] [] [] [];firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notgs. move => HW. case : (HW true) => s. case s;discriminate.
  apply HnotGS. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HPS. apply HGPG. apply HPI. apply HPP.
Qed.

Lemma TgetTputSGP_PT_notPP : ~[SGP &&& PT ===>pg PP].
Proof.
  move => H.
  bx_test[tg;tp;sgp;pt;notpp].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_sgp. by move => [] [] [].
  have_pt. by move => [] [] [];firstorder.
  have_notpp.
  by move => HW; move : (HW false true true aa bb(conj erefl erefl)).
  apply HnotPP. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HSGP. apply HPT.
Qed.

Lemma TgetTputUD_PI_PT_notPP : ~[UD &&& PI &&& PT ===>pg PP].
Proof.
  move => H.
  pose (Ss := nat).
  pose (Vv := nat).
  pose (l :=
    {|
      p_get := fun s : nat => Some (s / 2);
      p_put := fun '(s, v) => 
        match v =? (s / 2) with
        | true => Some s
        | false => match Nat.even s with
                   | true => Some (2 * v + 1)
                   | false => Some (2 * v)
                   end
        end
    |} : Lens nat nat).
  have HTG : GetTotal Ss Vv l. by move => [].
  have HTP : PutTotal Ss Vv l. move => s v H1. cbn in H1.
  destruct (v ?= s / 2). destruct 
  have HUD : UD Ss Vv l. move => s s' v v' [H1 H2]. inversion H1. inversion H2. simpl.
  have_pi. by move => [] [] [] [];firstorder.
  have_pt. by move => [] [] [];firstorder.
  have_notpp. unfold PP.
  by move => HW; move : (HW true true true (conj erefl erefl)).
  apply HnotPP. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HUD. apply HPI. apply HPT.
Qed.

Lemma TgetTputUD_GI_GS_PT_notPP : ~[UD &&& GI &&& GS &&& PT ===>pg PP].
Proof.
  move => H.
  bx_test[tg;tp;ud;gi;gs;pt;notpp].
  have_tg. by move => [];firstorder.
  have_tp. by move => [] [];firstorder.
  have_ud. by move => [] [] [] [];firstorder.
  have_gi. by move => [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists bb; firstorder.  exists aa;firstorder.
  have_pt. by move => [] [] [];firstorder.
  have_notpp. unfold PP.
  by move => HW; move : (HW true true true (conj erefl erefl)).
  apply HnotPP. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HUD. apply HGI. apply HGS. apply HPT.
Qed.

Lemma TgetTputPS_GI_PI_GS_PT_notPP : ~[PS &&& GI &&& PI &&& GS &&& PT ===>pg PP].
Proof.
  move => H.
  bx_test[tg;tp;ps;gi;pi;gs;pt;notpp].
  have_tg. by move => [];firstorder.
  have_tp. by move => [] [];firstorder.
  have_ps.
  have_gi. by move => [] [] [];firstorder.
  have_pi. by move => [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists bb; firstorder.  exists aa;firstorder.
  have_pt. by move => [] [] [];firstorder.
  have_notpp. unfold PP.
  by move => HW; move : (HW true true true (conj erefl erefl)).
  apply HnotPP. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HPS. apply HGI. apply HPI. apply HGS. apply HPT.
Qed.

Lemma TgetTputSGP_notPT : ~[SGP ===>pg PT].
Proof.
  move => H.
  bx_test[tg;tp;sgp;notpt].
  have_tg. by move => [];firstorder.
  have_tp. by move => [] [];firstorder.
  have_sgp. by move => [] [];firstorder.
  have_notPT. unfold PT.
  by move => HW; move : (HW true true true (conj erefl erefl)).
  apply Hnotpt. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HSGP.
Qed.

Lemma TgetTputGPG_GI_PI_GS_notPT : ~[GPG &&& GI &&& PI &&& GS ===>pg PT].
Proof.
  move => H.
  bx_test[tg;tp;gpg;gi;pi;gs;notpt].
  have_tg. by move => [];firstorder.
  have_tp. by move => [] [];firstorder.
  have_gpg. by move => [] [] [];firstorder.
  have_gi. by move => [] [] [];firstorder.
  have_pi. by move => [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists bb; firstorder.  exists aa;firstorder.
  have_notpt. unfold PT.
  by move => HW; move : (HW true true true (conj erefl erefl)).
  apply HnotPT. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HGPG. apply HGI. apply HPI. apply HGS.
Qed.

Lemma TgetTputUD_WSS_GI_GS_notPT : ~[UD &&& WSS &&& GI &&& GS ===>pg PT].
Proof.
  move => H.
  bx_test[tg;tp;ud;wss;gi;gs;notpt].
  have_tg. by move => [];firstorder.
  have_tp. by move => [] [];firstorder.
  have_ud. by move => [] [] [] [];firstorder.
  have_wss.
  have_gi. by move => [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists bb; firstorder.  exists aa;firstorder.
  have_notpt. unfold PT.
  by move => HW; move : (HW true true true (conj erefl erefl)).
  apply HnotPT. apply H. firstorder. firstorder. apply HTG. apply HTP. apply HUD. apply HWSS. apply HGI. apply HGS.
Qed.
