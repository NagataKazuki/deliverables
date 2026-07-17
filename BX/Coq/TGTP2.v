From bx_plugin.Coq Require Export TGTP.


Lemma TgetTputPIandPT_VD : [PI &&& PT ===>pg VD].
Proof.
  move => S V l hs hv gt pt PI PT s s' s'' v v' [H1 H2];
  apply (PI s'' s'' v v');
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


Lemma TgetTputUDandPGnotWSS : ~[UD &&& PG ===>pg WSS].
Proof.
  move => H.
  bx_test [tg;tp;ud;pg;notwss].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_ud. by move => [] [] [] [];firstorder.
  have_pg. by move => [] [] [].
  have_notwss. unfold WSS. by  move=> HW; case: (HW AA BB false) => v /(_ erefl);case: v.
  apply HnotWSS. apply H. firstorder. apply inhabited_bool.
  apply HTG. apply HTP. apply HUD. apply HPG.
Qed.

Lemma TgetTputGIandUDandGSnotWSS : ~[GI &&& UD &&& GS ===>pg WSS].
Proof.
  move => H.
  bx_test[tg;tp;gi;ud;gs;notwss].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_ud. by move => [] [] [] [];firstorder.
  have_gi. by move => [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_notwss.  by move=> HW; case: (HW true false true) => v /(_ erefl); case: v. 
  apply HnotWSS. apply H.  apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HGI. apply HUD. apply HGS.
Qed.

Lemma TgetTputGIandVDandGSnotWSS : ~[GI &&& VD &&& GS &&& PS ===>pg WSS].
Proof.
  move => H. set (Sv := nat). set (Vv := nat).
  set (l :=
  @mkLens nat nat
  (fun n => Some n)
  (fun '(s,v) =>
   match v with
   | 0 =>
       match s with
       | 0 => Some 1
       | S _ => Some 0
       end
   | S n => Some (S (S n))
   end)
      ).
  
  have HWSS : GetTotal Sv Vv l -> PutTotal Sv Vv l -> GI Sv Vv l -> VD Sv Vv l -> GS Sv Vv l -> PS Sv Vv l -> WSS Sv Vv l := H Sv Vv _ _ l.
  have HnotWSS : ~ WSS Sv Vv l.
  { unfold WSS. move=> HW.
    move: (HW (S 0) 0 0) => [v H_impl].
    have Hs := H_impl erefl. clear H_impl.
    case: v Hs => [|n]; discriminate. }
  have GT : GetTotal Sv Vv l. by move => [].
  have PT : PutTotal Sv Vv l. move => [] [].
  discriminate. discriminate. by move => [].
  destruct n. by move => []. by move => [].
  have HGI : GI Sv Vv l.
  move => [] [] [];firstorder. simpl in H0;simpl in H1;rewrite <- H0 in H1; inversion H1.
  rewrite <- H0 in H1; inversion H1.
  simpl in H0;simpl in H1; rewrite <- H0 in H1; inversion H1.
  rewrite <- H0 in H1; inversion H1; reflexivity.
  rewrite <- H0 in H1; inversion H1; reflexivity.
  rewrite <- H0 in H1; inversion H1; reflexivity.

  have HPS : PS Sv Vv l. unfold PS. move => s. case s. exists (S 0);exists(0); reflexivity.
  move => n. case n. exists (0);exists(0);reflexivity.
  move => n0. exists(S n0); exists (S n0);reflexivity.

  have HVD : VD Sv Vv l. move => [] [] [] [] []. firstorder. firstorder.
  by move => v' []. by move => n v' []. move =>[]. firstorder.
  by move => n []. by move => n v' []. move => v v' [H1 H2].
  case v,v'. discriminate. discriminate. discriminate. firstorder.
  move => n v v' [H1 H2]. case v,v'. discriminate. discriminate. discriminate. firstorder.
  by move => v' []. by move => n v' [].
  move => v v' [H1 H2]. case v,v'. discriminate. discriminate. discriminate. firstorder.
  move => n v v' [H1 H2]. case v,v'. discriminate. discriminate. discriminate. firstorder.
  move => v v' [H1 H2]. case v,v'. discriminate. discriminate. discriminate. firstorder.
  move => n v v' [H1 H2]. case n,v,v';firstorder. discriminate. discriminate.
  move => s'' v v' [H1 H2]. case s'',v,v';firstorder. discriminate. discriminate.
  move => n s'' v v' [H1 H2]. case n,s'',v,v';firstorder. discriminate. discriminate. discriminate. discriminate.
  move => v'. case v'. firstorder. by move => n [].
  by move => n v' []. move => v v'. case v,v';firstorder. discriminate.
  move => n v v' [H1 H2]. case n,v,v';firstorder. discriminate. discriminate.
  move => v v' [H1 H2]. case v,v';firstorder. discriminate. discriminate.
  move => n v v' [H1 H2]. case n,v,v';firstorder. discriminate. discriminate. discriminate. discriminate.
  move => s'' v v' [H1 H2]. case s'',v,v';firstorder. discriminate. discriminate. discriminate. discriminate.
  move => n s'' v v' [H1 H2]. case n,s'',v,v';firstorder.
  discriminate. discriminate. discriminate. discriminate. discriminate. discriminate. discriminate. discriminate.
  move => v v' [H1 H2]. case v,v';firstorder. discriminate.
  move => n v v' [H1 H2]. case n,v,v';firstorder. discriminate. discriminate.
  move => s'' v v' [H1 H2]. case s'',v,v';firstorder. discriminate. discriminate. discriminate. discriminate.
  move => n s'' v v' [H1 H2]. case n,s'',v,v';firstorder.
  discriminate. discriminate. discriminate.
  discriminate. discriminate. discriminate. discriminate. discriminate.
  move => s'' v v' []. case s'',v,v';firstorder. discriminate. discriminate.
  move => n s'' v v' [H1 H2]. case n,s'',v,v';firstorder.
  discriminate. discriminate. discriminate. discriminate.
  discriminate. discriminate. discriminate. discriminate.
  move => s' s'' v v' [H1 H2]. case s',s'',v,v';firstorder.
  discriminate. discriminate. discriminate. discriminate. discriminate. discriminate.
  move => n s' s'' v v' [H1 H2]. case n,s',s'',v,v';firstorder.
  discriminate. discriminate. discriminate. discriminate. discriminate. discriminate.
  discriminate. discriminate. discriminate. discriminate. discriminate. discriminate. 

  have HGS : GS Sv Vv l. move => v. case v. exists (0); firstorder.
  move => n. exists(S n);firstorder.
  
 by apply: HnotWSS;
   apply: (HWSS inhabited_nat inhabited_nat).
Qed.

Lemma TgetTputGPandGIandPIandGSnotPT : ~[GP &&& GI &&& PI &&& GS ===>pg PT].
  move => H.
  bx_test[tg;tp;gp;gi;pi;gs;notpt].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gp.  move => [] [];firstorder. simpl in H0. discriminate H0. discriminate. discriminate.
  have_gi. by move => [] [] [];firstorder. 
  have_pi. by move => [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists cc; firstorder. exists aa;firstorder. exists bb;firstorder.
  have_notpt.  by move => HW;move : (HW aa bb aa  erefl).
  apply HnotPT. apply H.  firstorder. firstorder.
  apply HTG. apply HTP. apply HGP. apply HGI. apply HPI. apply HGS.
Qed.

Lemma TgetTputSGPandPTnotPP : ~[SGP &&& PT ===>pg PP].
Proof.
  move => H.
  bx_test[tg;tp;sgp;pt;notpp].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_sgp. by move => [] [] [];firstorder.
  have_pt. by move => []  [] [];firstorder.
  have_notpp. unfold PP.  move => HW. move : (HW true false false cc bb(conj erefl erefl)). discriminate.
  apply HnotPP. apply H. apply inhabited_bool. firstorder.
  apply HTG. apply HTP. apply HSGP. apply HPT.
Qed.

(*Lemma TgetTputGPandPGandUDandPTnotPP : ~ [GP &&& PG &&& UD &&& PT ===>pg PP].*)  

Lemma TgetTputSGPandPPnotPI : ~[SGP &&& PP ===>pg PI].
Proof.
  move => H.
  bx_test[tg;tp;sgp;pp;notpi].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_sgp. by move => [] [] [];firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notpi.  by move => HW;move : (HW false false aa bb (conj erefl erefl)).
  apply HnotPI. apply H. apply inhabited_bool. firstorder.
  apply HTG. apply HTP. apply HSGP. apply HPP.
Qed.

Lemma TgetTputGPandUDandGIandGSandPPnotPI : ~[GP &&& UD &&& GI &&& GS &&& PP ===>pg PI].
Proof.
  move => H.
  bx_test[tg;tp;gp;ud;gi;gs;pp;notpi].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gp. by move => [] [];firstorder.
  have_ud. by move => [] [] [] [];firstorder.
  have_gi. by move => [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notpi. by move => HW;move : (HW true true true false (conj erefl erefl)).
  apply HnotPI. apply H.  apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HGP. apply HUD. apply HGI. apply HGS. apply HPP.
Qed.


Lemma TgetTputGPandGIandGSandPInotVD : ~[GP &&& GI &&& GS &&& PI ===>pg VD].
Proof.
  move => H.
  bx_test[tg;tp;gp;gi;gs;pi;notvd].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gp. by move => [] [];firstorder.
  have_gi. by move => [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists cc; firstorder. exists aa ;firstorder. exists bb;firstorder.
  have_pi. by move => [] [] [] [];firstorder.
  have_notvd. by move => HW;move : (HW aa bb cc cc bb (conj erefl erefl)).
  apply HnotVD. apply H. firstorder. firstorder.
  apply HTG. apply HTP. apply HGP. apply HGI. apply HGS. apply HPI.
Qed.

Lemma TgetTputSGPandPPnotGS : ~ [SGP &&& PP ===>pg GS].
Proof.
  move => H.
  bx_test [tg;tp;sgp;pp;notgs].
  have_tg. by move => [] [];firstorder.
  have_tp. by move => [] [] [];firstorder.
  have_sgp. by move => [] [] [].
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notgs. move=> HW; case: (HW bb) => [[]] //.
  apply HnotGS. apply H.  apply inhabited_bool. firstorder.
  apply HTG. apply HTP. apply HSGP. apply HPP.
Qed.

Lemma TgetTputSSandGIandVDandPPnotGS : ~[SS &&& GI &&& VD &&& PP ===>pg GS].
Proof.  
  move => H.
  set (Sv := nat). set (Vv := nat).
  set (l :=
         @mkLens nat nat
           (fun b => Some (S b))
           (fun '(s,v) => Some v) 
           ).
  have HGS : GetTotal Sv Vv l -> PutTotal Sv Vv l -> SS Sv Vv l -> GI Sv Vv l -> VD Sv Vv l -> PP Sv Vv l -> GS Sv Vv l := H Sv Vv _ _ l.
  have HSS : SS Sv Vv l. move => s. exists s. reflexivity.
  have HGI : GI Sv Vv l. move => s s' v [H1 H2].
  injection H1. move => e1. injection H2. move => e2. rewrite <- e1 in e2. inversion e2. reflexivity.
  have HVD : VD Sv Vv l. move => s s' s'' v v' [H1 H2]. inversion H1. inversion H2. reflexivity.
  have HPP : PP Sv Vv l. move => s s' s'' v v' [H1 H2]. simpl in H2. simpl. apply H2.
  have HnotGS : ~ GS Sv Vv l. move => HW. move : (HW 0) => [s Ho]. discriminate.
  have HTG : GetTotal Sv Vv l. move => s. discriminate.
  have HTP : PutTotal Sv Vv l. move => s v. discriminate.
  apply HnotGS. apply HGS. firstorder. exact 0. firstorder. exact 0.
  apply HTG. apply HTP. apply HSS. apply HGI. apply HVD. apply HPP.
Qed.

Lemma TgetTputGPandGIandPInotGS : ~[GP &&& GI &&& PI ===>pg GS].
Proof.
  move => H. set (Sv := nat). set (Vv := nat).
  set (l :=
         @mkLens nat nat
           (fun b => Some (2 * b))
           (fun '(s,v) =>
              match v with
              |0 => Some 0
              |_ => if Nat.eqb v  (2 * s) then Some s else Some(s+v) end)).              
  have HTG : GetTotal Sv Vv l. move => s. discriminate.  
  have HTP : PutTotal Sv Vv l. move => s v. destruct v. discriminate. simpl.
  destruct (match s + (s + 0) with| 0 => false | S m' => Nat.eqb v m' end); discriminate.
  have HGP : GP Sv Vv l. move => s v H1. simpl in H1. simpl.  injection H1 as He.
  rewrite <- He. destruct s as [| s'].
  reflexivity. simpl.
  rewrite Nat.eqb_refl.
  
  have_gi. by move => [] [] [];firstorder.
  have_pi. by move => [] [] [] [];firstorder.
  have_notgs. by move=> H_surj; case: (H_surj true) => s; case: s.
  apply H. apply HnotGS. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HGP. apply HGI. apply HPI.
Qed.

Lemma TgetTputGPandGIandPIandGSnotWPG : ~[GP &&& GI &&& PI &&& GS ===>pg WPG].
Proof.
  move => H.
  bx_test[tg;tp;gp;gi;pi;gs;notwpg].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gp. by move => [] [].
  have_gi. by move => [] [] [];firstorder.
  have_pi. by move => [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_notwpg. by move => HW;move : (HW false true false erefl).
  apply H. apply HnotPI. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HGP. apply HGI. apply HPI. apply HGS.
Qed.

Lemma TgetTputGPandGIandGSandPTnotWPG : ~[GP &&& GI &&& GS &&& PT ===>pg WPG].
Proof.
  move => H.
  bx_test[tg;tp;gp;gi;gs;pt;notwpg].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gp. by move => [] [].
  have_gi. by move => [] [] [];firstorder.
  have_pt. by move => [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_notwpg. by move => HW;move : (HW false true false erefl).
  apply H. apply HnotPI. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HGP. apply HGI. apply HGS. apply HPT.
Qed.

Lemma TgetTputGPGandSSandVDandGSandPPnotWPG : ~[GPG &&& SS &&& VD &&& GS &&& PP ===>pg WPG].
Proof.
  move => H.
  bx_test[tg;tp;gpg;ss;vd;gs;pp;notwpg].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gpg. by move => [] [] [];firstorder.
  have_ss. rewrite /SS; case => /=. exists true;by []. exists false ;by [].
  have_vd. by move => [] [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notwpg. by move => HW;move : (HW false true false erefl).
  apply H. apply HnotPI. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HGPG. apply HSS. apply HVD. apply HGS. apply HPP.
Qed.

Lemma TgetTputGIandSSandVDandGSandPPnotWPG : ~[GI &&& SS &&& VD &&& GS &&& PP ===>pg WPG].
Proof.
  move => H.
  bx_test[tg;tp;gi;ss;vd;gs;pp;notwpg].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gi. by move => [] [] [];firstorder.
  have_ss. rewrite /SS; case => /=. exists true;by []. exists false ;by [].
  have_vd. by move => [] [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notwpg. by move => HW;move : (HW false true false erefl).
  apply H. apply HnotPI. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HGI. apply HSS. apply HVD. apply HGS. apply HPP.
Qed.

Lemma TgetTputPGPandPGandPPnotPS : ~ [PGP &&& PG &&& PP ===>pg PS].
Proof.
  move => H.
  bx_test[tg;tp;pgp;pg;pp;notps].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_pgp. by move => [] [] [] [];firstorder.
  have_pg. by move => [] [] [];firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notps. by move=> HW ;case: (HW false) => s' [v Hv]; case: s' Hv; case: v.
  apply H. apply HnotPS. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HPGP. apply HPG. apply HPP.
Qed.

Lemma TgetTputGIandPGPandWPGandGSandPPnotPS : ~[GI &&& PGP &&& WPG &&& GS &&& PP ===>pg PS].
Proof.
  move => H.
  bx_test [tg;tp;gi;pgp;wpg;gs;pp;notps].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gi. by move => [] [] [];firstorder.
  have_pgp. by move => [] [] [] [];firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_wpg. by move => [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notps. by  move=> HW ;case: (HW false) => s' [v Hv]; case: s' Hv; case: v.
  apply H. apply HnotPS. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HGI. apply HPGP. apply HWPG. apply HGS. apply HPP.
Qed.  

Lemma TgetTputGIandVDandGSnotPS : ~[GI &&& VD &&& GS ===>pg PS].
Proof.
  move => H.
  bx_test[tg;tp;gi;vd;gs;notps].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gi. move => [] [] [];firstorder.
  have_vd. by move => [] [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_notps. by move=> HW ;case: (HW false) => s' [v Hv]; case: s' Hv; case: v.
  apply H. apply HnotPS. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HGI. apply HVD. apply HGS.
Qed.

Lemma TgetTputPSandPGnotSS : ~[PS &&& PG ===>pg SS].
Proof.
  move => H.
  bx_test[tg;tp;ps;pg;notss].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_ps. 
  have_pg. by move => [] [] [];firstorder.
  have_ss. 
  apply H. apply HnotPS. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HPS. apply HPG.
Qed.

Lemma TgetTput : ~[GP &&& UD &&& PP ===>pg GI].
Proof.
  move => H.
  bx_test [tg;tp;gp;ud;pp;notgi].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gp. by move => [] [];firstorder.
  have_ud. by move => [] [] [] [];firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notgi. by move => HW;move : (HW false true false erefl).
  apply H. apply HnotGI. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HGP. apply HUD. apply HPP.
Qed.

Lemma TgetTputGPandUDandGIandPPnotSGP : ~ [GP &&& UD &&& GI &&& GS &&& PP ===>pg SGP].
Proof.
  move => H.
  bx_test[tg;tp;gp;ud;gi;gs;pp;notsgp].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gp. by move => [] [];firstorder.
  have_ud. by move => [] [] [] [];firstorder.
  have_gi. by move => [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notsgp. by move => HW;move : (HW false true false erefl).
  apply H. apply HnotSGP. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HGP. apply HUD. apply HGI. apply HGS. apply HPP.
Qed.

Lemma TgetTputGPandUDandPGandPPnotSGP : ~ [GP &&& UD &&& PG &&& PP ===>pg SGP].
Proof.
  move => H.
  bx_test[tg;tp;gp;ud;pg;pp].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gp. by move => [] [];firstorder.
  have_ud. by move => [] [] [] [];firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_pg. by move => [] [] [];firstorder.
  have_notsgp. by move => HW;move : (HW false true false erefl).
  apply H. apply HnotSGP. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HGP. apply HUD. apply HPG. apply HPP.
Qed.

Lemma TgetTputSSandGPGandVDandGSandPPnotPGP : ~[SS &&& GPG &&& VD &&& GS &&& PP ===>pg PGP].
Proof.
  move => H.
  bx_test [tg;tp;ss;gpg;vd;gs;pp;notpgp].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_ss. 
  have_gpg. by move => [] [] [];firstorder.
  have_vd. by move => [] [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_pgp. by move => HW;move : (HW false true false erefl).
  apply H. apply HnotPGP. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HSS. apply HGPG. apply HVD. apply HGS. apply HPP.
Qed.

Lemma TgetTputSSandGIandVDandGSandPPnotPGP : ~[SS &&& GI &&& VD &&& GS &&& PP ===>pg PGP].
Proof.
  move => H.
  bx_test [tg;tp;ss;gi;vd;gs;pp;notpgp].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_ss.
  have_gi. by move => [] [] [];firstorder.
  have_vd. by move => [] [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notpgp. by move => HW;move : (HW false true false erefl).
  apply H. apply HnotPGP. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HSS. apply HGI. apply HVD. apply HGS. apply HPP.
Qed.

Lemma TgetTputUDandPGnotPGP : ~[UD &&& PG ===>pg PGP].
Proof.
  move => H.
  bx_test [tg;tp;ud;pg;notpgp].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_ud. by move => [] [] [] [];firstorder.
  have_pg. by move => [] [] [];firstorder.
  have_notpgp. by move => HW;move : (HW false true false erefl).
  apply H. apply HnotPGP. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HUD. apply HPG.  
Qed.

Lemma TgetTputUDandGIandGSnotPGP : ~[UD &&& GI && GS ===>pg PGP].
Proof.
  move => H.
  bx_test [tg;tp;ud;pg;notpgp].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_ud. by move => [] [] [] [];firstorder.
  have_gi. by move => [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_notpgp. by move => HW;move : (HW false true false erefl).
  apply H. apply HnotPGP. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HUD. apply HGI. apply HGS.
Qed.

Lemma TgetTputGPandPGandPTnotUD : ~[GP &&& PG &&& PT ===>pg UD].
Proof.
  move => H.
  bx_test[tg;tp;gp;pg;pt;notud].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_pg. by move => [] [] [];firstorder.
  have_gp. by move => [] [];firstorder.
  have_pt. by move => [] [] [];firstorder.
  have_notud. by move => HW;move : (HW false true false erefl).
  apply H. apply HnotUD. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HGP. apply HPG. apply HPT.
Qed.

Lemma TgetTputGPandGIandWPGandGsandPTnotUD : ~[GP &&& GI &&& WPG &&& GS &&& PT ===>pg UD].
Proof.
  move => H.
  bx_test[tg;tp;gp;gi;wpg;gs;pt;notud].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gp. by move => [] [];firstorder.
  have_gi. by move => [] [] [];firstorder.
  have_wpg. by move => [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_pt. by move => [] [] [] [];firstorder. 
  have_notud. by move => HW;move : (HW false true false erefl).
  apply H. apply HnotUD. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HGP. apply HGI. apply HWPG. apply HGS. apply HPT.
Qed.

Lemma TgetTputPGPandPGandPPnotUD : ~[PGP &&& PG &&& PP ===>pg UD].
Proof.
  move => H.
  bx_test[tg;tp;pgp;pg;pp;notud].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_pgp. by move => [] [] [] [];firstorder.
  have_pg. by move => [] [] [];firstorder.
  have_pp. by move =. [] [] [] [] [];firstorder.
  have_notud. by move => HW;move : (HW false true false erefl).
  apply H. apply HnotUD. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HPGP. apply HPG. apply HPP.
Qed.

Lemma TgetTputGIandSSandVDandGSandPPnotUD : ~[GI &&& SS &&& VD &&& GS &&& PP ===>pg UD].
Proof.
  move => H.
  bx_test [tg;tp;gi;ss;vd;gs;pp;notud].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gi. by move => [] [] [];firstorder.
  have_ss.
  have_vd. by move => [] [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notud. by move => HW;move : (HW false true false erefl).
  apply H. apply HnotUD. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HGI. apply HSS. apply HVD. apply HGS. apply HPP.
Qed.

Lemma TgetTputGIandWPGandPGPandGSandPPnotUD : ~[GI &&& WPG &&& PGP &&& GS &&& PP ===>pg UD].
Proof.
  move => H.
  bx_test[tg;tp;gi;wpg;pgp;gs;pp;notud].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gi. by move => [] [] [];firstorder.
  have_wpg. by move => [] [] [] [];firstorder.
  have_pgp. by move => [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notud. by move => HW;move : (HW false true false erefl).
  apply H. apply HnotUD. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HGI. apply HWPG. apply HPGP. spply HGS. apply HPP.
Qed.

Lemma TgetTputUDandPGnotGP : ~[UD &&& PG ===>pg GP].
Proof.
  move => H.
  bx_test[tg;tp;ud;pg;notgp].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_ud. by move => [] [] [] [];firstorder.
  have_pg. by move => [] [] [];firstorder.
  have_notgp. by move => HW;move : (HW false true false erefl).
  apply H. apply HnotUD. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HUD. apply HPG.
Qed.

Lemma TgetTputGIandUDandGSnotGP : ~[GI &&& UD &&& GS ===>pg GP].
Proof.
  move => H.
  bx_test[tg;tp;gi;ud;gs;notgp].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gi. by move => [] [] [];firstorder.
  have_ud. by move => [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_notgp. by move => HW;move : (HW false true false erefl).
  apply H. apply HnotGP. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HGI. apply HUD. apply HGS.
Qed.

Lemma TgetTputPGPabdPGandPPnotGP : ~[PGP &&& PG &&& PP ===>pg GP].
Proof.
  move => H.
  bx_test [tg;tp;pgp;pg;pp;notgp].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_pgp. by move => [] [] [] [];firstorder.
  have_pg. by move => [] [] [];firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notgp. by move => HW;move : (HW false true false erefl).
  apply H. apply HnotGP. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HPGP. apply HPG. apply HPP.

Qed.

Lemma TgetTputSSandGPGandVDandGSandPPnotGP : ~[SS &&& GPG &&& VD &&& GS &&& PP ===>pg GP].
Proof.
  move => H.
  bx_test [tg;tp;ss;gpg;vd;gs;pp;notgp].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_ss.
  have_gpg. by move => [] [] [];firstorder.
  have_vd. by move => [] [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notgp. by move => HW;move : (HW false true false erefl).
  apply H. apply HnotGP. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HSS. apply HGPG. apply HVD. apply HGS. apply HPP.
Qed.

Lemma TgetTputGIandSSandVDandGSandPPnotGP : ~[GI &&& SS &&& VD &&& GS &&& PP ===>pg GP].
Proof.
  move => H.
  bx_test [tg;tp;gi;vd;gs;pp;notgp].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gi. by move => [] [] [];firstorder.
  have_ss.
  have_vd. by move => [] [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_pp. by move => [] [] [] [] [];firstorder.
  have_notgp. by move => HW;move : (HW false true false erefl).
  apply H. apply HnotUD. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HGI. apply HSS. apply HVD. apply HGS. apply HPP.
Qed.

Lemma TgetTputGIandPGPandWPGandGSandPPnotGP : ~[GI &&& PGP &&& WPG &&& GS &&& PP ===>pg GP].
Proof.
  move => H.
  bx_test [tg;tp;gi;pgp;wpg;gs;pp;notgp].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gi. by move => [] [] [];firstorder.
  have_pgp. by move => [] [] [] [];firstorder.
  have_wpg. by move => [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_pp. by move => [] [] [] [] [].
  have_notgp. by move => HW;move : (HW false true false erefl).
  apply H. apply HnotUD. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HGI. apply HPGP. apply HWPG. apply HGS. apply HPP.
Qed.

