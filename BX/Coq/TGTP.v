From bx_plugin.Coq Require Import tac.

Notation "[ L1 &&& .. &&& Ln ===>pg L ]" :=
  (forall (S V : Type) `{inhabited S} `{inhabited V} (l : Lens S V),
     GetTotal S V l -> PutTotal S V l-> L1 S V l -> .. (Ln S V l -> L S V l) .. )
  (at level 60,
   format "[ L1  &&&  ..  &&&  Ln  ===>pg L ]").

Section GPfamily.

Lemma TgetTputSGP_GP : [SGP ===>pg GP].
Proof.
  firstorder.
Qed.

Lemma TgetTputSS_PS : [SS ===>pg PS].
Proof.
  firstorder.
Qed.

Lemma TgetTputSGP_GI : [SGP ===>pg GI].
Proof.
  move => S V l hs hv gt pt SGP s s' v [H1 H2];
  apply (SGP s s v) in H1;
  apply (SGP s s' v) in H2;
  rewrite H1 in H2; inversion H2; reflexivity.
Qed.

Lemma TgetTputSGP_WPG : [SGP ===>pg WPG].
Proof.
  firstorder.
Qed.

Lemma TgetTputSGP_UD : [SGP ===>pg UD].
Proof.
  firstorder.
Qed.

Lemma TgetTputGP_GPG : [GP ===>pg GPG].
Proof.
  move => S V hs hv l gt pt GP s s' v [H1 H2];
  apply GP in H1 as H3;
  rewrite H3 in H2;
  inversion H2;
  rewrite H0 in H1;
  apply H1.
Qed.

Lemma TgetTputGP_PGP : [GP ===>pg PGP].
Proof.
  firstorder.
Qed.

Lemma TgetTputSS_WSS : [SS ===>pg WSS].
Proof.
  firstorder.
Qed.

Lemma TgetTputWPGandSS_GP : [WPG &&& SS ===>pg GP].
Proof.
  move => S V hs hv l gt pt WPG SS s v H;
  case (SS s) => [v' H1];
  apply (WPG s s v' v);
  firstorder.
Qed.

Lemma TgetTputUDandSS_GP : [UD &&& SS ===>pg GP].
Proof.
  move => S V hs hv l gt pt UD SS s v H;
  case (SS s) => [v' H1];
  apply (UD s s v' v);
  firstorder.
Qed.

Lemma TgetTputPGPandUD_GPG : [PGP &&& UD ===>pg GPG].
Proof.
  move => S V hs hv l gt pt PGP UD s s' v [H1 H2];
  move : (UD s s' v v) => H3;
  have H4 := H3 (conj H2 H1);
  move : (PGP s' s v v) => H5;
  have H6 := H5 (conj H4 H1);
  rewrite H2 in H6; inversion H6;
  firstorder.
Qed.

Lemma TgetTputPGPandPS_GP : [PGP &&& PS ===>pg GP].
Proof.
  move => S V hs hv l gt pt PGP PS s v H1;
  case (PS s) => [s' [v' H2]];
  apply (PGP s' s v' v);
  firstorder.
Qed.

Lemma TgetTputWPGandWSS_PGP : [WPG &&& WSS ===>pg PGP].
Proof.
  move => S V hs hv l gt pt WPG WSS s s' v v' [H1 H2];
  case (WSS s' s v) => [v'' H3];
  apply (WPG s' s' v'' v');
  firstorder.
Qed.

Lemma TgetTputUDandWSS_PGP : [UD &&& WSS ===>pg PGP].
Proof.
  move => S V hs hv l gt pt UD WSS s s' v v' [H1 H2];
  case (WSS s' s v) => [v'' H3];
  apply (UD s' s' v'' v');
  firstorder.
Qed.

Lemma TgetTputUDandWSS_GPG : [UD &&& WSS ===>pg GPG].
Proof.
  move => S V hs hv l gt pt UD WSS s s' v [H1 H2];
  case (WSS s s' v) => [v' H3];
  move : (UD s s' v v) => H4;
  have H5 := H4 (conj H2 H1);
  apply H3 in H5;
  move : (UD s s v' v) => H6;
  have H7 := H6 (conj H5 H1);
  rewrite H2 in H7; inversion H7;
  firstorder.
Qed.

Lemma TgetTputWSSandPS_SS : [WSS &&& PS ===>pg SS].
Proof.
  move => S V hs hv l gt pt WSS PS s;
  case (PS s) => [s' [v H1]];
  case (WSS s s' v) => [v' H2];
  firstorder.
Qed.

Lemma TgetTputGP_SS : [GP ===>pg SS].
Proof.
  move => S V hs hv l gt pt GP s;
  case (p_get l s) eqn:H.
  -firstorder.
  -exfalso; apply (gt s) ; firstorder.
Qed.

Lemma TgetTputGPG_WSS : [PGP ===>pg WSS].
Proof.
  move => S V hs hv l gt pt PGP s s' v';
  case (p_get l s) eqn:H1.
  exists (v); move => H2;
  have H3 := (PGP s' s v' v) (conj H2 H1);
  firstorder.
  exfalso; apply (gt s); firstorder.
Qed.

Lemma TgetTputUD_WPG : [UD ===>pg WPG].
Proof.
  move => S V hs hv l gt pt UD s s' v v' [H1 H2];
  case (p_get l s) eqn:H3.
  have H4 := (UD s s' v v0) (conj H1 H3);
  have H5 := (UD s' s v0 v') (conj H4 H2);
  firstorder.
  exfalso; apply (gt s); firstorder.
Qed.

Lemma TgetTputUDandWSS_GP : [UD &&& WSS ===>pg GP].
Proof.
  move => S V hs hv l gt pt HUD HWSS s v H1;
  case (p_put l (s,v)) eqn:H2.
  have H3 := (HUD s s0 v v) (conj H2 H1);
  have H4 := (HWSS s s0 v). destruct H4.
  apply H in H3.
  have H5 := (HUD s s x v) (conj H3 H1).
  rewrite H5 in H2; firstorder. firstorder.
Qed.

Lemma TgetTputGIandGPG_GP : [GI &&& GPG ===>pg GP].
Proof.
  move => S V hs hv l gt pt GI GPG s v H;
  case (p_put l (s,v)) eqn:H1.
  have H2 := (GPG s s0 v) (conj H H1);
  have H3 := (GI s s0 v) (conj H H2);
  firstorder; rewrite H3; reflexivity.
  exfalso;apply (pt s v); firstorder.
Qed.

Lemma TgetTputGPandUDandGInotSGP : ~[GP &&& UD &&& GI ===>pg SGP].
Proof.
  move => H.
  bx_test [tg;tp;gp;ud;gi;notsgp].
  have_tg. by move=> [].
  have_tp. by move => [] [].
  have_gp. by move => [] [].
  have_ud. by move => [] [] [] [];firstorder.
  have_gi. by move => [] [] [];firstorder.
  have_notsgp.
  by move => HW;move:(HW false true true erefl).
  firstorder.
Qed.

Lemma TgetTputGPandUDnotGI : ~[GP &&& UD ===>pg GI].
Proof.
  bx_test [tg;tp;gp;ud;notgi]. 
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gp. by move => [] [].
  have_ud. by move => [] [] [] [] [].  
  have_notgi.
  by move => HW;move: (HW true false true (conj erefl erefl)).
  firstorder.  
Qed.

Lemma TgetTputGIandPGPandWPGnotGPG : ~[GI &&& PGP &&& WPG ===>pg GPG].
Proof.
  move => H.
  bx_test [tg;tp;gi;pgp;wpg;notgpg].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gi. by move => [] [] [];firstorder.
  have_pgp. by move => [] [] [] [];firstorder.  
  have_wpg. by move => [] [] [] [];firstorder.
  have_notgpg. by move => HW;move :(HW false true true (conj erefl erefl)).
  firstorder.
Qed.

Lemma TgetTputGIandSSnotGPG : ~[GI &&& SS ===>pg GPG].
Proof.
  move => H.
  bx_test [tg;tp;gi;ss;notgpg].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gi. by move => [] [] [];firstorder.
  have_ss. rewrite /SS; case=> /=; exists false; firstorder.
  have_notgpg. by move => HW;move : (HW true false true (conj erefl erefl)).
firstorder.
Qed.

Lemma TgetTputGIandUDnotGPG : ~[GI &&& UD ===>pg GPG].
Proof.
  move => H.
  bx_test [tg;tp;gi;ud;notgpg].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gi. by move => [] [] [] ;firstorder.
  have_ud. by move => [] [] [] [] ; firstorder.
  have_notgpg.  by move => HW;move:(HW true false false (conj erefl erefl)).
  firstorder.
Qed.

Lemma TgetTputGIandSSnotPGP : ~[GI &&& SS ===>pg PGP].
Proof.
  move => H.
  bx_test [tg;tp;gi;ss;notpgp].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gi. by move => [] [] [];firstorder.
  have_ss. rewrite /SS ;case => /=. exists true; by []. exists false; by [].
  have_notpgp. by move => HW;move: (HW false false false true (conj erefl erefl)). 
firstorder.
Qed.

Lemma TgetTputGPGandSSnotPGP : ~[GPG &&& SS ===>pg PGP].
Proof.
  move => H.
  bx_test [tg;tp;gpg;ss;notpgp].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gpg. by move => [] [] [];firstorder.
  have_ss. rewrite /SS; case => /=. exists true;by []. exists false ;by [].
  have_notpgp. by  move => HW; move :(HW false false false true (conj erefl erefl)).
  apply HnotPGP; apply H. apply inhabited_bool. apply inhabited_bool. apply HTG.
  apply HTP. apply HGPG. apply HSS.
Qed.

Lemma TgetTputGIandUDnotWSS : ~[GI &&& UD ===>pg WSS].
Proof.
  move => H.
  bx_test [tg;tp;gi;ud;notwss].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gi.  by move => [] [] [];firstorder.
  have_ud. by move => [] [] [] [];firstorder.         
  have_notwss.  by move=> HW; case: (HW true false true) => v /(_ erefl); case: v.  
  firstorder.  
Qed.

Lemma TgetTputGPGandUDnotWSS : ~[GPG &&& UD ===>pg WSS].
Proof.
  move => H.
  bx_test[tg;tp;gpg;ud;notwss].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gpg. by move => [] [] [];firstorder.
  have_ud. by move => [] [] [] [];firstorder.
  have_notwss. by move=> HW; case: (HW true false true) => v /(_ erefl); case: v. 
  apply HnotWSS. apply H. apply inhabited_bool. apply inhabited_bool.  apply HTG. apply HTP.
  apply HGPG. apply HUD.
Qed.

Lemma TgetTputGIandWPGandPGPnotPS : ~[GI &&& WPG &&& PGP ===>pg PS].
Proof.
  move => H.
  bx_test [tg;tp;gi;wpg;pgp;notps].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gi. by move => [] [] [];firstorder.
  have_wpg. by move => [] [] [] [];firstorder.
  have_pgp. by move => [] [] [] [];firstorder.
  have_notps. unfold PS. by  move=> HW ;case: (HW false) => s' [v Hv]; case: s' Hv; case: v.
  firstorder.
Qed.

Lemma TgetTputGPGandWPGandPGPnotPS : ~[GPG &&& WPG &&& PGP ===>pg PS].
Proof.
  move => H.
  bx_test[tg;tp;gpg;wpg;pgp;notps].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gpg. by move => [] [] [];firstorder.
  have_wpg. by move => [] [] [] [];firstorder.
  have_pgp. by move => [] [] [] [];firstorder.
  have_notps.  by  move=> HW ;case: (HW false) => s' [v Hv]; case: s' Hv; case: v.  
  apply HnotPS.  apply H. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HGPG. apply HWPG. apply HPGP.
Qed.

Lemma TgetTputGPnotWPG : ~[GP &&& GI ===>pg WPG].
Proof.
  move => H.
  bx_test [tg;tp;gp;gi;notwpg].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gp. by move => [] [].
  have_gi. by move => [] [] [];firstorder.  
  have_notwpg. unfold WPG.
  by move => HW;move:(HW true false b a (conj erefl erefl)).
  firstorder.
Qed.

End GPfamily.


Section PGfamily.

Lemma TgetTputPG_VD : [PG ===>pg VD].
Proof.
  move => S V hs hv l gt pt PG s s' s'' v v' [H1 H2];
  apply PG in H1;
  apply PG in H2;
  rewrite H1 in H2;
  inversion H2;
  reflexivity.
Qed.

Lemma TgetTputVD_PI : [VD ===>pg PI].
Proof.
  firstorder.
Qed.

Lemma TgetTputPG_GPG : [PG ===>pg GPG].
Proof.
  firstorder.
Qed.

Lemma TgetTputPG_WPG : [PG ===>pg WPG].
Proof.
  move => S V hs hv l gt pt PG s s' v v' [H1 H2];
  apply PG in H1 as H3;
  rewrite H2 in H3;
  inversion H3;
  firstorder.
Qed.

Lemma TgetTputPG_GS : [PG ===>pg GS].
Proof.
  move => S V hs hv l gt PT HPG v;
  pose (s_init := inhab : S);
  pose s_opt := p_put l (s_init, v);
  have H_not_none: s_opt <> None by apply: PT.
  destruct s_opt as [s' | ] eqn:H_put.
  exists s'.
  apply: (HPG s_init s' v).
  exact: H_put.
  done.
Qed.

Lemma TgetTputWPGandPI_PG : [WPG &&& PI ===>pg PG].
Proof.
  move => S V hs hv l gt pt WPG PI s s' v H;
  case (p_get l s') eqn:H1.
  move : (WPG s s' v v0) => H2;
  have H3 := H2 (conj H H1);
  have H4 := (PI s s' v v0) (conj H H3);
  rewrite H4.
  -reflexivity.
  -exfalso; apply (gt s'); apply H1.
Qed.

Lemma TgetTputVDandGSnotGPG : ~[VD &&& GS ===>pg GPG].
Proof.
  move => H.
  bx_test[tg;tp;vd;gs;notgpg].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_vd. by move => [] [] [] [] [];firstorder.
  have_gs. rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_notgpg. by move => HW;move: (HW true false true (conj erefl erefl)).
  apply HnotGPG. apply H. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HVD. apply HGS.
Qed.  

Lemma TgetTputWPGandGSnotGPG : ~[WPG &&& GS ===>pg GPG].
Proof.
  move => H.
  bx_test [tg;tp;wpg;gs;notgpg].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_wpg. by move => [] [] [] [];firstorder.
  have_gs.  rewrite / GS ;case => /=. exists false; firstorder.  exists true;firstorder.
  have_notgpg.  by move => HW;move: (HW true false false (conj erefl erefl)).
  apply HnotGPG. apply H. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HWPG. apply HGS.
Qed.

Lemma TgetTputGPGandVDandGSnotWPG : ~[GPG &&& VD &&& GS ===>pg WPG].
Proof.
  move => H.
  bx_test [tg;tp;gpg;vd;gs;notwpg].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gpg. by move => [] [] [];firstorder.
  have_vd. by move => [] [] [] [] [];firstorder.
  have_gs.  rewrite / GS ;case => /=. exists c; firstorder.  exists a;firstorder.
  have_notwpg. by move => HW;move:(HW a b true false (conj erefl erefl)).
  apply HnotWPG. apply H. firstorder. apply inhabited_bool.
  apply HTG. apply HTP. apply HGPG. apply HVD. apply HGS.
Qed.

Lemma TgetTputGPGandWPGnotGS : ~[GPG &&& WPG ===>pg GS].
Proof.
  move => H.
  bx_test [tg;tp;gpg;wpg;notgs].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gpg. by move => [] [] [] ;firstorder.
  have_wpg. by move => [] [] [] [];firstorder.
  have_notgs. by move=> H_surj; case: (H_surj true) => s; case: s.
  apply HnotGS. apply H. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HGPG. apply HWPG.
Qed.

Lemma TgetTputGPGandVDnotGS : ~[GPG &&& VD ===>pg GS].
Proof.
  move => H.
  bx_test [tg;tp;gpg;vd;notgs].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gpg. by move => [] [] [];firstorder.
  have_vd. by move => [] [] [] [] [];firstorder.
  have_notgs. by move=> H_surj; case: (H_surj true) => s; case: s.
  apply HnotGS. apply H. apply inhabited_bool. apply inhabited_bool.
  apply HTG. apply HTP. apply HGPG. apply HVD.
Qed.

Lemma TgetTputGPGandWPGandGSnotPI : ~[GPG &&& WPG &&& GS ===>pg PI].
Proof.
  move => H.
  bx_test [tg;tp;gpg;wpg;gs;notpi].
  have_tg. by move => [].
  have_tp. by move => [] [].
  have_gpg. by move => [] [] [];firstorder.
  have_wpg. by move => [] [] [] [];firstorder.
  have_gs.  rewrite / GS ;case => /=. exists true; firstorder.  exists false;firstorder.
  have_notpi. unfold PI.
    
Qed.

Lemma TgetTputGPGandGSandPInotVD : ~[GPG &&& GS &&& PI ===>pg VD].
Proof.
  move => H.
  bx_test [tg;tp;gpg;gs;pi;notvd].
Qed.






End PGfamily.

Lemma TputPP_PT : [PP ===>pg PT].
Proof.
  move => S V hs hv l gt pt PP s s' v H;
  case (p_put l (s,v)) eqn:H1;
  case (p_put l (s',v)) eqn:H3;
  inversion H;
  rewrite H2 in H1.
  have H4 := (PP s s' s1 v v)(conj H1 H3);
  rewrite H4 in H1; firstorder.
  exfalso;apply(pt s' v);firstorder.
Qed.

Lemma TgetTputPT_WSS : [PT ===>pg WSS].
Proof.
  move => S V hs hv l gt pt PT s s' v';
  exists(v');
  firstorder.
Qed.


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

