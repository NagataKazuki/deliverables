Require Import Setoid.
From mathcomp
Require Import ssreflect.

Variable S V : Type.
Variable p_get : S -> option V.
Variable p_put : S * V -> option S.

Section PartialLensLaws.

Definition pSGP : Prop :=
  forall (s s' : S) (v : V),
    p_get s' = Some v ->
    p_put (s, v) = Some s'.

Definition pGP : Prop :=
  forall (s : S) (v : V),
    p_get s = Some v ->
    p_put (s, v) = Some s.

Definition pPG : Prop :=
  forall (s s' : S) (v : V),
    p_put (s, v) = Some s' ->
    p_get s' = Some v.

Definition pPP : Prop :=
  forall (s s' s'' : S) (v v' : V),
    p_put(s, v) = Some s' /\
    p_put(s', v') = Some s'' ->
    p_put(s, v') = Some s''.

Definition pWPG : Prop :=
  forall (s s' : S) (v v' : V),
    p_put(s, v) = Some s' /\
    p_get s' = Some v' ->
    p_put(s, v') = Some s'.

Definition pPGP : Prop :=
  forall (s s' : S) (v v' : V),
    p_put(s, v) = Some s' /\
    p_get s' = Some v' ->
    p_put(s', v') = Some s'.

Definition pGPG : Prop :=
  forall (s s' : S) (v : V),
    p_get s = Some v /\
    p_put(s, v) = Some s' ->
    p_get s' = Some v.

Definition pUD : Prop :=
  forall (s s' : S) (v v' : V),
    p_put(s, v) = Some s' /\
    p_get s = Some v' ->
    p_put(s', v') = Some s.

Definition pGI : Prop :=
  forall (s s' : S) (v : V),
    p_get s = Some v /\ p_get s' = Some v ->
    Some s = Some s'.

Definition pGS : Prop :=
  forall (v : V) ,exists (s : S),
    p_get s = Some v.

Definition pPT : Prop :=
  forall (s s' : S) (v : V),
    p_put(s, v) = Some s' ->
    p_put(s', v) =Some s'.

Definition pSS : Prop :=
  forall (s : S),exists (v : V),
    p_put(s, v) = Some s.

Definition pWSS : Prop :=
  forall (s s' : S) (v' : V),exists (v : V),
    p_put(s', v') = Some s ->
    p_put(s , v) = Some s.

Definition pPS : Prop :=
  forall (s : S),exists (s' : S) (v : V),
    p_put(s', v) = Some s.

Definition pVD : Prop :=
  forall (s s' s'' : S) (v v' : V),
    p_put(s,v) = Some s'' /\ p_put(s', v') = Some s'' ->
    v = v'.

Definition pPI : Prop :=
  forall (s s' : S) (v v' : V),
    p_put(s, v) = Some s' /\ p_put(s, v') = Some s' ->
    v = v'.

End PartialLensLaws.

Ltac unfold_laws :=
  rewrite / pSGP /pGP / pPG /pPP
          / pWPG / pUD / pGPG / pPGP
          / pGS / pGI / pPS / pGS
          / pSS / pWSS / pVD / pPI.

(*Pget means "get is a partial function",also Tget means "get is a total function"*)
(*Pput means "put is a partial function",also Tput means "put is a total function"*)


(*PPInplication means Implications when get and put are both partial functions*)
Section PPImplication.

Section GPFamily.

Theorem PgetPputSGP_GP : pSGP -> pGP.
Proof.
  firstorder.
Qed.

Theorem PgetPputSS_PS : pSS -> pPS.
Proof.
  firstorder.
Qed.

Theorem PgetPputSGP_GI : pSGP -> pGI.
Proof.
  move => SGP s s' v [H1 H2];
  apply (SGP s s v) in H1;
  apply (SGP s s' v) in H2;
  rewrite H1 in H2;
  apply H2.
Qed.

Theorem PgetPputSGP_WPG : pSGP -> pWPG.
Proof.
  firstorder.
Qed.

Theorem PgetPputSGP_UD : pSGP -> pUD.
Proof.
  firstorder.
Qed.

Theorem PgetPputGP_GPG : pGP -> pGPG.
Proof.
  move => GP s s' v [H1 H2];
  apply GP in H1 as H3;
  rewrite H3 in H2;
  inversion H2;
  rewrite H0 in H1;
  apply H1.
Qed.

Theorem PgetPputGP_PGP : pGP -> pPGP.
Proof.
  firstorder.
Qed.

Theorem PgetPputSS_WSS : pSS -> pWSS.
Proof.
  move => SS s s' v';
  case (SS s) => [v SS1];
  exists (v);
  intros H1;
  firstorder.
Qed.

Theorem PgetPputWPGandSS_GP : pWPG /\ pSS -> pGP.
Proof.
  move => [WPG SS] s v H;
  case (SS s) => [v' H1];
  apply (WPG s s v' v);
  firstorder.
Qed.

Theorem PgetPputUDandSS_GP : pUD /\ pSS -> pGP.
Proof.
  move => [UD SS] s v H;
  case (SS s) => [v' H1];
  apply (UD s s v' v);
  firstorder.
Qed.

Theorem PgetPputPGPandUD_GPG : pPGP /\ pUD -> pGPG.
Proof.
  move => [PGP UD] s s' v [H1 H2];
  move : (UD s s' v v) => H3;
  have H4 := H3 (conj H2 H1);
  move : (PGP s' s v v) => H5;
  have H6 := H5 (conj H4 H1);
  rewrite H2 in H6; inversion H6;
  firstorder.
Qed.


Theorem PgetPputPGPandPS_GP : pPGP /\ pPS -> pGP.
Proof.
  intros [PGP PS] s v H1;
  case (PS s) => [s' [v' H2]];
  apply (PGP s' s v' v);
  firstorder.
Qed.

Theorem PgetPputWPGandWSS_PGP : pWPG /\ pWSS -> pPGP.
Proof.
  intros [WPG WSS] s s' v v' [H1 H2];
  case (WSS s' s v) => [v'' H3];
  apply (WPG s' s' v'' v');
  firstorder.
Qed.

Theorem PgetPputUDandWSS_PGP : pUD /\ pWSS -> pPGP.
Proof.
  move => [UD WSS] s s' v v' [H1 H2];
  case (WSS s' s v) => [v'' H3];
  apply (UD s' s' v'' v');
  firstorder.
Qed.

Theorem PgetPputUDandWSS_GPG : pUD /\ pWSS -> pGPG.
Proof.
  move => [UD WSS] s s' v [H1 H2];
  case (WSS s s' v) => [v' H3];
  move : (UD s s' v v) => H4;
  have H5 := H4 (conj H2 H1);
  apply H3 in H5;
  move : (UD s s v' v) => H6;
  have H7 := H6 (conj H5 H1);
  rewrite H2 in H7; inversion H7;
  firstorder.
Qed.

Theorem PgetPputWSSandPS_SS : pWSS /\ pPS -> pSS.
Proof.
  move => [WSS PS] s;
  case (PS s) => [s' [v H1]];
  case (WSS s s' v) => [v' H2];
  firstorder.
Qed.

End GPFamily.

Section PGFamily.

Theorem PgetPputPG_VD : pPG -> pVD.
Proof.
  move => PG s s' s'' v v' [H1 H2];
  apply PG in H1;
  apply PG in H2;
  rewrite H1 in H2;
  inversion H2;
  reflexivity.
Qed.

Theorem PgetPputVD_PI : pVD -> pPI.
Proof.
  firstorder.
Qed.

Theorem PgetPputPG_GPG : pPG -> pGPG.
Proof.
  firstorder.
Qed.

Theorem PgetPputPG_WPG : pPG -> pWPG.
Proof.
  move => PG s s' v v' [H1 H2];
  apply PG in H1 as H3;
  rewrite H2 in H3;
  inversion H3;
  firstorder.
Qed.

End PGFamily.

Section PPFamily.

Theorem PgetPputPT_WSS : pPT -> pWSS.
Proof.
  move => PT s s' v';
  exists (v');
  firstorder.
Qed.

End PPFamily.

Theorem PgetPputPIandPT_VD : pPI /\ pPT -> pVD.
Proof.
  move => [PI PT] s s' s'' v v' [H1 H2];
  apply (PI s'' s'' v v');
  firstorder.
Qed.

Theorem PgetPputSGPandGS_PG : pSGP /\ pGS -> pPG.
Proof.
  unfold pSGP;unfold pGS;unfold pPG.
  move => [SGP GS] s s' v H;
  case (GS v) => [s'' H1];
  apply (SGP s s'' v) in H1 as H2;
  rewrite H in H2;
  inversion H2;
  firstorder.
Qed.
Theorem PgetPputWSSandVD_PT : pWSS /\ pVD -> pPT.
Proof.
  move => [WSS VD] s s' v H;
  case (WSS s' s v) => [v' H1];
  move :(H1 H) => H2;
  have H3 : v = v';
  move : (VD s s' s' v v');
  firstorder;
  rewrite H3;
  apply H2.
Qed.

Theorem PgetPputPGPandPP_WPG : pPGP /\ pPP -> pWPG.
Proof.
  move => [PGP PP] s s' v v' [H1 H2];
  apply (PP s s' s' v v');
  split;
  firstorder;
  apply (PGP s s' v v');
  firstorder.
Qed.

Theorem PgetPputPGPandPG_PT : pPGP /\ pPG -> pPT.
Proof.
  move => [PGP PG] s s' v H1;
  apply PG in H1 as H2;
  move : (PGP s s' v v) => H3;
  have H4 := H3 (conj H1 H2);
  apply H4.
Qed.

End PPImplication.

Variable get : S -> V.
Variable put : S * V -> S.
Variable PartialProp : (S -> option V) -> (S * V -> option S) -> Prop.

Definition get_total : Prop :=
  forall (s : S), p_get s <> None.

Definition put_total : Prop :=
  forall (s : S) (v : V), p_put (s, v) <> None.

(*Props of partial functions contain props of total functions*)
Definition Prop_PartialtoTotal :
  (S -> V) -> (S * V -> S) -> Prop :=
  fun get put =>
    PartialProp (fun s => Some (get s))
       (fun sv => Some (put sv)).

Theorem PartialProptoTotalProp :
  PartialProp (fun s => Some (get s))
     (fun sv => Some (put sv))
  <-> Prop_PartialtoTotal get put.
Proof.
  unfold Prop_PartialtoTotal.
  firstorder;
  firstorder.
Qed.

Section PGImplication.

