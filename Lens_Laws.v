Require Import Setoid.
Module Export Lens_Laws.

Section Lens.

Variable S V : Type.
Variable get : S -> V.
Variable put : S * V -> S.

Definition SGP : Prop :=
  forall (s s' : S),
    put(s, get s') = s'.

Definition GP : Prop :=
  forall (s : S),
    put(s, get s) = s.

Definition PG : Prop :=
  forall (s : S) (v : V),
    get (put(s , v))= v.

Definition PP : Prop :=
  forall (s : S) (v v' : V),
    put(put(s,v),v') = put(s,v').

Definition WPG : Prop :=
  forall (s : S) (v : V),
    put(s,get(put(s,v))) = put(s,v).

Definition PGP : Prop :=
  forall (s : S) (v : V),
    put(put(s,v),get(put(s,v))) = put(s,v).

Definition GPG : Prop :=
  forall (s : S),
    get(put(s,get(s))) = get s.

Definition UD : Prop :=
  forall (s : S) (v : V),
    put(put(s,v),get(s)) = s.

Definition GI : Prop :=
  forall (s s' : S),
    get s = get s' -> s = s'.

Definition GS : Prop :=
  forall (v : V) , exists (s : S),
    get s = v.

Definition PT : Prop :=
  forall (s : S) (v : V),
    put(put(s,v),v) = put(s,v).

Definition SS : Prop :=
  forall (s : S), exists (v : V),
    put(s,v) = s.

Definition WSS : Prop :=
  forall (s : S) (v' : V) , exists (v : V),
    put(put(s, v'), v) = put(s, v').

Definition VD : Prop :=
  forall (s s' : S) (v v' : V),
    put(s,v) = put(s',v') -> v = v'.

Definition PI : Prop :=
  forall (s : S) (v v' : V),
    put(s,v) = put(s,v') -> v = v'.

Definition PS : Prop :=
  forall (s : S) ,exists (s' : S) (v : V),
    put(s',v) = s.

Variable s0 : S.

Theorem SGP_GP : SGP -> GP.
Proof.
  unfold SGP. unfold GP.
  intros H s. apply H.
Qed.

Theorem GP_SS : GP -> SS.
Proof.
  unfold GP. unfold SS.
  eauto.
Qed.

Theorem SS_PS : SS -> PS.
Proof.
  unfold SS. unfold PS.
  eauto.
Qed.

Theorem SGP_GI : SGP -> GI.
Proof.
  unfold SGP. unfold GI.
  intros H s s' H1. rewrite <- (H s s).
  rewrite <- (H s s').
  rewrite -> H1. reflexivity.
Qed.

Theorem SGP_UD : SGP -> UD.
Proof.
  unfold SGP. unfold UD.
  auto.
Qed.

Theorem UD_WPG : UD -> WPG.
Proof.
  unfold UD. unfold WPG.
  intros H s v. rewrite <- (H s v) at 1.
  apply H.
Qed.

Theorem UD_PS : UD -> PS.
Proof.
  unfold UD. unfold PS.
  intros H s. exists (put (s, get s)), (get s).
  apply H.
Qed.

Theorem GP_GPG : GP -> GPG.
Proof.
  unfold GP. unfold GPG.
  intros H s. rewrite -> H.
  reflexivity.
Qed.

Theorem GP_PGP : GP -> PGP.
Proof.
  unfold GP. unfold PGP.
  intros H s v. rewrite -> H.
  reflexivity.
Qed.

Theorem SS_WSS : SS -> WSS.
Proof.
  unfold SS. unfold WSS.
  auto.
Qed.

Theorem PGP_WSS : PGP -> WSS.
Proof.
  unfold PGP. unfold WSS.
  intros H s v'. eauto.
Qed.

Theorem PGP_PS_GP : PGP /\ PS -> GP.
Proof.
  unfold PGP. unfold PS. unfold GP.
  intros [H1 H2] s.
  destruct (H2 s) as [s' [v H]].
  rewrite <- H.
  apply H1.
Qed.

Theorem SS_WPG_GP : SS /\ WPG -> GP.
Proof.
  unfold SS. unfold WPG. unfold GP.
  intros [H1 H2] s. destruct (H1 s) as [v H].
  rewrite <- H at 2. rewrite H2. apply H.
Qed.

Theorem GI_GPG_GP : GI /\ GPG -> GP.
Proof.
  unfold GI. unfold GPG. unfold GP.
  intros [H1 H2] s. auto.
Qed.

Theorem WPG_WSS_PGP : WPG /\ WSS -> PGP.
Proof.
  unfold WPG. unfold WSS. unfold PGP.
  intros [H1 H2] s v. 
  destruct (H2 s v) as [v' H].
  rewrite <- H. Admitted.

Theorem UD_WSS_GP : UD /\ WSS -> GP.
Proof.
  unfold UD. unfold WSS. unfold GPG.
  intros [H1 H2] s. 
  destruct (H2 s (get s)) as [v H].
  rewrite <- H. Admitted.

Theorem PS_WSS_SS : PS /\ WSS -> SS.
Proof.
  unfold PS. unfold WSS. unfold SS.
  intros [H1 H2] s.
  destruct (H1 s) as [s' [v' H3]].
  destruct (H2 s' v') as [v H4].
  rewrite H3 in H4.
  exists v.
  apply H4.
Qed.


Theorem PG_VD : PG -> VD.
Proof.
  unfold PG. unfold VD.
  intros H s s' v v' H2.
  rewrite <- (H s v).
  rewrite <- (H s' v').
  rewrite -> H2. reflexivity.
Qed.

Theorem VD_PI : VD -> PI.
Proof.
  unfold VD. unfold PI.
  intros H s v v' H1.
  apply (H s s v v').
  apply H1.
Qed.

Theorem PG_WPG : PG -> WPG.
Proof.
  unfold PG. unfold WPG.
  intros H s v.
  rewrite H at 1.
  reflexivity.
Qed.

Theorem PG_GPG : PG -> GPG.
Proof.
  unfold PG. unfold GPG.
  intros H s. auto.
Qed.


Theorem PG_GS : PG -> GS.
Proof.
  unfold PG. unfold GS.
  intros H v. exists (put(s0,v)).
  apply H.
Qed.

Theorem PI_WPG_PG : PI /\ WPG -> PG.
Proof.
  unfold PI. unfold WPG. unfold PG.
  intros [H1 H2] s v.
  apply (H1 s (get(put(s,v))) v ) in H2.
  apply H2.
Qed.

Theorem PP_PT : PP -> PT.
Proof.
  unfold PP. unfold PT.
  intros H s v. auto.
Qed.

Theorem PT_WSS : PT -> WSS.
Proof.
  unfold PT. unfold WSS.
  intros H s v'. exists (v').
  apply H.
Qed.


Theorem PI_PT_VD : PI /\ PT -> VD.
Proof.
  unfold PI. unfold PT. unfold VD.
  intros [H1 H2] s s' v v' H. apply (H1 (put(s,v)) v v').
  rewrite H at 2.
  rewrite <- H2 in H. rewrite <- (H2 s' v') in H.
  apply H.
Qed.

Theorem VD_PGP_PG : VD /\ PGP -> PG.
Proof.
  unfold VD. unfold PGP. unfold PG.
  intros [H1 H2] s v.
  apply (H1 (put (s, v)) s (get (put (s, v))) v).
  apply H2.
Qed.

Theorem GI_PG_SGP : GI /\ PG -> SGP.
Proof.
  unfold GI. unfold PG. unfold SGP.
  intros [H1 H2] s s'. auto.
Qed.

Theorem GS_SGP_PG : GS /\ SGP -> PG.
Proof.
  unfold GS. unfold SGP. unfold PG.
  intros [H1 H2] s v. destruct (H1 v) as [s' H].
  rewrite <- H. rewrite H2. reflexivity.
Qed.



Theorem SGP_PG_PP : SGP/\ PG -> PP.
Proof.
  unfold SGP. unfold PG.
  unfold PP.
  intros [H1 H2] s v v'.
  rewrite <- (H1 s (put(put(s,v),v'))).
  rewrite H2. reflexivity.
Qed.

Theorem SGP_PI_PP : SGP/\PI -> PP.
Proof.
  unfold SGP. unfold PI.
  unfold PP.
  intros [H1 H2] s v v'.
  rewrite <- (H1 s (put(put(s,v),v'))).
  rewrite <- (H1 s (put(s,v'))).
  Admitted.

Theorem GP_PP_UD : GP /\ PP -> UD.
Proof.
  unfold GP. unfold PP. unfold UD.
  intros [H1 H2] s v. 
  rewrite H2. rewrite H1. reflexivity.
Qed.

Theorem PGP_PP_WPG : PGP /\ PP -> WPG.
Proof.
  unfold PGP. unfold PP. unfold WPG.
  intros [H1 H2] s v.
  rewrite <- (H1 s v) at 2.
  rewrite H2. reflexivity.
Qed.

Theorem WSS_VD_PT : WSS /\ VD -> PT.
Proof.
  unfold WSS. unfold VD. unfold PT.
  intros [H1 H2] s v.
  destruct (H1 s v) as [v' H].
  rewrite <- H at 2.
  apply H2 in H.
  rewrite <- H at 2. reflexivity.
Qed.


Theorem PG_PGP_PT : PG /\ PGP -> PT.
Proof.
  unfold PG. unfold PGP. unfold PT.
  intros [H1 H2] s v.
  rewrite <- (H2 s v) at 2.
  rewrite H1. reflexivity.
Qed.


Theorem PS_WSS_PT : PS /\ WSS -> PT.
Proof.
  unfold PS. unfold WSS. unfold PT.
  intros [H1 H2] s v.
  destruct (H1 s) as [s' [v' H3]].
  destruct (H2 s' v') as [v'' H4].
  rewrite <- H3. Admitted.

End Lens.

End Lens_Laws.          