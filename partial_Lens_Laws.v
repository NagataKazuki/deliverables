Require Import Setoid.

Section PartialLens.

Variable S V : Type.
Variable get : S -> V.
Variable put : S * V -> S.
Variable p_get : S -> option V.
Variable p_put : S * V -> option S.

Variable Pp : (S -> option V) -> (S * V -> option S) -> Prop.

Definition P_PtoT :
  (S -> V) -> (S * V -> S) -> Prop :=
  fun get put =>
    Pp (fun s => Some (get s))
       (fun sv => Some (put sv)).

Theorem Pp_Pt :
  Pp (fun s => Some (get s))
     (fun sv => Some (put sv))
  <-> P_PtoT get put.
Proof.
  unfold P_PtoT.
  split.
  -intro H. apply H.
  -intro H. apply H.
Qed.

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
    p_put(s', v) =Some s.

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

Theorem pSPG_pPG_pPP : pSGP/\pPG->pPP.
Proof.
  unfold pSGP. unfold pPG.
  unfold pPP.
  intros [H1 H2] s s' s'' v v' [H3 H4].
  

Definition get_total : Prop :=
  forall (s : S), p_get s <> None.
Definition put_total : Prop :=
  forall (s : S) (v : V), p_put (s, v) <> None.

Theorem Ss : pPG -> pVD.
Proof.
  unfold pPG. unfold pVD.
  intros H s s' s'' v v' [H1 H2] .
  apply H in H1. apply H in H2.
  rewrite H1 in H2.
