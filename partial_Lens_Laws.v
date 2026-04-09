Require Import Setoid.
From mathcomp
Require Import all_ssreflect.
From mathcomp Require Import ssreflect ssrfun ssrbool.
From Hammer Require Import Tactics.
From Hammer Require Import Hammer.


Record Lens (S V : Type):= mkLens{
  p_get : S -> option V;
  p_put : S * V -> option S;
}.

Arguments p_get {S V} _ _.
Arguments p_put {S V} _ _.


Class inhabited (T : Type) := Inhabited { inhab : T }.
Instance inhabited_bool : inhabited bool :=
  {| inhab := true |}.
Instance inhabited_nat : inhabited nat :=
  {| inhab := 0 |}.


Section LensLaws.

Variable (S V : Type) (l : Lens S V).

Notation get := l.(p_get).
Notation put := l.(p_put).

Definition SGP : Prop :=
  forall (s s' : S) (v : V),
    get s' = Some v ->
    put (s, v) = Some s'.

Definition GP : Prop :=
  forall (s : S) (v : V),
    get s = Some v ->
    put (s, v) = Some s.

Definition PG : Prop :=
  forall (s s' : S) (v : V),
    put (s, v) = Some s' ->
    get s' = Some v.

Definition PP : Prop :=
  forall (s s' s'' : S) (v v' : V),
    put(s, v) = Some s' /\
    put(s', v') = Some s'' ->
    put(s, v') = Some s''.

Definition WPG : Prop :=
  forall (s s' : S) (v v' : V),
    put(s, v) = Some s' /\
    get s' = Some v' ->
    put(s, v') = Some s'.

Definition PGP : Prop :=
  forall (s s' : S) (v v' : V),
    put(s, v) = Some s' /\
    get s' = Some v' ->
    put(s', v') = Some s'.

Definition GPG : Prop :=
  forall (s s' : S) (v : V),
    get s = Some v /\
    put(s, v) = Some s' ->
    get s' = Some v.

Definition UD : Prop :=
  forall (s s' : S) (v v' : V),
    put(s, v) = Some s' /\
    get s = Some v' ->
    put(s', v') = Some s.

Definition GI : Prop :=
  forall (s s' : S) (v : V),
    get s = Some v /\ get s' = Some v ->
    Some s = Some s'.

Definition GS : Prop :=
  forall (v : V) ,exists (s : S),
    get s = Some v.

Definition PT : Prop :=
  forall (s s' : S) (v : V),
    put(s, v) = Some s' ->
    put(s', v) =Some s'.

Definition SS : Prop :=
  forall (s : S),exists (v : V),
    put(s, v) = Some s.

Definition WSS : Prop :=
  forall (s s' : S) (v' : V),exists (v : V),
    put(s', v') = Some s ->
    put(s , v) = Some s.

Definition PS : Prop :=
  forall (s : S),exists (s' : S) (v : V),
    put(s', v) = Some s.

Definition VD : Prop :=
  forall (s s' s'' : S) (v v' : V),
    put(s,v) = Some s'' /\ put(s', v') = Some s'' ->
    v = v'.

Definition PI : Prop :=
  forall (s s' : S) (v v' : V),
    put(s, v) = Some s' /\ put(s, v') = Some s' ->
    v = v'.

End LensLaws.

Notation "[ L1 &&& .. &&& Ln ===> L ]" :=
 (forall (S V : Type) `{inhabited S} `{inhabited V} (l : Lens S V),
   L1 S V l -> .. (Ln S V l -> L S V l) .. )
  (at level 60, format "[ L1  &&&  ..  &&&  Ln  ===>  L ]").

(*Pget means "get is a partial function",also Tget means "get is a total function"*)
(*Pput means "put is a partial function",also Tput means "put is a total function"*)

(*PPInplication means Implications when get and put are both partial functions*)
Section PPImplication.

Section GPFamily.

Lemma PgetPputSGP_GP : [SGP ===> GP].
Proof.
  firstorder.
Qed.

Lemma PgetPputSS_PS : [SS ===> PS].
Proof.
  firstorder.
Qed.

Theorem PgetPputSGP_GI : [SGP ===> GI].
Proof.
  move => S V l hs hv SGP s s' v [H1 H2].
  apply (SGP s s v) in H1;
  apply (SGP s s' v) in H2;
  rewrite H1 in H2;
  apply H2.
Qed.

Theorem PgetPputSGP_WPG : [SGP ===> WPG].
Proof.
  firstorder.
Qed.

Theorem PgetPputSGP_UD : [SGP ===> UD].
Proof.
  firstorder.
Qed.

Theorem PgetPputGP_GPG : [GP ===> GPG].
Proof.
  move => S V hs hv l GP s s' v [H1 H2];
  apply GP in H1 as H3;
  rewrite H3 in H2;
  inversion H2;
  rewrite H0 in H1;
  apply H1.
Qed.

Theorem PgetPputGP_PGP : [GP ===> PGP].
Proof.
  firstorder.
Qed.

Theorem PgetPputSS_WSS : [SS ===> WSS].
Proof.
  move => S V hs hv l SS s s' v';
  case (SS s) => [v SS1];
  firstorder.
Qed.

Theorem PgetPputWPGandSS_GP : [WPG &&& SS ===> GP].
Proof.
  move => S V hs hv l WPG SS s v H;
  case (SS s) => [v' H1];
  apply (WPG s s v' v);
  firstorder.
Qed.

Theorem PgetPputUDandSS_GP : [UD &&& SS ===> GP].
Proof.
  move => S V hs hv l UD SS s v H;
  case (SS s) => [v' H1];
  apply (UD s s v' v);
  firstorder.
Qed.

Theorem PgetPputPGPandUD_GPG : [PGP &&& UD ===> GPG].
Proof.
  move => S V hs hv l PGP UD s s' v [H1 H2];
  move : (UD s s' v v) => H3;
  have H4 := H3 (conj H2 H1);
  move : (PGP s' s v v) => H5;
  have H6 := H5 (conj H4 H1);
  rewrite H2 in H6; inversion H6;
  firstorder.
Qed.


Theorem PgetPputPGPandPS_GP : [PGP &&& PS ===> GP].
Proof.
  move => S V hs hv l PGP PS s v H1;
  case (PS s) => [s' [v' H2]];
  apply (PGP s' s v' v);
  firstorder.
Qed.

Theorem PgetPputWPGandWSS_PGP : [WPG &&& WSS ===> PGP].
Proof.
  move => S V hs hv l WPG WSS s s' v v' [H1 H2];
  case (WSS s' s v) => [v'' H3];
  apply (WPG s' s' v'' v');
  firstorder.
Qed.

Theorem PgetPputUDandWSS_PGP : [UD &&& WSS ===> PGP].
Proof.
  move => S V hs hv l UD WSS s s' v v' [H1 H2];
  case (WSS s' s v) => [v'' H3];
  apply (UD s' s' v'' v');
  firstorder.
Qed.

Theorem PgetPputUDandWSS_GPG : [UD &&& WSS ===> GPG].
Proof.
  move => S V hs hv l UD WSS s s' v [H1 H2];
  case (WSS s s' v) => [v' H3];
  move : (UD s s' v v) => H4;
  have H5 := H4 (conj H2 H1);
  apply H3 in H5;
  move : (UD s s v' v) => H6;
  have H7 := H6 (conj H5 H1);
  rewrite H2 in H7; inversion H7;
  firstorder.
Qed.

Theorem PgetPputWSSandPS_SS : [WSS &&& PS ===> SS].
Proof.
  move => S V hs hv l WSS PS s;
  case (PS s) => [s' [v H1]];
  case (WSS s s' v) => [v' H2];
  firstorder.
Qed.

End GPFamily.

Section PGFamily.

Theorem PgetPputPG_VD : [PG ===> VD].
Proof.
  move => S V hs hv l PG s s' s'' v v' [H1 H2];
  apply PG in H1;
  apply PG in H2;
  rewrite H1 in H2;
  inversion H2;
  reflexivity.
Qed.

Theorem PgetPputVD_PI : [VD ===> PI].
Proof.
  firstorder.
Qed.

Theorem PgetPputPG_GPG : [PG ===> GPG].
Proof.
  firstorder.
Qed.

Theorem PgetPputPG_WPG : [PG ===> WPG].
Proof.
  move => S V hs hv l PG s s' v v' [H1 H2];
  apply PG in H1 as H3;
  rewrite H2 in H3;
  inversion H3;
  firstorder.
Qed.

End PGFamily.

Section PPFamily.

Theorem PgetPputPT_WSS : [PT ===> WSS].
Proof.
  move => S V hs hv l PT s s' v';
  exists (v');
  firstorder.
Qed.

End PPFamily.

Theorem PgetPputPIandPT_VD : [PI &&& PT ===> VD].
Proof.
  move => S V l hs hv PI PT s s' s'' v v' [H1 H2];
  apply (PI s'' s'' v v');
  firstorder.
Qed.

Theorem PgetPputSGPandGS_PG : [SGP &&& GS ===> PG].
Proof.
  move => S V hs hv l SGP GS s s' v H;
  case (GS v) => [s'' H1];
  apply (SGP s s'' v) in H1 as H2;
  rewrite H in H2;
  inversion H2;
  firstorder.
Qed.

Theorem PgetPputSGPandGS_PP : [SGP &&& GS ===> PP].
Proof.
  move => S V hs hv l HSGP HGS s s' s'' v v' [H1 H2].
  case (HGS v') => [s''' H3].
  apply (HSGP s' s''' v') in H3 as H4;
  rewrite H2 in H4; inversion H4;
  apply HSGP; firstorder.
Qed.

Theorem PgetPputWSSandVD_PT : [WSS &&& VD ===> PT].
Proof.
  move => S V hs hv l WSS VD s s' v H;
  case (WSS s' s v) => [v' H1];
  move :(H1 H) => H2;
  have H3 : v = v';
  move : (VD s s' s' v v');
  firstorder;
  rewrite H3;
  apply H2.
Qed.

Theorem PgetPputPGPandPP_WPG : [PGP &&& PP ===> WPG].
Proof.
  move => S V hs hv l PGP PP s s' v v' [H1 H2];
  apply (PP s s' s' v v');
  split;
  firstorder;
  apply (PGP s s' v v');
  firstorder.
Qed.

Theorem PgetPputPGPandPG_PT : [PGP &&& PG ===> PT].
Proof.
  move => S V hs hv l PGP PG s s' v H1;
  apply PG in H1 as H2;
  move : (PGP s s' v v) => H3;
  have H4 := H3 (conj H1 H2);
  apply H4.
Qed.

End PPImplication.

Section Partial.

Variables S V : Type.
Variable p_get : S -> option V.
Variable p_put : S * V -> option S.

Variable PartialProp :
  (S -> option V) -> (S * V -> option S) -> Prop.

Definition get_total : Prop :=
  forall s : S , p_get s <> None.

Definition put_total : Prop :=
  forall s : S, forall v : V, p_put (s, v) <> None.
Section Total.

Variable get : S -> V.
Variable put : S * V -> S.
Definition Prop_PartialtoTotal : Prop :=
  PartialProp
    (fun s => Some (get s))
    (fun sv => Some (put sv)).
Theorem PartialProptoTotalProp :
  PartialProp
    (fun s => Some (get s))
    (fun sv => Some (put sv))
  <-> Prop_PartialtoTotal.
Proof.
  tauto.
Qed.

End Total.
End Partial.
Definition GetTotal (S V : Type) (l : Lens S V) : Prop :=
  forall s : S, l.(p_get) s <> None.

Definition PutTotal (S V : Type) (l : Lens S V) : Prop :=
  forall (s : S) (v : V), l.(p_put) (s,v)<> None.

Notation "[ L1 &&& .. &&& Ln ===>g L ]" :=
  (forall (S V : Type) `{inhabited S} `{inhabited V} (l : Lens S V),
     GetTotal S V l ->
     L1 S V l -> .. (Ln S V l -> L S V l) .. )
  (at level 60,
   format "[ L1  &&&  ..  &&&  Ln  ===>g  L ]").

Notation "[ L1 &&& .. &&& Ln ===>p L ]" :=
  (forall (S V : Type) `{inhabited S} `{inhabited V} (l : Lens S V),
     PutTotal S V l -> L1 S V l -> .. (Ln S V l -> L S V l) .. )
  (at level 60,
   format "[ L1  &&&  ..  &&&  Ln  ===>p L ]").

Notation "[ L1 &&& .. &&& Ln ===>pg L ]" :=
  (forall (S V : Type) `{inhabited S} `{inhabited V} (l : Lens S V),
     GetTotal S V l -> PutTotal S V l-> L1 S V l -> .. (Ln S V l -> L S V l) .. )
  (at level 60,
   format "[ L1  &&&  ..  &&&  Ln  ===>pg L ]").


Lemma TgetPputGP_SS : [GP ===>g SS].
Proof.
  move => S V hs hv l gt GP s.
  case (p_get l s) eqn:H.
  -firstorder.
  -exfalso; apply (gt s) ; firstorder.
Qed.

Lemma TgetPputGPG_WSS : [PGP ===>g WSS].
Proof.
  move => S V hs hv l gt PGP s s' v';
  case (p_get l s) eqn:H1.
  exists (v); move => H2;
  have H3 := (PGP s' s v' v) (conj H2 H1);
  firstorder.
  exfalso; apply (gt s); firstorder.
Qed.

Lemma TgetPputUD_WPG : [UD ===>g WPG].
Proof.
  move => S V hs hv l gt UD s s' v v' [H1 H2];
  case (p_get l s) eqn:H3.
  have H4 := (UD s s' v v0) (conj H1 H3);
  have H5 := (UD s' s v0 v') (conj H4 H2);
  firstorder.
  exfalso; apply (gt s); firstorder.
Qed.


Lemma TgetPputWPGandPI_PG : [WPG &&& PI ===>g PG].
Proof.
  move => S V hs hv l gt WPG PI s s' v H;
  case (p_get l s') eqn:H1.
  move : (WPG s s' v v0) => H2;
  have H3 := H2 (conj H H1);
  have H4 := (PI s s' v v0) (conj H H3);
  rewrite H4.
  -reflexivity.
  -exfalso; apply (gt s'); apply H1.
Qed.

Lemma TgetPputPGPandVD_PG : [PGP &&& VD ===>g PG].
Proof.
  move => S V hs hv l gt PGP VD s s' v H;
  case (p_get l s') eqn:H1.
  have H2 := (PGP s s' v v0) (conj H H1);
  have H3 := (VD s s' s' v v0) (conj H H2);
  rewrite H3; reflexivity.
  exfalso; apply (gt s'); firstorder.
Qed.

Lemma PgetTputGIandGPG_GP : [GI &&& GPG ===>p GP].
Proof.
  move => S V hs hv l pt GI GPG s v H;
  case (p_put l (s,v)) eqn:H1.
  have H2 := (GPG s s0 v) (conj H H1);
  have H3 := (GI s s0 v) (conj H H2);
  firstorder.
  exfalso;apply (pt s v); firstorder.
Qed.

Lemma PgetTputPG_GS : [PG ===>p GS].
Proof.
  move => S V hs hv l PT HPG v.
  pose (s_init := inhab : S).
  pose s_opt := p_put l (s_init, v).
  have H_not_none: s_opt <> None by apply: PT.
  destruct s_opt as [s' | ] eqn:H_put.
  exists s'.
  apply: (HPG s_init s' v).
  exact: H_put.
  done.
Qed.

Lemma PgetTputPGandGI_SGP : [PG &&& GI ===>p SGP].
Proof.
  move => S V hs hv l pt HPG HGI s s' v H;
  case (p_put l (s,v)) eqn : H1.
  apply (HGI s0 s' v);
  split. apply (HPG s s0 v); firstorder.
  apply H.
  exfalso; apply (pt s v); firstorder.
Qed.

Lemma PgetTputUDandVD_WPG : [UD &&& VD ===>p WPG].
Proof.
  move => S V hs hv l PT HUD HVD s s' v v' [H1 H2].
  case (p_put l (s',v')) eqn:Hp.
  move : (HUD s' s0 v' v') => H3;
  have H4 := H3 (conj Hp H2).
  move : (HVD s s0 s' v v') => H5;
  have H6 := H5 (conj H1 H4).
  rewrite <- H6; apply H1.
  firstorder.
Qed.

Lemma TgetPputUDandPP_PT : [UD &&& PP ===>g PT].
Proof.
  move => S V hs hv l TG HUD HPP s s' v H.
  case (p_get l s) eqn:Hp.
  move : (HUD s s' v v0) => H1;
  have H2 := H1 (conj H Hp);
  apply (HPP s' s s' v0 v);
  firstorder. firstorder.
Qed.

Lemma PputPP_PT : [PP ===>p PT].
Proof.
  move => S V hs hv l pt PP s s' v H;
  case (p_put l (s,v)) eqn:H1;
  case (p_put l (s',v)) eqn:H3;
  inversion H;
  rewrite H2 in H1.
  have H4 := (PP s s' s1 v v)(conj H1 H3);
  rewrite H4 in H1; firstorder.
  exfalso;apply(pt s' v);firstorder.
Qed.


Ltac unfold_laws :=
  rewrite /SGP /GP /PG /PP /WPG /PGP 
          /UD /PT /SS /PS 
          /VD /PI /GS /GI /GPG.

Lemma non_implication (P Q : Prop) : P -> ~ Q -> ~ (P -> Q).
Proof. firstorder. Qed.

Ltac intro_all :=
  repeat (move=> ?).

Ltac ce_lens S V p_get p_put :=
  move=> H;
  have := H S V (mkLens p_get p_put);
  unfold_laws=> /=;
  intro_all.

Tactic Notation "len" 
  constr(S) constr(V) uconstr(get) uconstr(put):=
  move => H;
  let l := constr:(@mkLens S V get put) in
  pose l as l1.

Inductive Dom3 : Type :=
| a | b | c.

Lemma TgetTputGPandUDandGInotSGP : ~[GP &&& UD &&& GI ===>pg SGP].
Proof.
  move => H.
  set (S := bool).
  set (V := bool).
  set (l :=
  @mkLens bool bool
   (fun b =>
    match b with
    |false => Some true
    |true => Some false
    end)
   (fun sv =>
    match sv with
    |(false,_) => Some false
    |(true,_) => Some true
    end)
  ).
  have HSGP : GetTotal S V l -> PutTotal S V l -> GP S V l -> UD S V l -> GI S V l -> SGP S V l := H S V _ _ l.
  have GT : GetTotal S V l.
  by move=> [].
  have PT : PutTotal S V l.
  by move => [] [].
  have HGP : GP S V l.
  by move => [] [].
  have HUD : UD S V l.
  by move=> [] [] [] []; firstorder.
  have HGI : GI S V l.
  by move => [] [] []; firstorder.
  have HnotSGP : ~ SGP S V l.
  by move => HW;move :(HW false true false erefl).
  firstorder.
Qed.

Lemma TgetTputGPandUDnotGI : ~[GP &&& UD ===>pg GI].
Proof.
  move => H.
  set (S := bool).
  set(V := bool).
  set(l :=
  @mkLens bool bool 
   (fun b => Some false)
   (fun sv =>
    match sv with
    |(false,_) => Some false
    |(true,_) => Some true
    end)).
  have HGI : GetTotal S V l -> PutTotal S V l -> GP S V l -> UD S V l -> GI S V l := H S V _ _ l.
  have GT : GetTotal S V l.
  by move => [].
  have PT : PutTotal S V l. 
  by move => [] [].
  have GP : GP S V l. by move => [] [].
  have UD : UD S V l. move => [] [] [] [] ; firstorder.
  have HnotGI : ~ GI S V l.
  by move => HW;move:( HW false true false (conj erefl erefl)).
  firstorder.
Qed.

Lemma TgetTputGIandPGPandWPGnotGPG : ~[GI &&& PGP &&& WPG ===>pg GPG].
Proof.
  move => H.
  set(S := bool).
  set(V := bool).
  set (l :=
  @mkLens bool bool
  (fun b => Some b)
  (fun sv => Some true)
  ).
  have HGPG : GetTotal S V l -> PutTotal S V l -> GI S V l -> PGP S V l -> WPG S V l -> GPG S V l := H S V _ _ l.
  have GT : GetTotal S V l. by move => [].
  have PT : PutTotal S V l. by move => [] [].
  have HGI : GI S V l. by move => [] [] []; firstorder.
  have HPGP : PGP S V l. by move => [] [] [] [];firstorder.
  have HWPG : WPG S V l. by move => [] [] [] [];firstorder.
  have HnotGPG : ~ GPG S V l.
  by move => HW ;move :(HW false true false (conj erefl erefl)).
  firstorder.
Qed.

Lemma TgetTputGIandSSnotGPG : ~[GI &&& SS ===>pg GPG].
Proof.
  move => H.
  set(S := bool).
  set(V := bool).
  set (l :=
  @mkLens bool bool
  (fun b => 
   match b with
   |true => Some false
   |false => Some true
  end)
  (fun sv =>
   match sv with
   |(true,true) => Some true
   |_ => Some false
   end
   )
  ).
  have HGPG : GetTotal S V l -> PutTotal S V l -> GI S V l -> SS S V l -> GPG S V l := H S V _ _ l.
  have GT : GetTotal S V l. by move => [].
  have PT : PutTotal S V l. by move => [] [].
  have HGI : GI S V l. by move => [] [] [] ; firstorder.
  have HSS : SS S V l. rewrite /SS; case=> /=; exists true; firstorder.
  have HnotGPG : ~ GPG S V l. move => HW.
  have := HW true false false (conj erefl erefl).
  discriminate. firstorder.
Qed.

Lemma TgetTputGIandUDnotGPG : ~[GI &&& UD ===>pg GPG].
Proof.
  move => H. set(S := bool). set(V := bool).
  set (l :=
  @mkLens bool bool
  (fun b => Some b)
  (fun sv =>
   match sv with
   |(false,_) => Some true
   |(true,_) => Some false
   end
   )
  ).
  have HGPG : GetTotal S V l -> PutTotal S V l -> GI S V l -> UD S V l -> GPG S V l := H S V _ _ l.
  have GT : GetTotal S V l. by move => [].
  have PT : PutTotal S V l. by move => [] [].
  have HGI : GI S V l. by move => [] [] [] ; firstorder.
  have HUD : UD S V l. by move => [] [] [] [];firstorder.
  have HnotGPG : ~ GPG S V l.
  by move => HW;move:(HW false true false (conj erefl erefl)).
  firstorder.
Qed.

Lemma TgetTputGIandSSnotPGP : ~[GI &&& SS ===>pg PGP].
Proof.
  move => H. set(S := bool). set(V := bool).
  set (l :=
  @mkLens bool bool
  (fun b => Some b)
  (fun sv =>
   match sv with
   |(_,false) => Some true
   |(_,true) => Some false
   end
   )
  ).
  have HPGP : GetTotal S V l -> PutTotal S V l -> GI S V l -> SS S V l -> PGP S V l := H S V _ _ l.
  have GT : GetTotal S V l. by move => [].
  have PT : PutTotal S V l. by move => [] [].
  have HGI : GI S V l. by move => [] [] []; firstorder.
  have HSS : SS S V l. rewrite /SS ;case => /=.
  exists false; by []. exists true; by [].
  have HnotPGP : ~ PGP S V l.
  by move=> HW; move: (HW false true false true (conj erefl erefl)). 
  firstorder.
Qed.


Lemma TgetTputGPGandSSnotPGP : ~[GPG &&& SS ===>pg PGP].
Proof.
  move => H.
  set(S := bool).
  set(V := bool).
  set (l :=
  @mkLens bool bool
  (fun _ => Some false)
  (fun sv =>
   match sv with
   |(_,false) => Some true
   |(_,true) => Some false
   end
   )
  ).
  have HPGP : GetTotal S V l -> PutTotal S V l -> GPG S V l -> SS S V l -> PGP S V l := H S V _ _ l.
  have GT : GetTotal S V l. by move => [].
  have PT : PutTotal S V l. by move => [] [].
  have HGI : GPG S V l. by move => [] [] []; firstorder.
  have HSS : SS S V l. rewrite /SS; case => /=.
  exists false;by [].
  exists true;by [].
  have HnotPGP : ~ PGP S V l.
  by move => HW; move :(HW false false true false (conj erefl erefl)).
  firstorder.
Qed.

Lemma TgetTputGIandUDnotWSS : ~[GI &&& UD ===>pg WSS].
Proof.
  move => H. set(S := bool). set(V := bool).
  set (l :=
  @mkLens bool bool
  (fun b => Some b)
  (fun sv =>
   match sv with
   |(false,true) => Some true
   |_ => Some false
   end
   )
  ).
  have HWSS : GetTotal S V l -> PutTotal S V l -> GI S V l -> UD S V l -> WSS S V l := H S V _ _ l.
  have GT : GetTotal S V l. by move => [].
  have PT : PutTotal S V l. by move => [] [].
  have HGI : GI S V l. by move => [] [] [];firstorder.
  have HUD : UD S V l. by move => [] [] [] [];firstorder.
  have HnotWSS : ~ WSS S V l.
  by move=> HW; move: (HW true false true) => [v Hv];
  have := Hv erefl. firstorder.
Qed.

Lemma TgetTputGPGandUDnotWSS : ~[GPG &&& UD ===>pg WSS].
Proof.
  move => H. set(S := bool). set(V := bool).
  set (l :=
  @mkLens bool bool
  (fun b => Some true)
  (fun sv =>
   match sv with
   |(false,_) => Some true
   |(true,_) => Some false
   end
   )
  ).
  have HWSS : GetTotal S V l -> PutTotal S V l -> GPG S V l -> UD S V l -> WSS S V l := H S V _ _ l.
  have GT : GetTotal S V l. by [].
  have PT : PutTotal S V l. by move => [] [].
  have HGPG : GPG S V l. by move => [] []; firstorder.
  have HUD : UD S V l. by move => [] [] [] [];firstorder.
  have HnotWSS : ~ WSS S V l.
  by move => HW; move :(HW true false true) => [v Hv];
  have := Hv erefl. firstorder.
Qed.

Lemma TgetTputGIandWPGandPGPnotPS : ~[GI &&& WPG &&& PGP ===>pg PS].
Proof.
  move => H. set(S := bool). set(V := bool).
  set (l :=
  @mkLens bool bool
  (fun b =>
    match b with
    |false => Some true
    |true => Some false
    end)
  (fun _ => Some true
   )
  ).
  have HPS : GetTotal S V l -> PutTotal S V l -> GI S V l -> WPG S V l -> PGP S V l -> PS S V l := H S V _ _ l.
  have GT : GetTotal S V l. by move => [].
  have PT : PutTotal S V l. by move => [] [].
  have HGI : GI S V l. by move => [] [] []; firstorder.
  have HWPG : WPG S V l. by move => [] [] [] [];firstorder.
  have HPGP : PGP S V l. by move => [] [] [] [];firstorder.
  have HnotPS : ~ PS S V l.
  by move => HW ; move : (HW false) => [s' [v HJ]].
  firstorder.
Qed.

Lemma TgetTputGPGandWPGandPGPnotPS : ~[GPG &&& WPG &&& PGP ===>pg PS].
Proof.
  move => H. set(S := bool). set(V := bool).
  set (l :=
  @mkLens bool bool
  (fun _ => Some false)
  (fun _ => Some true)
  ).
  have HPS : GetTotal S V l -> PutTotal S V l -> GPG S V l -> WPG S V l -> PGP S V l -> PS S V l := H S V _ _ l.
  have GT : GetTotal S V l. by [].
  have PT : PutTotal S V l. by [].
  have HGI : GPG S V l. by move => [] [] [];firstorder.
  have HWPG : WPG S V l. by move => [] [] [] [];firstorder.
  have HPGP : PGP S V l. by move => [] [] [] [];firstorder.
  have HnotPS : ~ PS S V l.
  by move => HW;move: (HW false)=> [s' [v HJ]].
  firstorder.
Qed.


Lemma TgetTputGPnotWPG : ~[GP &&& GI ===>pg WPG].
Proof.
  move => H. set (S := bool). set (V := Dom3).
  set (l :=
  @mkLens bool Dom3
    (fun s =>
       match s with
       | false => Some a
       | true => Some c
       end)
    (fun sv =>
     match sv with
     | (false, a) => Some false
     | (false, b) => Some true
     | (false, c) => Some false
     | (true,  a) => Some true
     | (true,  b) => Some false
     | (true,  c) => Some true
     end)).
  have HWPG : GetTotal S V l -> PutTotal S V l -> GP S V l -> GI S V l -> WPG S V l := H S V _ _ l.
  have GT : GetTotal S V l. by move => [].
  have PT : PutTotal S V l. by move => [] [].
  have HGP : GP S V l. by move => [] [];firstorder.
  have HGI : GI S V l. by move => [] [] [];firstorder.
  have HnotWPG : ~ WPG S V l.
  by move => HW;move:(HW false true b c (conj erefl erefl)).
  firstorder.
Qed.

Lemma PgetTputUDnotWPG : ~[ UD ===>p WPG].
Proof.
  move => H. set (S := bool). set (V := bool).
  set (l :=
  @mkLens bool bool
  (fun b =>
   match b with
   |false => None
   |true => Some false
   end) 
    (fun x => Some match x with
      | (false, false) => false
      | _ => true
     end)
  ).
  have HWPG : PutTotal S V l -> UD S V l -> WPG S V l := H S V _ _ l.
  have HPT : PutTotal S V l. by [].
  have HUD : UD S V l. by move => [] [] [] [];firstorder.
  have HnotWPG : ~ WPG S V l.
  by move => HW;move: (HW false true true false (conj erefl erefl)).
  firstorder.
Qed.

Lemma PgetTputSGPnotWSS : ~[SGP ===>p WSS].
Proof.
  move => H. set (S := bool). set (V := bool).
  set (l :=
  @mkLens bool bool
  (fun _ => None) 
  (fun sv =>
   match sv with
   |(false,true) => Some true
   |_ => Some false
   end
   )
  ).
  have HWSS : PutTotal S V l -> SGP S V l -> WSS S V l := H S V _ _ l.
  have PT : PutTotal S V l. by move =>[] [].
  have HSGP : SGP S V l. by move => [] [] [].
  have HnotWSS : ~ WSS S V l.
  by move => HW;move: (HW true false true) => [v HJ]; firstorder.
  firstorder.
Qed.

Lemma PgetTputSGPnotPS : ~[SGP ===>p PS].
Proof.
  move => H. set (S := bool). set (V := bool).
  set (l :=
  @mkLens bool bool
  (fun _ => None) 
  (fun sv => Some true)
  ).
  have HPS : PutTotal S V l -> SGP S V l -> PS S V l := H S V _ _ l.
  have PT : PutTotal S V l. by [].
  have HSGP : SGP S V l. by [].
  have HnotPS : ~ PS S V l.
  by move => HW; move :(HW false) => [s' [v HJ]].
  firstorder.
Qed.

Lemma TgetPputGIandGPGnotGP : ~[GI &&& GPG ===>g GP].
Proof.
  move => H. set (S := bool). set (V := bool).
  set (l :=
  @mkLens bool bool
  (fun b => Some b)
  (fun sv => None)
  ).
  have HGP : GetTotal S V l -> GI S V l -> GPG S V l -> GP S V l := H S V _ _ l.
  have GT : GetTotal S V l. by [].
  have HGI : GI S V l. by move => [] [] [];firstorder.
  have HGPG : GPG S V l. by move => [] [] [];firstorder.
  have HnotGP : ~ GP S V l.
  by move => HW;move :(HW true true erefl).
 firstorder.
Qed.

Lemma TgetPputUDnotPS : ~[UD ===>g PS].
Proof.
  move => H. set (S := bool). set (V := bool).
  set (l :=
  @mkLens bool bool
  (fun b => Some false)
  (fun sv => None)
  ).
  have HPS : GetTotal S V l -> UD S V l -> PS S V l := H S V _ _ l.
  have GT : GetTotal S V l. by [].
  have HUD : UD S V l. by move => [] [] [] []; firstorder.
  have HnotPS : ~ PS S V l.
  by move => HW;move: (HW true) => [s' [v HJ]].
  firstorder.
Qed.

Lemma TgetTputVDandGSnotGPG : ~[VD &&& GS ===>pg GPG].
Proof.
  move => H. set (S := bool). set (V := bool).
  set (l :=
  @mkLens bool bool
  (fun b =>
   match b with
   |false => Some true
   |true => Some false
   end)
  (fun sv =>
   match sv with
   |(_,false) => Some false
   |(_,true) => Some true
  end)
  ).
  have HGPG : GetTotal S V l -> PutTotal S V l -> VD S V l -> GS S V l -> GPG S V l := H S V _ _ l.
  have GT : GetTotal S V l. by move => [].
  have PT : PutTotal S V l. by move => [] [].
  have HVD : VD S V l. by move => [] [] [] [] []; firstorder.
  have HGS : GS S V l. rewrite / GS ;case => /=.
  exists false; firstorder.
  exists true;firstorder.
  have HnotGPG : ~ GPG S V l.
  by move => HW;move: (HW true false false (conj erefl erefl)).
  firstorder.
Qed.

Lemma TgetTputWPGandGSnotGPG : ~[WPG &&& GS ===>pg GPG].
Proof.
  move => H. set (S := bool). set (V := bool).
  set (l :=
  @mkLens bool bool
  (fun b => Some b)
  (fun sv =>
   match sv with
   |(false,_) => Some true
   |(true,_) => Some false
  end)
  ).
  have HGPG : GetTotal S V l -> PutTotal S V l -> WPG S V l -> GS S V l -> GPG S V l := H S V _ _ l.
  have GT : GetTotal S V l. by [].
  have PT : PutTotal S V l. by move => [] [].
  have HWPG : WPG S V l. by move => [] [] [] [];firstorder.
  have HGS : GS S V l. rewrite / GS ;case => /=.
  exists true; firstorder.
  exists false; firstorder.
  have HnotGPG : ~ GPG S V l.
  by move => HW ; move:(HW true false true(conj erefl erefl)).
  firstorder.
Qed.

Lemma TgetTputGPGandVDandGSnotWPG : ~[GPG &&& VD &&& GS ===>pg WPG].
Proof.
  move => H. set (S := Dom3). set (V := bool).
  set (l :=
  @mkLens Dom3 bool
  (fun b =>
   match b with
   |c => Some false
   |_ => Some true
   end)
  (fun sv =>
   match sv with
   |(_,true) => Some b
   |(c,false) => Some c
   |_ => Some a
  end)
  ).
  have HWPG : GetTotal S V l -> PutTotal S V l -> GPG S V l -> VD S V l -> GS S V l -> WPG S V l := H S V _ _ l.
  have GT : GetTotal S V l. by move => [].
  have PT : PutTotal S V l. by move => [] [].
  have HGPG : GPG S V l. by move => [] [] [];firstorder.
  have HVD : VD S V l. by move => [] [] [] [] [];firstorder.
  have HGS : GS S V l. rewrite / GS ; case => /=.
  exists a ; firstorder.
  exists c ; firstorder.
  have HnotWPG : ~ WPG S V l.
  by move => HW;move : (HW a a false true (conj erefl erefl)).
  firstorder.
Qed.

Lemma TgetTputGPGandWPGnotGS : ~[GPG &&& WPG ===>pg GS].
Proof.
  move => H. set (S := bool). set (V := bool).
  set (l :=
  @mkLens bool bool
  (fun _ => Some true)
  (fun sv =>
   match sv with
   |(false,_) => Some false
   |(true,_) => Some true
  end)
  ).
  have HGS : GetTotal S V l -> PutTotal S V l -> GPG S V l -> WPG S V l -> GS S V l := H S V _ _ l.
  have GT : GetTotal S V l. by [].
  have PT : PutTotal S V l. by move => [] [].
  have HGPG : GPG S V l. by move => [] [] [];firstorder.
  have HWPG : WPG S V l. by move => [] [] [] [] ; firstorder.
  have HnotGS : ~ GS S V l.
  by move => HW;move: (HW false) => [s HJ].
  firstorder.
Qed.


Lemma TgetTputGPGandVDnotGS : ~[GPG &&& VD ===>pg GS].
Proof.
  move => H. set (S := bool). set (V := bool).
  set (l :=
  @mkLens bool bool
  (fun _ => Some true)
  (fun sv =>
   match sv with
   |(_,false) => Some true
   |(_,true) => Some false
  end)
  ).
  have HGS : GetTotal S V l -> PutTotal S V l -> GPG S V l -> VD S V l -> GS S V l := H S V _ _ l.
  have GT : GetTotal S V l. by [].
  have PT : PutTotal S V l. by move => [] [].
  have HGPG : GPG S V l. by move => [] [] []; firstorder.
  have HVD : VD S V l. by move => [] [] [] [] [];firstorder.
  have HnotGS : ~ GS S V l.
  by move => HW;move: (HW false) => [s HJ].
  firstorder.
Qed.

Lemma TgetTputGPGandWPGandGSnotPI : ~[GPG &&& WPG &&& GS ===>pg PI].
Proof.
  move => H.
  set (S := bool).
  set (V := bool).
  set (l :=
  @mkLens bool bool
  (fun b =>
   match b with
   |false => Some true
   |true => Some false
   end)
  (fun sv =>
   match sv with
   |(true,false) => Some true
   |_ => Some false
  end)
  ).
  have HPI : GetTotal S V l -> PutTotal S V l -> GPG S V l -> WPG S V l -> GS S V l -> PI S V l:= H S V _ _ l.
  have GT : GetTotal S V l. by move => [].
  have PT : PutTotal S V l. by move => [] [].
  have HGPG : GPG S V l. by move => [] [] [];firstorder.
  have HWPG : WPG S V l. by move => [] [] [] [];firstorder.
  have HGS : GS S V l. rewrite /GS ;case => /=.
  exists false; firstorder.
  exists true; firstorder.
  have HnotPI : ~ PI S V l.
  by move => HW; move: (HW false false false true (conj erefl erefl)).
  firstorder.
Qed.

Lemma PgetTputWPGandVDnotPG : ~[WPG &&& VD ===>p PG].
Proof.
  move => H. set (S := bool). set (V := bool).
  set (l :=
  @mkLens bool bool
  (fun _ => None)
  (fun sv =>
   match sv with
   |(_,false) => Some true
   |(_,true) => Some false
  end)
  ).
  have HPG : PutTotal S V l -> WPG S V l -> VD S V l -> PG S V l := H S V _ _ l.
  have PT : PutTotal S V l. by move => [] [].
  have HWPG : WPG S V l. by move => [] [] [] [];firstorder.
  have HVD : VD S V l. by move => [] [] [] [] [];firstorder.
  have HnotPG : ~ PG S V l.
  by move => HW; move :(HW true true false erefl).
  firstorder.
Qed.

Lemma TgetPputPGnotGS : ~[PG ===>g GS].
Proof.
  move => H. set (S := bool). set (V := bool).
  set (l :=
  @mkLens bool bool
  (fun _ => Some true)
  (fun _ => None)
  ).
  have HGS : GetTotal S V l -> PG S V l -> GS S V l := H S V _ _ l.
  have GT : GetTotal S V l. by [].
  have HPG : PG S V l. by move => [] [] [];firstorder.
  have HnotGS : ~ GS S V l.
  by move => HW;move: (HW false) => [s HJ].
  firstorder.
Qed.

Lemma TputWSSnotPT : ~[WSS ===>p PT].
Proof.
  move => H. set (S := bool). set (V := bool).
  set (l :=
  @mkLens bool bool
  (fun b => Some true)
  (fun sv =>
   match sv with
   |(false,false) => Some true
   |(true,true) => Some true
   |_ => Some false
  end)
  ).
  have HPT : PutTotal S V l -> WSS S V l -> PT S V l := H S V _ _ l.
  have Pt : PutTotal S V l. by move => [] [].
  have HWSS : WSS S V l. rewrite / WSS ; case => /=.
  exists (true); firstorder.
  exists (true); firstorder.
  have HnotPT : ~ PT S V l.
  by move => HW;move : (HW false true false erefl).
  firstorder.
Qed.

Lemma TputPTnotPP : ~[PT ===>p PP].
Proof.
  move => H. set (S := bool). set (V := bool).
  set (l :=
  @mkLens bool bool
  (fun _ => Some true)
  (fun sv =>
   match sv with
   |(false,true) => Some false
   |_ => Some true
  end)
  ).
  have HPP : PutTotal S V l -> PT S V l -> PP S V l := H S V _ _ l.
  have Pt : PutTotal S V l. by move => [] [].
  have HPT : PT S V l. by move => [] [] [].
  have HnotPP : ~PP S V l.
  by move => HW ; move :  (HW false true true false true (conj erefl erefl)).
  firstorder.
Qed.

Lemma PputPPnotWSS : ~[PP ===> WSS].
Proof.
  move => H. set (S := bool). set (V := bool).
  set (l :=
  @mkLens bool bool
  (fun b => Some false)
  (fun sv =>
   match sv with
   |(false,false) => Some false
   |(false,true) => Some true
   |_ => None
  end)
  ).
  have HWSS : PP S V l -> WSS S V l := H S V _ _ l.
  have HPP : PP S V l. by move => [] [] [] [] [];firstorder.
  have HnotWSS : ~WSS S V l.
  by move => HW ; move : (HW true false true) => [v HJ];firstorder.
  firstorder.
Qed.

Lemma TgetTputSGPnotPI : ~[SGP ===>pg PI].
Proof.
  move => H. set (S := bool). set (V := Dom3).
  set (l :=
  @mkLens bool Dom3
  (fun b =>
   match b with
   |false => Some a
   |true => Some c
   end)
  (fun sv =>
   match sv with
   |(_,c) => Some true
   |_ => Some false
  end)
  ).
  have HPI : GetTotal S V l -> PutTotal S V l -> SGP S V l -> PI S V l := H S V _ _ l.
  have GT : GetTotal S V l. by move => [].
  have PT : PutTotal S V l. by move => [] [].
  have HSGP : SGP S V l. by move => [] [] [].
  have HnotPI : ~ PI S V l.
  by move => HW; move : (HW false false a b (conj erefl erefl)).
  firstorder.
Qed.

Lemma TgetPputSGPnotGS : ~[SGP ===>pg GS].
Proof.
  move => H. set (S := bool). set (V := Dom3).
  set (l :=
  @mkLens bool Dom3
  (fun b =>
   match b with
   |false => Some c
   |true => Some a
   end)
  (fun sv =>
   match sv with
   |(_,a) => Some true
   |_ => Some false
  end)
  ).
  have HGS : GetTotal S V l -> PutTotal S V l -> SGP S V l -> GS S V l := H S V _ _ l.
  have GT : GetTotal S V l. by move => [].
  have PT : PutTotal S V l. by move => [] [].
  have HSGP : SGP S V l. by move => [] [] [].
  
  have HnotGS : ~ GS S V l.
  move=> HW; case: (HW b) => [[]] //.
  firstorder. 
Qed.

Lemma TgetPputSGPnotPT : ~[SGP ===>pg PT].
Proof.
  move => H. set (S := bool). set (V := Dom3).
  set (l :=
  @mkLens bool Dom3
  (fun B =>
   match B with
   |false => Some a
   |true => Some b
   end)
  (fun sv =>
   match sv with
   |(_,a) => Some false
   |(true , c) => Some false
   |_ => Some true
  end)
  ).
  have HPT : GetTotal S V l -> PutTotal S V l -> SGP S V l -> PT S V l := H S V _ _ l.
  have GT : GetTotal S V l. by move => [].
  have Pt : PutTotal S V l. by move => [] [].
  have HSGP : SGP S V l. by move => [] [] [].
  have HnotPT : ~ PT S V l.
  by move => HW ; move : (HW true false c erefl).
  firstorder.
Qed.

Lemma TgetTputPGnotGI : ~[PG ===>pg GI].
Proof.
  move => H. set (S := Dom3). set (V := bool).
  set (l :=
  @mkLens Dom3 bool
  (fun b =>
   match b with
   |c => Some true
   |_ => Some false
   end)
  (fun sv =>
   match sv with
   |(_,false) => Some a
   |(_,true) => Some c
  end)
  ).
  have HGI : GetTotal S V l -> PutTotal S V l -> PG S V l -> GI S V l := H S V _ _ l.
  have GT : GetTotal S V l. by move => [].
  have Pt : PutTotal S V l. by move => [] [].
  have HPG : PG S V l. by move => [] [] [].
  have HnotGI : ~ GI S V l.
  by move => HW;move : (HW a b false (conj erefl erefl)).
  firstorder.
Qed.

Lemma TgetTputPGnotWSS : ~[PG ===>pg WSS].
Proof.
  move => H. set (S := Dom3). set (V := bool).
  set (l :=
  @mkLens Dom3 bool
  (fun b =>
   match b with
   |b => Some true
   |_ => Some false
   end)
  (fun sv =>
   match sv with
   |(_,true) => Some b
   |(a,false) => Some c
   |_ => Some a
  end)
  ).
  have HWSS : GetTotal S V l -> PutTotal S V l -> PG S V l -> WSS S V l := H S V _ _ l.
  have GT : GetTotal S V l. by move => [].
  have Pt : PutTotal S V l. by move => [] [].
  have HPG : PG S V l. by move => [] [] [].
  have HnotWSS : ~ WSS S V l.
  by move=> HW; case: (HW c a false) => [v HJ]; case: v HJ => //= Hj; move : (Hj erefl).
  firstorder.
Qed.

Lemma TgetTputPGnotPS : ~[PG ===>pg PS].
Proof.
  move => H. set (S := Dom3). set (V := bool).
  set (l :=
  @mkLens Dom3 bool
  (fun b =>
   match b with
   |b => Some true
   |_ => Some false
   end)
  (fun sv =>
   match sv with
   |(_,false) => Some c
   |(_,true) => Some b
  end)
  ).
  have HPS : GetTotal S V l -> PutTotal S V l -> PG S V l -> PS S V l := H S V _ _ l.
  have GT : GetTotal S V l. by move => [].
  have Pt : PutTotal S V l. by move => [] [].
  have HPG : PG S V l. by move => [] [] [].
  have HnotPS : ~PS S V l.
  by move => HW; move: (HW a) => [s' [v HJ]] ;case s',v.
  firstorder.
Qed.

Lemma TgetTputPPnotGI : ~[PP ===>pg GI].
Proof.
  move => H. set (S := bool). set (V := bool).
  set (l :=
  @mkLens bool bool
  (fun _ => Some false)
  (fun sv =>
   match sv with
   |(_,false) => Some true
   |(_,true) => Some false
  end)
  ).
  have HGI : GetTotal S V l -> PutTotal S V l -> PP S V l -> GI S V l := H S V _ _ l.
  have GT : GetTotal S V l. by move => [].
  have Pt : PutTotal S V l. by move => [] [].
  have HPP : PP S V l. by move => [] [] [] [] [];firstorder.
  have HnotGI : ~ GI S V l.
  by move => HW;move : (HW true false false (conj erefl erefl)).
  firstorder.
Qed.

Lemma TgetTputPPnotGPG : ~[PP ===>pg GPG].
Proof.
  move => H. set (S := bool). set (V := bool).
  set (l :=
  @mkLens bool bool
  (fun b =>
   match b with
   |false => Some true
   |true => Some false
  end)
  (fun sv =>
   match sv with
   |(_,false) => Some false
   |(_,true) => Some true
  end)
  ).
  have HGPG : GetTotal S V l -> PutTotal S V l -> PP S V l -> GPG S V l := H S V _ _ l.
  have GT : GetTotal S V l. by move => [].
  have Pt : PutTotal S V l. by move => [] [].
  have HPP : PP S V l. by move => [] [] [];firstorder.
  have HnotGPG : ~GPG S V l.
  by move => HW ;move : (HW false true true (conj erefl erefl)).
  firstorder.
Qed.

Lemma TgetTputPPnotPGP : ~[PP ===>pg PGP].
Proof.
  move => H. set (S := bool). set (V := bool).
  set (l :=
  @mkLens bool bool
  (fun _ => Some false)
  (fun sv =>
   match sv with
   |(_,false) => Some true
   |(_,true) => Some false
  end)
  ).
  have HPGP : GetTotal S V l -> PutTotal S V l -> PP S V l -> PGP S V l := H S V _ _ l.
  have GT : GetTotal S V l. by move => [].
  have Pt : PutTotal S V l. by move => [] [].
  have HPP : PP S V l. by move => [] [] [];firstorder.
  have HnotPGP : ~PGP S V l.
  by move => HW ; move : (HW false false true false (conj erefl erefl)).
  firstorder.
Qed.

Lemma TgetTputPPnotPS : ~[PP ===>pg PS].
Proof.
  move => H. set (S := bool). set (V := bool).
  set (l :=
  @mkLens bool bool
  (fun _ => Some false)
  (fun _ => Some true)).
  have HPS : GetTotal S V l -> PutTotal S V l -> PP S V l -> PS S V l := H S V _ _ l.
  have GT : GetTotal S V l. by move => [].
  have Pt : PutTotal S V l. by move => [] [].
  have HPP : PP S V l. by move => [] [] [] ;firstorder.
  have HnotPS : ~PS S V l.
  by move => HW;move: (HW false) => [s [v HJ]];case s,v.
  firstorder.
Qed.

Lemma TgetTputPPnotWPG : ~[PP ===>pg WPG].
Proof.
  move => H. set (S := bool). set (V := bool).
  set (l :=
  @mkLens bool bool
  (fun b => Some false)
  (fun sv =>
   match sv with
   |(_,false) => Some true
   |(_,true) => Some false
  end)
  ).
  have HWPG : GetTotal S V l -> PutTotal S V l -> PP S V l -> WPG S V l := H S V _ _ l.
  have GT : GetTotal S V l. by move => [].
  have Pt : PutTotal S V l. by move => [] [].
  have HPP : PP S V l. by move => [] [] [];firstorder.
  have HnotWPG : ~WPG S V l.
  by move => HW;move: (HW false false true false (conj erefl erefl)).
  firstorder.
Qed.

Lemma j : [PG &&& PS &&& UD &&& PP ===> WSS].
Proof.
  move => S V hs hv l HPG HPS HUD HPP s s' v'.
  unfold PG in HPG;unfold PS in HPS ; unfold UD in HUD; unfold PP in HPP.
  case (HPS s') => [s'' [v H1]].
  exists (v). move => H2.
  move : (HPG s' s v') => H3. have H4 := H3 H2.
  move : (HPG s'' s' v) => H5. have H6 := H5 H1.
  move : (HUD s' s v' v) => H7. have H8 := H7 (conj H2 H6).
  move : (HUD s s' v v') => H9. have H10 := H9 (conj H8 H4).
  Admitted.

Lemma TgetTputUDandPGnotWSS : ~[UD &&& PG ===>pg WSS].
Lemma TgetTputGIandUDandGSnotWSS : ~[GI &&& UD &&& GS ===>pg WSS].
Lemma TgetTputGIandVDandGSnotWSS : ~[GI &&& VD &&& GS ===>pg WSS].
Lemma TgetTputGIandGSandVDandPSnotWSS : ~[GI &&& GS &&& VD &&& PS ===>pg WSS].
(*yuugenn dato mitukaranai. wakaranai*)

Lemma PgetTputGPandUDandWPGandGIandPIandGSnotWSS : ~[GP &&& UD &&& WPG &&& GI &&& PI &&& GS ===>p WSS].
Lemma PgetTputSGPandVDnotWSS : ~[SGP &&& VD ===>p WSS].
Lemma TgetPputPSandPGandGSandPPnotWSS : ~[PS &&& PG &&& GS &&& PP ===>g WSS].
Lemma TgetTputUDandPGnotWSS : ~[UD &&& PG ===> WSS].
Lemma PgetPputUDandPGandGSandPSandPPnotWSS : ~[UD &&& PG &&& GS &&& PS &&& PP ===> WSS].
(*PS mo hairu kanousei ga aru*)

Lemma TgetTputGPandGIandPIandGSnotPT : ~[GP &&& GI &&& PI &&& GS ===>pg PT].
Lemma PgetTputSGPandPSandVDnotPT : ~[SGP &&& PS &&& VD ===>p PT].
Lemma PgetTputSGPandSSandPInotPT : ~[SGP &&& SS &&& PI ===>p PT].
Lemma PgetTputUDandPSandPGnotPT : ~[UD &&& PS &&& PG ===>p PT].
Lemma TgetPputGPandUDandWPGandGIandPIandGSnotPT : ~[GP &&& UD &&& WPG &&& GI &&& PI &&& GS ===>g PT].

Lemma TgetTputSGPandPTnotPP : ~[SGP &&& PT ===>pg PP].
(*kore ha domeinn ga mugenn.ronnbunn wo sannkou ni*)
(*PT mo iranai ga menndou nanode ireteru*)
Lemma TgetTputGPandPGandUDandPTnotPP : ~ [GP &&& PG &&& UD &&& PT ===>pg PP].
Lemma PgetTputSGPandSSandVDandPTnotPP : ~ [SGP &&& SS &&& VD &&& PT ===>p PP].

Lemma TgetTputGPandUDandGIandGSandPPnotPI : ~[GP &&& UD &&& GI &&& GS &&& PP ===>pg PI].

Lemma TgetTputGPandGIandGSandPInotVD : ~[GP &&& GI &&& GS &&& PI ===>pg VD].

Lemma TgetTputSGPandPPnotGS : ~ [SGP &&& PP ===>pg GS].
(*yuugenn no hannrei nai*)
Lemma TgetTputSSandGIandVDandPPnotGS : ~[SS &&& GI &&& VD &&& PP ===>pg GS].
Lemma TgetTputGPandGIandPInotGS : ~[GP &&& GI &&& PI ===>pg GS].

Lemma PgetTputSGPandSSandVDandPPnotGS : ~ [ SGP &&& SS &&& VD &&& PP ===>p GS].
Lemma TgetPputSGPandPGandPPandPTnotGS : ~ [ SGP &&& PG &&& PP &&& PT ===>g GS].

Lemma TgetTputSGPandPPnotPG : ~[SGP &&& PP ===>pg PG].
Lemma PgetTputSGPandSSandVDandPPnotPG : ~ [SGP &&& SS &&& VD &&& PP ===>p PG].

Lemma TgetTputGPandGIandPIandGSnotWPG : ~[GP &&& GI &&& PI &&& GS ===>pg WPG].
Lemma TgetTputGPandGIandGSandPTnotWPG : ~[GP &&& GI &&& GS &&& PT ===>pg WPG].
Lemma TgetTputGPGandSSandVDandGSandPPnotWPG : ~[GPG &&& SS &&& VD &&& GS &&& PP ===>pg WPG].
Lemma TgetTputGIandSSandVDandGSandPPnotWPG : ~[GI &&& SS &&& VD &&& GS &&& PP ===>pg WPG].

Lemma PgetTputGPandUDandGIandSSandGSandPInotWPG : ~[GP &&& UD &&& GI &&& SS &&& GS &&& PI ===>p WPG].
Lemma PgetTputGPandUDandGIandSSandGSandPTnotWPG : ~[GP &&& UD &&& GI &&& SS &&& GS &&& PT ===>p WPG].
Lemma PgetTputGPGandSSandVDandGSandPPnotWPG : ~[GPG &&& SS &&& VD &&& GS &&& PP ===>p WPG].
Lemma PgetTputGIandSSandVDandGSandPPnotWPG : ~[GI &&& SS &&& VD &&& GS &&& PP ===>p WPG].


Lemma TgetTputPGPandPGandPPnotPS : ~ [PGP &&& PG &&& PP ===>pg PS].
Lemma TgetTputGIandPGPandWPGandGSandPPnotPS : ~[GI &&& PGP &&& WPG &&& GS &&& PP ===>pg PS].
Lemma TgetTputGIandVDandGSnotPS : ~[GI &&& VD &&& GS ===>pg PS].

Lemma PgetTputSGPandPGandPPnotPS : ~[SGP &&& PG &&& PP ===>p PS].

Lemma TgetPputUDandGIandPGPandPGandGSandPPandPTnotPS : ~[UD &&& GI &&& PGP &&& PG &&& GS &&& PP &&& PT ===>g PS].


Lemma TgetTputPSandPGnotSS : ~[PS &&& PG ===>pg SS].
Lemma PgetTputSGPandPSandVDnotSS : ~[SGP &&& PS &&& VD ===>p SS].
Lemma TgetPputPSandPGandGSandPPnotSS : ~[PS &&& PG &&& GS &&& PP ===>g SS].

Lemma TgetTputGPandUDandGIandPPnotSGP : ~ [GP &&& UD &&& GI &&& PP ===>pg SGP].





