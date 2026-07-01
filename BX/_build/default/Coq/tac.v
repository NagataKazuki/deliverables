From bx_plugin.Coq Require Export sample.

Ltac have_tg :=
  have HTG : GetTotal S V l.

Ltac have_tp :=
  have HTP : PutTotal S V l.

Ltac have_sgp :=
  have HSGP : SGP S V l.

Ltac have_notsgp :=
  have HnotSGP : ~ SGP S V l.

Ltac have_gp :=
  have HGP : GP S V l.

Ltac have_notgp :=
  have HnotGP : ~ GP S V l.

Ltac have_pg :=
  have HPG : PG S V l.

Ltac have_notpg :=
  have HnotPG : ~ PG S V l.

Ltac have_pp :=
  have HPP : PP S V l.

Ltac have_notpp :=
  have HnotPP : ~ PP S V l.

Ltac have_wpg :=
  have HWPG : WPG S V l.

Ltac have_notwpg :=
  have HnotWPG : ~ WPG S V l.

Ltac have_pgp :=
  have HPGP : PGP S V l.

Ltac have_notpgp :=
  have HnotPGP : ~ PGP S V l.

Ltac have_gpg :=
  have HGPG : GPG S V l.

Ltac have_notgpg :=
  have HnotGPG : ~ GPG S V l.

Ltac have_ud :=
  have HUD : UD S V l.

Ltac have_notud :=
  have HnotUD : ~ UD S V l.

Ltac have_gi :=
  have HGI : GI S V l.

Ltac have_notgi :=
  have HnotGI : ~ GI S V l.

Ltac have_gs :=
  have HGS : GS S V l.

Ltac have_notgs :=
  have HnotGS : ~ GS S V l.

Ltac have_pt :=
  have HPT : PT S V l.

Ltac have_notpt :=
  have HnotPT : ~ PT S V l.

Ltac have_ss :=
  have HSS : SS S V l.

Ltac have_notss :=
  have HnotSS : ~ SS S V l.

Ltac have_wss :=
  have HWSS : WSS S V l.

Ltac have_notwss :=
  have HnotWSS : ~ WSS S V l.

Ltac have_ps :=
  have HPS : PS S V l.

Ltac have_notps :=
  have HnotPS : ~ PS S V l. 

Ltac have_vd :=
  have HVD : VD S V l.

Ltac have_notvd :=
  have HnotVD : ~ VD S V l.

Ltac have_pi :=
  have HPI : PI S V l.

Ltac have_notpi :=
  have HnotPI : ~ PI S V l.