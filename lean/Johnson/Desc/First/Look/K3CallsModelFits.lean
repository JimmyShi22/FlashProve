-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/First/Look/K3CallsModelFits.lean: the lookup on a link's CALLS: THE FIELD "model" OF
AttTiesR AND LayTiesR (Johnson/Desc/First/Look/K3CallsMeanR.lean), LAID IN THE FIELD's PLACE BY
LEAN,
AT ONE SET OF LETTERS: att_model_hid, lay_model_hid (K3CallsModelAt.lean) with SymsAre paid by
symsAre_readAt (K3CopiesRead.lean) and, at the layers, the reading of the weights by hW_conduit
(K3CallsWeights.lean). A joining: no new mathematics. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: the table of joints' items constr m .lookCalls, constr m .rider.
USER: Johnson/Desc/Sound/MgAt/K3Calls.lean (att_model_at, lay_model_at).
  Meant: attTies_ofR, layTies_ofR's premise model at the composed meaning.
LETTERS: those of the four files; the family of readings is msgF w j := readAt D.codes arr ms N j w:
  the witness's messages as segment j reads them; at the layers the committed table's letters are
  the terms oWc, wOfC, msgWc (K3StoredThree.lean) at the sizes rows, cols.

WHAT IS LEFT, EACH A NAMED PREMISE: EQUATIONS ON LETTERS: hc (constr) · hhid, hb (how H reads a
  witness) · at the layers hpw (pinW), hdec (the one decoder) · ON PUBLIC LETTERS: fit (sizesFit) ·
  T
  (linkTieB) · O1 (OneNumber at id) · Own (OwnNamed) · hgs (GroupsSeated) · AttOK | LayOK, hT, hU
  (theorems in the goals' scope) · OVER EVERY WITNESS: reads (ReadsOne: readsOne_readAt
  (Johnson/P5J/WordsAtQ.lean) gives it from five premises on public letters).

Main names: `att_model_at`, `att_model_fits` · `lay_model_at`, `lay_model_fits`.

Limits. A rule over letters: no premise is shown at any term here.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsMeanR
import Johnson.Desc.First.Look.K3CallsModelAt
import Johnson.Desc.First.Look.K3CopiesRead
import Johnson.Desc.First.Look.K3CallsWeights

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Inst.Model Inst.Model.All
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look.Stored (oWc wOfC msgWc CellsW)
open VerifiableInference.Desc.First (ModelPart Meaning Numbers)
open _root_.Meaning (linkTieB BaseSegF seatBy fLay hidAtF ReadsOne sizesFit)

/-! ## Attention -/

section
variable {P Cl Cells Tok Xi : Type} {Fr : Frame} {rows cols : ℕ} {X : Verify.Public}
  {set : Params.Setting} {x : Desc.First.Look.Place} {D : Desc.First.Look.Sent}
  {rad : OracleShape → ℕ} {num : ℕ → ℕ → ℕ} {idx : ℕ → ℕ} (tls : ℕ → HTailF2)
  (tok : Desc.Wit Cells Tok MsgT → Fin ppref.V) {g m hd : ℕ}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ) {ms : List Mem}
  {N : Numbers} {Mg : Meaning P (Desc.Wit Cells Tok MsgT)}
  {put : P5J.TReq → Fin ppref.V → P5J.TReq}
  {H : P5J.HidAt X P (Desc.Wit Cells Tok MsgT) rows cols}
  {headPart : P5J.TPart → Cm.Idx → P × P5J.TS → Desc.Strs → Desc.Wit Cells Tok MsgT → Prop}
  {digitsPart : ℕ → P × P5J.TS → Desc.Strs → Desc.Wit Cells Tok MsgT → Prop}

/-- **model, at an attention link**, at the family "as segment j reads them". -/
theorem att_model_at (hc : Mg.constr = P5J.constrQAt hd put H headPart digitsPart)
    (hhid : ∀ w, H.hid w = hidAtF X (fun j => szOf (tls j))
      (seatBy (fLay D.layout num) X fun j => szOf (tls j)) (tok w)
      (fun j => Desc.Sound.readAt D.codes arr ms N j w))
    (hb : ∀ j w, H.base j w → BaseSegF (fun j => szOf (tls j))
      (seatBy (fLay D.layout num) X fun j => szOf (tls j))
      (fun j => Desc.Sound.readAt D.codes arr ms N j w) j)
    (fit : sizesFit X (fun j => szOf (tls j)) = true)
    (reads : ∀ w : Desc.Wit Cells Tok MsgT, ReadsOne X (fun j => szOf (tls j))
      (seatBy (fLay D.layout num) X fun j => szOf (tls j))
      (fun j => Desc.Sound.readAt D.codes arr ms N j w))
    (hg : g < 12) (hxl : x.link = m) (hl : m = 2 * g + 1) (hhd : m ≠ hd)
    (T : linkTieB X D rad num idx x.link (tls x.link) = true)
    (O1 : OneNumber X D rad num idx tls x.link seatT arr id)
    (Own : OwnNamed X D num tls x.link arr ms N) (hgs : GroupsSeated ms N)
    (HA : AttOK set x (Road.Hd.shapeA X g) (tls x.link) D rad)
    (hT : TabsAre (Road.Hd.shapeA X g) x.fs)
    (hU : ∀ c : Fin 4, (Road.L5.dimOf (Road.Hd.shapeA X g)).used c ≤
      2 ^ Cb.LdLkp.Port.nOf x.fs c) (z : P) :
    ∀ s y w, AttSays x (Road.Hd.shapeA X g) (tls x.link) D rad (attMs x D rad seatT arr w) →
      Mg.constr m .small (z, s) y w →
      Mg.constr m .lookCalls (z, s) y w ∧ Mg.constr m .rider (z, s) y w :=
  att_model_hid tls (fun w j => Desc.Sound.readAt D.codes arr ms N j w) tok seatT arr hc hhid hb
    fit reads hg hxl hl hhd T HA (fun w => symsAre_readAt_att T O1 Own hgs w) hT hU z

/-- **Lean lays it in the field's place.** -/
theorem att_model_fits (G : Desc.FileDescription Xi)
    (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
      Option ((attSg x D rad).om i).Smp)
    (claim : Aff → Cl) (links : List ModelPart) (ps : List Desc.Place) (k : ℕ)
    (Yes : Desc.First.S × Fr.E.Str → Desc.First.S × Fr.E.Str → Prop)
    (Rc : Desc.First.S × Fr.E.Str → Prop)
    (hc : Mg.constr = P5J.constrQAt hd put H headPart digitsPart)
    (hhid : ∀ w, H.hid w = hidAtF X (fun j => szOf (tls j))
      (seatBy (fLay D.layout num) X fun j => szOf (tls j)) (tok w)
      (fun j => Desc.Sound.readAt D.codes arr ms N j w))
    (hb : ∀ j w, H.base j w → BaseSegF (fun j => szOf (tls j))
      (seatBy (fLay D.layout num) X fun j => szOf (tls j))
      (fun j => Desc.Sound.readAt D.codes arr ms N j w) j)
    (fit : sizesFit X (fun j => szOf (tls j)) = true)
    (reads : ∀ w : Desc.Wit Cells Tok MsgT, ReadsOne X (fun j => szOf (tls j))
      (seatBy (fLay D.layout num) X fun j => szOf (tls j))
      (fun j => Desc.Sound.readAt D.codes arr ms N j w))
    (hg : g < 12) (hxl : x.link = m) (hl : m = 2 * g + 1) (hhd : m ≠ hd)
    (T : linkTieB X D rad num idx x.link (tls x.link) = true)
    (O1 : OneNumber X D rad num idx tls x.link seatT arr id)
    (Own : OwnNamed X D num tls x.link arr ms N) (hgs : GroupsSeated ms N)
    (HA : AttOK set x (Road.Hd.shapeA X g) (tls x.link) D rad)
    (hT : TabsAre (Road.Hd.shapeA X g) x.fs)
    (hU : ∀ c : Fin 4, (Road.L5.dimOf (Road.Hd.shapeA X g)).used c ≤
      2 ^ Cb.LdLkp.Port.nOf x.fs c) (z : P)
    (O : AttTiesR (Fr := Fr) G x (Road.Hd.shapeA X g) (tls x.link) D rad set seatT arr smp claim N
      Mg links ps z k m Yes Rc) :
    AttTiesR (Fr := Fr) G x (Road.Hd.shapeA X g) (tls x.link) D rad set seatT arr smp claim N Mg
      links ps z k m Yes Rc :=
  { O with
    model := att_model_at tls tok seatT arr hc hhid hb fit reads hg hxl hl hhd T O1 Own hgs HA hT
      hU z }

end

/-! ## The layers -/

section
variable {P Cl Tok Xi : Type} {Fr : Frame} {rows cols : ℕ} {X : Verify.Public}
  {set : Params.Setting} {x : Desc.First.Look.Place} {D : Desc.First.Look.Sent}
  {rad : OracleShape → ℕ} {num : ℕ → ℕ → ℕ} {idx : ℕ → ℕ} (tls : ℕ → HTailF2)
  (tok : Desc.Wit (CellsW rows cols) Tok MsgT → Fin ppref.V) {g m hd : ℕ}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ) {ms : List Mem}
  {N : Numbers} {Mg : Meaning P (Desc.Wit (CellsW rows cols) Tok MsgT)}
  {put : P5J.TReq → Fin ppref.V → P5J.TReq}
  {H : P5J.HidAt X P (Desc.Wit (CellsW rows cols) Tok MsgT) rows cols}
  {headPart : P5J.TPart → Cm.Idx → P × P5J.TS → Desc.Strs →
    Desc.Wit (CellsW rows cols) Tok MsgT → Prop}
  {digitsPart : ℕ → P × P5J.TS → Desc.Strs → Desc.Wit (CellsW rows cols) Tok MsgT → Prop}
  {decT : (ℕ → Option (ℕ × List UInt64)) → P × P5J.TS → Option (CellsW rows cols)}

/-- **model, at a layers' link**, at that family and K3StoredThree.lean's terms for the committed
table. -/
theorem lay_model_at (hc : Mg.constr = P5J.constrQAt hd put H headPart digitsPart)
    (hhid : ∀ w, H.hid w = hidAtF X (fun j => szOf (tls j))
      (seatBy (fLay D.layout num) X fun j => szOf (tls j)) (tok w)
      (fun j => Desc.Sound.readAt D.codes arr ms N j w))
    (hb : ∀ j w, H.base j w → BaseSegF (fun j => szOf (tls j))
      (seatBy (fLay D.layout num) X fun j => szOf (tls j))
      (fun j => Desc.Sound.readAt D.codes arr ms N j w) j)
    (fit : sizesFit X (fun j => szOf (tls j)) = true)
    (reads : ∀ w : Desc.Wit (CellsW rows cols) Tok MsgT, ReadsOne X (fun j => szOf (tls j))
      (seatBy (fLay D.layout num) X fun j => szOf (tls j))
      (fun j => Desc.Sound.readAt D.codes arr ms N j w))
    (hg : g < 12) (hxl : x.link = m) (hl : m = 2 * g) (hhd : m ≠ hd)
    (T : linkTieB X D rad num idx x.link (tls x.link) = true)
    (O1 : OneNumber X D rad num idx tls x.link seatT arr id)
    (Own : OwnNamed X D num tls x.link arr ms N) (hgs : GroupsSeated ms N)
    (hq : m / Desc.First.Look.stepOf X = g) (HL : LayOK set x)
    (hpw : Mg.pinW = pinWOf decT) (hdec : H.dec = fun a y => decT y.cell a) (z : P) :
    ∀ s y w, LaySays x (pubAt X (m / Desc.First.Look.stepOf X)) (tls x.link) D rad (oWc rows cols)
        wOfC rows cols (layMs x D rad (oWc rows cols) seatT arr msgWc w) →
      Mg.constr m .small (z, s) y w → Mg.pinW (z, s) y w →
      Mg.constr m .lookCalls (z, s) y w ∧ Mg.constr m .rider (z, s) y w :=
  lay_model_hid tls (fun w j => Desc.Sound.readAt D.codes arr ms N j w) tok seatT arr msgWc hc hhid
    hb fit reads hg hxl hl hhd hq T HL (fun w => symsAre_readAt_lay msgWc T O1 Own hgs w) z
    (hW_conduit seatT arr hpw hdec z)

/-- **Lean lays it in the field's place.** -/
theorem lay_model_fits (G : Desc.FileDescription Xi)
    (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
      Option ((attSg x D rad).om i).Smp)
    (smpW : Desc.First.S → Option (oWc rows cols).Smp) (strW : Fr.E.Str → (oWc rows cols).Str)
    (claim : Aff → Cl) (links : List ModelPart) (ps : List Desc.Place) (k : ℕ)
    (Yes : Desc.First.S × Fr.E.Str → Desc.First.S × Fr.E.Str → Prop)
    (Rc : Desc.First.S × Fr.E.Str → Prop)
    (hc : Mg.constr = P5J.constrQAt hd put H headPart digitsPart)
    (hhid : ∀ w, H.hid w = hidAtF X (fun j => szOf (tls j))
      (seatBy (fLay D.layout num) X fun j => szOf (tls j)) (tok w)
      (fun j => Desc.Sound.readAt D.codes arr ms N j w))
    (hb : ∀ j w, H.base j w → BaseSegF (fun j => szOf (tls j))
      (seatBy (fLay D.layout num) X fun j => szOf (tls j))
      (fun j => Desc.Sound.readAt D.codes arr ms N j w) j)
    (fit : sizesFit X (fun j => szOf (tls j)) = true)
    (reads : ∀ w : Desc.Wit (CellsW rows cols) Tok MsgT, ReadsOne X (fun j => szOf (tls j))
      (seatBy (fLay D.layout num) X fun j => szOf (tls j))
      (fun j => Desc.Sound.readAt D.codes arr ms N j w))
    (hg : g < 12) (hxl : x.link = m) (hl : m = 2 * g) (hhd : m ≠ hd)
    (T : linkTieB X D rad num idx x.link (tls x.link) = true)
    (O1 : OneNumber X D rad num idx tls x.link seatT arr id)
    (Own : OwnNamed X D num tls x.link arr ms N) (hgs : GroupsSeated ms N)
    (hq : m / Desc.First.Look.stepOf X = g) (HL : LayOK set x)
    (hpw : Mg.pinW = pinWOf decT) (hdec : H.dec = fun a y => decT y.cell a) (z : P)
    (O : LayTiesR (Fr := Fr) G x (pubAt X (m / Desc.First.Look.stepOf X)) (tls x.link) D rad
      (oWc rows cols) wOfC rows cols set seatT arr smp smpW strW msgWc claim N Mg links ps z k m
      Yes Rc) :
    LayTiesR (Fr := Fr) G x (pubAt X (m / Desc.First.Look.stepOf X)) (tls x.link) D rad
      (oWc rows cols) wOfC rows cols set seatT arr smp smpW strW msgWc claim N Mg links ps z k m
      Yes Rc :=
  { O with
    model := lay_model_at tls tok seatT arr hc hhid hb fit reads hg hxl hl hhd T O1 Own hgs hq HL
      hpw hdec z }

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.att_model_at
#print axioms VerifiableInference.OnPublicFiles.att_model_fits
#print axioms VerifiableInference.OnPublicFiles.lay_model_at
#print axioms VerifiableInference.OnPublicFiles.lay_model_fits
