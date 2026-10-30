-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/First/Look/K3CallsModelAt.lean: the lookup on a link's CALLS: THE FIELD "model" WHERE
THE WITNESS IS READ AS hidAtSeat READS IT (Johnson/P5J/MeansQ.lean): att_model_of and
lay_model_of (Johnson/Desc/First/Look/K3CallsModel.lean) WITH THREE OF THEIR PREMISES PAID: hMA,
hMG (the hidden lists are ownL at the family of readings) and hbase (the part "small" says that
the symbols are the packing of small integers). A joining of other files' theorems: no new
mathematics. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: the table of joints' items constr l .lookCalls, constr l .rider.
USER: K3CallsModelFits.lean (att_model_hid, lay_model_hid).
  Meant: the field model of AttTiesR, LayTiesR at the composed meaning.
LETTERS: those of K3CallsModel.lean; tok: the witness's token as a number below the vocabulary's
  size; msgF w: the family of readings; at hidAtSeat: msgF w k := readAt cs arr ms N k w.

THE TWO PREMISES ON H, BY NAME: hhid : H.hid w is hidAtF at the sizes szOf (tls
  j), the seats off the layout by the label, and msgF w · hb : H.base k w gives BaseSegF there. AT
  hidAtSeat BOTH ARE rfl: `hidAtSeat_hid`, `hidAtSeat_base`.
PAID WITH THEM: hMA, hMG: by hidAtF_MA, hidAtF_MG
  (Johnson/Goal/Meaning/HidFamily.lean) UNDER fit (sizesFit: a test on the public parameters) AND
  reads (ReadsOne at msgF w: at readAt: readsOne_readAt, Johnson/P5J/WordsAtQ.lean).

Main names: `att_model_hid`, `lay_model_hid`.

Limits. A rule over letters. LEFT: linkTieB, SymsAre, fit, reads; hW at the layers.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsModel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Inst.Model Inst.Model.All
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning Numbers)
open VerifiableInference.OnPublicFiles.Flat (Holds)
open _root_.Meaning (ownL SymsAre linkTieB BaseSegF seatBy fLay Msgs hidAtF hidAtF_MA hidAtF_MG
  ReadsOne sizesFit)

/-! ## At hidAtSeat the two premises are rfl -/

section
variable {P Cells Tok : Type} {rows cols : ℕ} (X : Verify.Public) (cs : OnBytes.Codes)
  (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (s : ℕ → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (tokV : Tok → Fin ppref.V)
  (req : P × P5J.TS → P5J.TReq)
  (dec : P × P5J.TS → Desc.Strs → Option (Fin rows → Fin cols → Flat.GE))
  (h1 : SeatsNamed arr N s seat) (h2 : GroupsSeated ms N)

theorem hidAtSeat_hid (w : Desc.Wit Cells Tok MsgT) :
    (P5J.hidAtSeat X cs arr ms N s seat tokV req dec h1 h2).hid w =
      hidAtF X s seat (tokV w.tok) fun k => readAt cs arr ms N k w := rfl

theorem hidAtSeat_base (k : ℕ) (w : Desc.Wit Cells Tok MsgT) :
    (P5J.hidAtSeat X cs arr ms N s seat tokV req dec h1 h2).base k w =
      BaseSegF s seat (fun k => readAt cs arr ms N k w) k := rfl

end

section
variable {P Cells Tok : Type} {rows cols : ℕ} {X : Verify.Public}
  {set : Params.Setting} {x : Desc.First.Look.Place} {D : Desc.First.Look.Sent}
  {rad : OracleShape → ℕ} {num : ℕ → ℕ → ℕ} {idx : ℕ → ℕ} (tls : ℕ → HTailF2)
  (msgF : Desc.Wit Cells Tok MsgT → ℕ → Msgs) (tok : Desc.Wit Cells Tok MsgT → Fin ppref.V)
  {g l hd : ℕ}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  {Mg : Meaning P (Desc.Wit Cells Tok MsgT)}
  {put : P5J.TReq → Fin ppref.V → P5J.TReq}
  {H : P5J.HidAt X P (Desc.Wit Cells Tok MsgT) rows cols}
  {headPart : P5J.TPart → Cm.Idx → P × P5J.TS → Desc.Strs → Desc.Wit Cells Tok MsgT → Prop}
  {digitsPart : ℕ → P × P5J.TS → Desc.Strs → Desc.Wit Cells Tok MsgT → Prop}

/-- **model, at an attention link**, where the witness is read by hidAtF. -/
theorem att_model_hid (hc : Mg.constr = P5J.constrQAt hd put H headPart digitsPart)
    (hhid : ∀ w, H.hid w = hidAtF X (fun j => szOf (tls j))
      (seatBy (fLay D.layout num) X fun j => szOf (tls j)) (tok w) (msgF w))
    (hb : ∀ k w, H.base k w → BaseSegF (fun j => szOf (tls j))
      (seatBy (fLay D.layout num) X fun j => szOf (tls j)) (msgF w) k)
    (fit : sizesFit X (fun j => szOf (tls j)) = true)
    (reads : ∀ w, ReadsOne X (fun j => szOf (tls j))
      (seatBy (fLay D.layout num) X fun j => szOf (tls j)) (msgF w))
    (hg : g < 12) (hxl : x.link = l) (hl : l = 2 * g + 1) (hhd : l ≠ hd)
    (T : linkTieB X D rad num idx x.link (tls x.link) = true)
    (HA : AttOK set x (Road.Hd.shapeA X g) (tls x.link) D rad)
    (hm : ∀ w, SymsAre X D rad num idx tls (msgF w) x.link (attMs x D rad seatT arr w))
    (hT : TabsAre (Road.Hd.shapeA X g) x.fs)
    (hU : ∀ c : Fin 4, (Road.L5.dimOf (Road.Hd.shapeA X g)).used c ≤
      2 ^ Cb.LdLkp.Port.nOf x.fs c) (z : P) :
    ∀ s y w, AttSays x (Road.Hd.shapeA X g) (tls x.link) D rad (attMs x D rad seatT arr w) →
      Mg.constr l .small (z, s) y w →
      Mg.constr l .lookCalls (z, s) y w ∧ Mg.constr l .rider (z, s) y w :=
  att_model_of tls msgF seatT arr hc hxl hl hhd T HA
    (fun w => by
      rw [hhid]
      exact hidAtF_MA fit (reads w) (tok w) hg)
    (fun w h => by
      rw [hxl]
      exact hb l w h) hm hT hU z

variable {oW : Cb.OMsg Cb.Gl.E} {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc : ℕ}
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg)

/-- **model, at a layers' link**, where the witness is read by hidAtF. -/
theorem lay_model_hid (hc : Mg.constr = P5J.constrQAt hd put H headPart digitsPart)
    (hhid : ∀ w, H.hid w = hidAtF X (fun j => szOf (tls j))
      (seatBy (fLay D.layout num) X fun j => szOf (tls j)) (tok w) (msgF w))
    (hb : ∀ k w, H.base k w → BaseSegF (fun j => szOf (tls j))
      (seatBy (fLay D.layout num) X fun j => szOf (tls j)) (msgF w) k)
    (fit : sizesFit X (fun j => szOf (tls j)) = true)
    (reads : ∀ w, ReadsOne X (fun j => szOf (tls j))
      (seatBy (fLay D.layout num) X fun j => szOf (tls j)) (msgF w))
    (hg : g < 12) (hxl : x.link = l) (hl : l = 2 * g) (hhd : l ≠ hd)
    (hq : l / Desc.First.Look.stepOf X = g)
    (T : linkTieB X D rad num idx x.link (tls x.link) = true) (HL : LayOK set x)
    (hm : ∀ w, SymsAre X D rad num idx tls (msgF w) x.link
      (ownPart (layMs x D rad oW seatT arr msgW w))) (z : P)
    (hW : ∀ s y w M (i : Cm.Idx), Mg.pinW (z, s) y w → H.dec (z, s) y = some M → Holds M i →
      WeightsAre x (tls x.link) D rad oW wOf nr nc g (layMs x D rad oW seatT arr msgW w) i.mat) :
    ∀ s y w, LaySays x (pubAt X (l / Desc.First.Look.stepOf X)) (tls x.link) D rad oW wOf nr nc
        (layMs x D rad oW seatT arr msgW w) →
      Mg.constr l .small (z, s) y w → Mg.pinW (z, s) y w →
      Mg.constr l .lookCalls (z, s) y w ∧ Mg.constr l .rider (z, s) y w :=
  lay_model_of tls msgF seatT arr msgW hc hxl hl hhd hq T HL
    (fun w => by
      rw [hhid]
      exact hidAtF_MG fit (reads w) (tok w) hg)
    (fun w h => by
      rw [hxl]
      exact hb l w h) hm z hW

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.hidAtSeat_hid
#print axioms VerifiableInference.OnPublicFiles.hidAtSeat_base
#print axioms VerifiableInference.OnPublicFiles.att_model_hid
#print axioms VerifiableInference.OnPublicFiles.lay_model_hid
