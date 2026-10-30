-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/First/Look/K3CallsModel.lean: the lookup on a link's CALLS: THE FIELD "model" OF THE
TABLES' TIES (AttTies, LayTies, Johnson/Desc/First/Look/K3CallsMeanOf.lean) WHERE THE MEANING's
LETTER constr IS constrQAt (Johnson/P5J/MeansQ.lean): from what the closed caller's
relation says of the witness's messages (AttSays, LaySays) and the part "small" to the model's own
clauses on the calls: AttKey, AttRidden at an attention sub-proof; KeyField, HotField at a group of
layers. A joining of other files' theorems: no new mathematics. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: the table of joints' items constr l .lookCalls, constr l .rider.
USER: K3CallsModelAt.lean (att_model_of, lay_model_of).
  Meant: attTies_of, layTies_of (Johnson/Desc/First/Look/K3CallsAt.lean) at the
  composed meaning.
LETTERS: hd, put, H, headPart, digitsPart: constrQAt's own; msgF w: the family of readings of the
  witness's messages behind H.hid w; num, idx, tls as in Johnson/Goal/Meaning/ReadingsOneLook.lean.

How it goes. constrQAt at a part p that is not the digits' says: (p = small gives H.base l w) and,
at every matrix M that the committed table decodes to and every index i that holds M, the model's
part p at H.hid w's integers. The part "small" in front hands over H.base l w: with hbase: the
symbols are the packing of small integers. Then the four theorems of ReadingsOneLook.lean (aKey_own,
aRidden_own, gKey_own, gHot_own) end at the lists ownL, which hMA | hMG say are H.hid w's.

THE PREMISES, BY NAME: hc (constr is constrQAt: at the composed meaning by rfl) · hMA | hMG (H.hid
  w's list of the sub-proof is ownL at msgF w: hidAtF_MA | hidAtF_MG give it
  under two premises of their own) · hbase · hm (SymsAre) · T (linkTieB) · AttOK | LayOK · hT, hU
  (attention's keys) · hW (the layers' keys: the committed weights are the index's matrix's).

AT THE LAYERS THE FIELD AS LayAtTable HAS IT TODAY IS NOT REACHED BY THIS ROAD (by reading: no
counterexample is typed): KeyField is asked at i.mat for every index i that holds the matrix M to
which THE STRINGS decode, while LaySays speaks of THE WITNESS's cells: what ties the two is the item
pinW, which stands in the row's ctx and which the field does not hand over. So lay_model_of takes
Mg.pinW (z, s) y w as one premise more: the field is to turn likewise (the row's proof has it at
that place).

Main names: `att_model_of`, `lay_model_of`.

Limits. A rule over letters: none of the premises is shown at any term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.P5J.MeansQ
import Johnson.Desc.First.Look.K03Means
import Johnson.Desc.First.Look.K3CallerLayTests
import Johnson.Goal.Meaning.ReadingsOneLook

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Inst.Model Inst.Model.All
open OnBytes.Road.Rows.Norms (KeyField HotField)
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.OnPublicFiles.Flat (Holds)
open _root_.Meaning (ownL SymsAre linkTieB BaseSegF seatBy fLay Msgs AttKey AttRidden gKey_own
  gHot_own aKey_own aRidden_own)

section
variable {P Cells Tok : Type} {rows cols : ℕ} {X : Verify.Public}
  {set : Params.Setting} {x : Desc.First.Look.Place} {D : Desc.First.Look.Sent}
  {rad : OracleShape → ℕ} {num : ℕ → ℕ → ℕ} {idx : ℕ → ℕ} (tls : ℕ → HTailF2)
  (msgF : Desc.Wit Cells Tok MsgT → ℕ → Msgs) {g l hd : ℕ}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  {Mg : Meaning P (Desc.Wit Cells Tok MsgT)}
  {put : P5J.TReq → Fin ppref.V → P5J.TReq}
  {H : P5J.HidAt X P (Desc.Wit Cells Tok MsgT) rows cols}
  {headPart : P5J.TPart → Cm.Idx → P × P5J.TS → Desc.Strs → Desc.Wit Cells Tok MsgT → Prop}
  {digitsPart : ℕ → P × P5J.TS → Desc.Strs → Desc.Wit Cells Tok MsgT → Prop}

/-- The part "small" hands over "the symbols are the packing of small integers". -/
theorem small_base (a : P × P5J.TS) (y : Desc.Strs) (w : Desc.Wit Cells Tok MsgT)
    (h : P5J.constrQAt hd put H headPart digitsPart l .small a y w) : H.base l w := by
  unfold P5J.constrQAt at h
  rw [if_neg (show ¬ ((.small : P5J.TPart) = .lookDigits) by decide)] at h
  exact h.1 rfl

/-- **model, at an attention link.** -/
theorem att_model_of (hc : Mg.constr = P5J.constrQAt hd put H headPart digitsPart)
    (hxl : x.link = l) (hl : l = 2 * g + 1) (hhd : l ≠ hd)
    (T : linkTieB X D rad num idx x.link (tls x.link) = true)
    (HA : AttOK set x (Road.Hd.shapeA X g) (tls x.link) D rad)
    (hMA : ∀ w, (H.hid w).MA g = ownL X D num tls (msgF w) (2 * g + 1))
    (hbase : ∀ w, H.base l w →
      BaseSegF (fun j => szOf (tls j)) (seatBy (fLay D.layout num) X fun j => szOf (tls j))
        (msgF w) x.link)
    (hm : ∀ w, SymsAre X D rad num idx tls (msgF w) x.link (attMs x D rad seatT arr w))
    (hT : TabsAre (Road.Hd.shapeA X g) x.fs)
    (hU : ∀ c : Fin 4, (Road.L5.dimOf (Road.Hd.shapeA X g)).used c ≤
      2 ^ Cb.LdLkp.Port.nOf x.fs c) (z : P) :
    ∀ s y w, AttSays x (Road.Hd.shapeA X g) (tls x.link) D rad (attMs x D rad seatT arr w) →
      Mg.constr l .small (z, s) y w →
      Mg.constr l .lookCalls (z, s) y w ∧ Mg.constr l .rider (z, s) y w := by
  intro s y w hS hsm
  rw [hc] at hsm ⊢
  have hB := hbase w (small_base (z, s) y w hsm)
  have hl' : x.link = 2 * g + 1 := hxl.trans hl
  have kA : AttKey (Road.Hd.shapeA X g) ((H.hid w).MA g) := by
    rw [hMA]
    exact aKey_own tls (msgF w) extNone Unit hl' T HA ((), ()) (attMs x D rad seatT arr w, ())
      (att_relR HA _ hS) (hm w) hB hT hU
  have kR : AttRidden (Road.Hd.shapeA X g) ((H.hid w).MA g) := by
    rw [hMA]
    exact aRidden_own tls (msgF w) extNone Unit hl' T HA ((), ()) (attMs x D rad seatT arr w, ())
      (att_relR HA _ hS) (hm w) hB
  have e2 : l / 2 = g := by omega
  have hodd : ¬ l % 2 = 0 := by omega
  refine ⟨?_, ?_⟩
  · unfold P5J.constrQAt
    rw [if_neg (show ¬ ((.lookCalls : P5J.TPart) = .lookDigits) by decide)]
    refine ⟨fun h => absurd h (by decide), fun M i _ _ => ?_⟩
    rw [if_neg hhd, if_neg hodd, e2]
    exact kA
  · unfold P5J.constrQAt
    rw [if_neg (show ¬ ((.rider : P5J.TPart) = .lookDigits) by decide)]
    refine ⟨fun h => absurd h (by decide), fun M i _ _ => ?_⟩
    rw [if_neg hhd, if_neg hodd, e2]
    exact kR

variable {oW : Cb.OMsg Cb.Gl.E} {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc : ℕ}
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg)

/-- **model, at a layers' link**: with the item pinW in front. -/
theorem lay_model_of (hc : Mg.constr = P5J.constrQAt hd put H headPart digitsPart)
    (hxl : x.link = l) (hl : l = 2 * g) (hhd : l ≠ hd) (hq : l / Desc.First.Look.stepOf X = g)
    (T : linkTieB X D rad num idx x.link (tls x.link) = true) (HL : LayOK set x)
    (hMG : ∀ w, (H.hid w).MG g = ownL X D num tls (msgF w) (2 * g))
    (hbase : ∀ w, H.base l w →
      BaseSegF (fun j => szOf (tls j)) (seatBy (fLay D.layout num) X fun j => szOf (tls j))
        (msgF w) x.link)
    (hm : ∀ w, SymsAre X D rad num idx tls (msgF w) x.link
      (ownPart (layMs x D rad oW seatT arr msgW w))) (z : P)
    (hW : ∀ s y w M (i : Cm.Idx), Mg.pinW (z, s) y w → H.dec (z, s) y = some M → Holds M i →
      WeightsAre x (tls x.link) D rad oW wOf nr nc g (layMs x D rad oW seatT arr msgW w) i.mat) :
    ∀ s y w, LaySays x (pubAt X (l / Desc.First.Look.stepOf X)) (tls x.link) D rad oW wOf nr nc
        (layMs x D rad oW seatT arr msgW w) →
      Mg.constr l .small (z, s) y w → Mg.pinW (z, s) y w →
      Mg.constr l .lookCalls (z, s) y w ∧ Mg.constr l .rider (z, s) y w := by
  intro s y w hS hsm hpw
  rw [hq] at hS
  rw [hc] at hsm ⊢
  have hB := hbase w (small_base (z, s) y w hsm)
  have hl' : x.link = 2 * g := hxl.trans hl
  have e2 : l / 2 = g := by omega
  have hev : l % 2 = 0 := by omega
  refine ⟨?_, ?_⟩
  · unfold P5J.constrQAt
    rw [if_neg (show ¬ ((.lookCalls : P5J.TPart) = .lookDigits) by decide)]
    refine ⟨fun h => absurd h (by decide), fun M i hM hi => ?_⟩
    rw [if_neg hhd, if_pos hev, e2]
    show KeyField (Verify.layerShape X.P) X.layers.sc X.y g ((H.hid w).MG g) i.mat
    rw [hMG]
    exact gKey_own tls (msgF w) extNone Unit hl' T HL ((), ())
      (layMs x D rad oW seatT arr msgW w, ()) (lay_relR (pubAt X g) _ hS) (hm w) hB i.mat
      (hW s y w M i hpw hM hi)
  · unfold P5J.constrQAt
    rw [if_neg (show ¬ ((.rider : P5J.TPart) = .lookDigits) by decide)]
    refine ⟨fun h => absurd h (by decide), fun M i _ _ => ?_⟩
    rw [if_neg hhd, if_pos hev, e2]
    show HotField (Verify.layerShape X.P) X.layers.sc X.y g ((H.hid w).MG g) i.mat _
    rw [hMG]
    exact gHot_own tls (msgF w) extNone Unit hl' T ((), ())
      (layMs x D rad oW seatT arr msgW w, ()) (lay_relR (pubAt X g) _ hS) (hm w) hB i.mat _

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.att_model_of
#print axioms VerifiableInference.OnPublicFiles.lay_model_of
