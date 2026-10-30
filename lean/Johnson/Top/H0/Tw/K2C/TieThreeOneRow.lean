-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/TieThreeOneRow.lean: code switching: THE PREMISE hone OF hAt_at_place AND ITS
THREE ARMS (Tw/K2C/TieThreeAt.lean · TieThreeArms.lean): «at each entry of the place's frame the
front's statement stores just one OOD answers' row»: FROM THE FIRST TIE's TEST, TWO INVARIANTS OF
THE VERIFIER's STATE AT THE FRONT's STATEMENT, AND TWO CLOSED FACTS. One theorem. A JOINING: every
step is a call. NO SUB-PROTOCOL IMPORTS THIS FILE.
  hone_at_place   by K2.hone_of_both (Tw/K2C/OneStored.lean) and one_answer_of_test
                  (K2Caller/OneAnswer.lean), at the frame that pub12_of_twelve names
LEFT, BY NAME: hInv (K2.SampleGoodS · K2.AnsweredStored at the front's statement, asked under the
table of joints' promise, Rch and «no mark») · hty (the written front's kept messages have the typed
kept members' shapes: keptTyped_at, K2Caller/KeptTypedFull.lean, AT THE FULL SIZE's
TABLE ALONE) · hs (keptShapeB r; at the written tables: Johnson.G.keptShape_full |
keptShape_small, by Lean's kernel) · and hT1, hnd h0f hcs hpub, which hAt_at_place takes already.
LIMITS. No premise is shown met here. No soundness is claimed. On hiding nothing.

-/
import Johnson.Top.H0.Tw.K2C.TieThreeAt
import Johnson.Top.H0.Tw.K2C.OneStored
import Johnson.Top.H0.K2Caller.OneAnswer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers)
open VerifiableInference.Desc.First.K2Hands
open Johnson.G (keptShapeB)
open _root_.Tw.K2 (switchNotices)

/-- **hone at a place.** -/
theorem hone_at_place {F : Frame} {P Cells Tok : Type} {r : SwRow} (p : K2.P2)
    (enter : Rec → Except String Rec)
    (N : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place) (z : P) (Rch : ℕ → Rec × F.E.Str → Prop)
    (k n0 grp rows : ℕ) (f₀ : _root_.Tw.K2.Front) (W : SwitchFrame) (olds : List ℕ)
    (hnd : olds.Nodup) (h0f : K2.frameAt f₀ = some W) (hcs : f₀.st.codes = r.cs)
    (hpub : frontPubB r.l.length f₀ = true)
    (hty : keptShapes f₀ = r.kept.map fun i => (r.lo[i]?).map (·.1))
    (hs : keptShapeB r = true)
    (hT1 : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
        frontB2 f₀ W grp rows n0 olds fx = true ∧ Tied r.l (switchNotices fx.T fx.others))
    (hInv : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
        K2.SampleGoodS fx.st ∧ K2.AnsweredStored fx.st) :
    ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
        ∀ κ ∈ (placeFrame W n0 olds).kept,
          (fx.st.oracles.getD κ.old default).sampleRows.size = 1 := by
  intro a ha hrc hm t et fx hf
  obtain ⟨hB2, hTd⟩ := hT1 a ha hrc hm t et fx hf
  obtain ⟨hG, hA⟩ := hInv a ha hrc hm t et fx hf
  have P12 : Pub12 (r := r) (placeFrame W n0 olds) fx :=
    pub12_of_twelve h0f hcs hpub hnd hTd hB2
  exact K2.hone_of_both hG hA (one_answer_of_test hB2 hty hs P12.frameIs)

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.hone_at_place
