-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/K4/TermsShown.lean: THREE FACTS ON LEDGERS AT THE PLACE WHERE THE BATCHED
SUMCHECK OF THE LAYERS' OWN ROUNDS BEGINS, as the fourth claim's file asks them
(Johnson/Road/K4/Claim4.lean: hkeep, h0, htt). Statements and proofs.

  `later_fo`: the library's two notions "later" agree in what is used here: `PscRun.Later` gives
    `Fo.Later`.
  `later_terms`: the ledger that the terms' sumcheck leaves is later than the one that the norms'
    stretch was handed (by the instances of OnBytes/Desc/First/K4/HearGrows.lean).
  `kept_value` (for hkeep): a form that names filled slots alone of a ledger F0 has one value in
    the worlds of F0 and of every later ledger, at one mask row and one table of entries. It is
    `Fo.value_later`, restated for the eye.
  `tsc_target` (for htt): where a token sumcheck returns from a ledger with arrays of the right
    sizes: its record's target reads as its start form's value in the world, at the mask row 0, of
    every ledger later than the one that it leaves.
  `terms_shown` (for h0 and htt): where `hearTerms` returns from such a ledger: of the token
    sumcheck's record tT that the heard record then holds: every ledger later than the one left
    shows zeroE under tT's hiding slots, from tT.p.first on, tT.p.walk.1.length of them; and the
    target reads as said.

Limits. That the lookup's end form names filled slots alone of the ledger in front of the own
rounds (the premise of `kept_value` in its use for hkeep) is the lookup's to give: not shown here.
"Shows zeroE": the text lays these slots with the word zeroE and the factor -1: the array vp holds
zeroE there; nothing on the mask entries. One direction: from a return.
-/
import OnBytes.Desc.First.K4.HearGrows
import OnBytes.Desc.First.K4.HearCalls
import OnBytes.Desc.First.K4.HearLaws
import OnBytes.Desc.First.P1.Heard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.PscRun (Sized Filled hideRun_ok)
open OnBytes.Desc.First.Grow (Grows)
open OnBytes.Desc.First.P1 (tscIn_heard tsc_world publicPart_slot slot_worldOf pscRow_spec)

/-- The one "later" gives the other. -/
theorem later_fo {F G : Fork} (h : OnBytes.PscRun.Later F G) : Fo.Later F G :=
  ⟨h.next, h.ns, h.keep⟩

/-- The ledger at which the batched sumcheck begins is later than the one in front of the own
rounds. -/
theorem later_terms {P : Pub} {g : Nat} {fo : Forest.Heard} {F G1 G2 : Fork} {t u1 u2 : Tape}
    {H1 H : Heard} (hN : hearNorms engFl P g fo F t = some (H1, G1, u1))
    (hT : hearTerms engFl P H1 G1 u1 = some (H, G2, u2)) : Fo.Later F G2 :=
  later_fo ((Grows.later hN).trans (Grows.later hT))

variable {K : Type} [Field K] (ρ : Reading K)

/-- A form on filled slots has one value in every later ledger's world. -/
theorem kept_value {F0 F : Fork} (hL : Fo.Later F0 F) (C : Aff) (hC : Fo.FilledA F0 C)
    (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) :
    C.value ρ (F.worldOf ρ mask entry) = C.value ρ (F0.worldOf ρ mask entry) :=
  Fo.value_later ρ hL C hC mask entry

/-- **A token sumcheck's target reads as its start form's value at what a later ledger shows.** -/
theorem tsc_target {P : Array E} {lt n dY : Nat} {F G : Fork} {t u : Tape} {o : Tsc}
    (hF : Sized F) (h : Fl.tscIn P lt n dY F t = some (o, G, u)) (Hl : Fork) (hL : Fo.Later G Hl)
    (entry : ℕ → ℕ → ℕ → K) :
    ρ.val o.p.target = o.p.start.value ρ (Hl.worldOf ρ (fun _ => 0) entry) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hstart, _, _, _, v, G0, hG0, hT, _, _, _, hG⟩ :=
    tscIn_heard h
  have hF' : Sized ({ F with next := F.next + 1 } : Fork) := hF
  obtain ⟨_, hS0, _, _⟩ := hideRun_ok _ G0 F.next _ oneE hF' hG0
  have hS0' : Sized ({ G0 with next := G0.next + 1 + 2 * (P.toList.take lt).length + dY + n } :
      Fork) := hS0
  have l2 : Fo.Later G0
      ({ G0 with next := G0.next + 1 + 2 * (P.toList.take lt).length + dY + n } : Fork) :=
    ⟨by show G0.next ≤ G0.next + 1 + 2 * (P.toList.take lt).length + dY + n; omega, rfl,
      fun _ hj => ⟨hj, rfl, rfl⟩⟩
  have l3 := Fo.hideRun_later hS0' hG
  obtain ⟨e, hfill⟩ := publicPart_slot ρ hT
  have k := ((l2.trans l3).trans hL).keep F.next hfill
  rw [hstart, Aff.value_slot, slot_worldOf]
  simp only [mul_zero, sub_zero]
  rw [k.2.1, e]

/-- **What every later ledger shows of the terms' sumcheck**, where `hearTerms` returns from a
ledger with arrays of the right sizes. -/
theorem terms_shown {P : Pub} {H H' : Heard} {F G : Fork} {t u : Tape} (hF : Sized F)
    (h : hearTerms engFl P H F t = some (H', G, u)) (tT : Tsc) (hH : H'.tT = some tT) (Hl : Fork)
    (hL : Fo.Later G Hl) :
    (∀ j, tT.p.first ≤ j → j < tT.p.first + tT.p.walk.1.length → Hl.vp.getD j zeroE = zeroE) ∧
      ∀ entry : ℕ → ℕ → ℕ → K,
        ρ.val tT.p.target = tT.p.start.value ρ (Hl.worldOf ρ (fun _ => 0) entry) := by
  obtain ⟨t0, G1, u1, row, p', cT, _, cR, rfl⟩ := hearTerms_calls h
  obtain rfl : ({ t0 with p := p' } : Tsc) = tT := Option.some.inj hH
  obtain ⟨_, rfl⟩ := pscRow_some cR
  obtain ⟨_, hS1, _⟩ := tsc_world ρ (fun _ => 0) (fun _ _ _ => 0) hF cT
  have hR : G1.hideRun t0.p.first (Array.replicate t0.p.walk.1.length zeroE)
      (subE zeroE oneE) = some G := (pscRow_spec cR).2.2
  obtain ⟨_, _, hin, _⟩ := hideRun_ok G1 G _ _ _ hS1 hR
  have lR := Fo.hideRun_later hS1 hR
  refine ⟨fun j h1 h2 => ?_, fun entry => tsc_target ρ hF cT Hl (lR.trans hL) entry⟩
  have h1' : t0.p.first ≤ j := h1
  have h2' : j < t0.p.first + t0.p.walk.1.length := h2
  have q := hin (j - t0.p.first) (by rw [Array.size_replicate]; omega)
  have ej : t0.p.first + (j - t0.p.first) = j := by omega
  rw [ej] at q
  have hz : (Array.replicate t0.p.walk.1.length zeroE).getD (j - t0.p.first) zeroE = zeroE := by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  rw [(hL.keep j q.2.2.1).2.1, q.2.2.2.1, hz]

end OnBytes.Desc.First.K4

#print axioms OnBytes.Desc.First.K4.later_terms
#print axioms OnBytes.Desc.First.K4.kept_value
#print axioms OnBytes.Desc.First.K4.tsc_target
#print axioms OnBytes.Desc.First.K4.terms_shown
