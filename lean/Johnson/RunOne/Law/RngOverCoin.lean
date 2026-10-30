-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/RngOverCoin.lean: THE RANGES' TEST's SEAT OF A KEY FILE IS A SEAT «OVER» THE KIND K12's BLOCK, in the words of Johnson/Desc/K12/Coin/Over.lean (structure Over): so a law of the kind's block at its own record goes over to the seated block by that file's leads_over. Statements with proofs.
OBJECT. `rangesTest laid back N` (Johnson/Desc/Key/Ranges.lean) against the kind's block `proximityTestKind guardedProximityTestParts (rangesParams N)`.
USER. Johnson/RunOne/Law/K12SeatsLaw.lean (law_rng), K12SeatsHeld.lean (law_rng_held) and K12AtField.lean call over_keyD. Nobody calls leads_keyD yet.
LETTERS. The piece p is free; hb (its block is the kind's at the place's numbers) is closed by rfl at the piece of which the plain law speaks. In leads_keyD the kind's law is a premise.
  over_rng: for every piece p whose block is the kind's at the place's numbers: Over p (rangesTest laid back N) R R', with R s t: the seat's entering (reading, then asking) returns t at s; R' s t' s': the seat's leaving lays t' back as s'. Any state, any two halves, any type of claims.
  over_keyD: the same at a key file's own halves (Key.enterRanges one, Key.leaveRanges) and type of claims.
  leads_keyD: that file's leads_over there, written out.
All three fields are Johnson/RunOne/Law/RngOver.lean's. Nothing on soundness: leads_keyD takes the kind's law as a premise. Its promise, "for every t that the entering returns …", holds for want of a case where the entering fails: rightly: there the block says no.
THE PIECE «over p B'» HOLDS THE BARE BLOCK AT ITS CHAIN's OWN STATE. In the dress in which a file's rule of composition holds a block (below the prime's test; lifted over what was handed): Johnson/RunOne/Law/K12SeatsHeld.lean.

-/
import Johnson.RunOne.Law.RngOver
import Johnson.Desc.K12.Coin.Over

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.RngOverCoin
open _root_.Run.PQ (CK)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Coin (Over leads_over)
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (FirstState Claim enterRanges leaveRanges)

variable {σ Cl W : Type} {C : CK} {F : Frame}

/-- The seat stands over the kind's block. -/
theorem over_rng (laid : σ → Except String RangesLaid) (back : σ → T12 → Except String σ) (N : H2U.PlaceNums)
    (p : Piece C F T12 Unit W) (hb : p.b = proximityTestKind guardedProximityTestParts (rangesParams N)) :
    Over p (rangesTest laid back N : Block σ Cl) (fun s t => enterAndAsk laid (rangesParams N) s = .ok t)
      (fun s t' s' => back s t' = .ok s') where
  rounds := by rw [hb, RngOver.rounds_over]
  step := fun s rs cols s' k h => by
    rw [hb]
    exact RngOver.step_over laid back N F.ft s rs cols s' k h
  one := fun s t₁ t₂ h₁ h₂ => RngOver.enter_one laid N s t₁ t₂ h₁ h₂

theorem over_keyD (one : OnBytes.Params.OneTime) (N : H2U.PlaceNums) (p : Piece C F T12 Unit W)
    (hb : p.b = proximityTestKind guardedProximityTestParts (rangesParams N)) :
    Over p (rangesTest (Key.enterRanges one) Key.leaveRanges N : Block Key.FirstState Key.Claim)
      (fun s t => enterAndAsk (Key.enterRanges one) (rangesParams N) s = .ok t) (fun s t' s' => Key.leaveRanges s t' = .ok s') :=
  over_rng (Key.enterRanges one) Key.leaveRanges N p hb

/-- **The kind's law at its own record goes over to the block that a key file seats.** -/
theorem leads_keyD (one : OnBytes.Params.OneTime) (N : H2U.PlaceNums) (p : Piece C F T12 Unit W)
    (hb : p.b = proximityTestKind guardedProximityTestParts (rangesParams N)) (on : T12 × F.E.Str → Prop)
    (Q : T12 × F.E.Str → T12 × F.E.Str → Prop) (h : p.ior.red.Leads on Q p.err) :
    (VerifiableInference.Desc.K12.Coin.«over» p (rangesTest (Key.enterRanges one) Key.leaveRanges N : Block Key.FirstState Key.Claim)).ior.red.Leads
      (fun a => ∀ t, enterAndAsk (Key.enterRanges one) (rangesParams N) a.1 = .ok t → on (t, a.2))
      (fun a b => ∃ t t', enterAndAsk (Key.enterRanges one) (rangesParams N) a.1 = .ok t ∧ Key.leaveRanges a.1 t' = .ok b.1 ∧
        Q (t, a.2) (t', b.2))
      (VerifiableInference.Desc.K12.Coin.«over» p (rangesTest (Key.enterRanges one) Key.leaveRanges N : Block Key.FirstState Key.Claim)).err :=
  leads_over p _ _ _ (over_keyD one N p hb) on Q h

end Johnson.RunOne.Law.RngOverCoin

#print axioms Johnson.RunOne.Law.RngOverCoin.over_rng
#print axioms Johnson.RunOne.Law.RngOverCoin.over_keyD
#print axioms Johnson.RunOne.Law.RngOverCoin.leads_keyD
