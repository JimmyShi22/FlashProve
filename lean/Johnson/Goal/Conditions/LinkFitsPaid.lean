-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
This file states no goal.
Johnson/Goal/Conditions/LinkFitsPaid.lean: TWO OF THE THREE PREMISES THAT STAND
BESIDE "the link's decision says yes" in linkFits_of_yes (Johnson/Goal/Conditions/LinkFitsHome.lean)
ARE PAID: at what the kit draws each external opening reads as many positions as it counts; every
stored symbol that is read carries its position.

Main names.
  at_three        round number 3 of the written rounds' data counts 124 positions.
  full_full       everyOpeningHasItsDraws at every list of challenges.
  enc_pos         every symbol of an encoded index carries its position, at the home's own letters.
  carries_home    symbolsCarryTheirPositions at two encodings of an index, at every list of challenges.

How. fr_xs (OnBytes/Slice/FullRecSz.lean); fitsDrawn_run (Johnson/Prover/Link/ChainRounds.lean);
carriesX_of (Johnson/Prover/Link/LinkFrame.lean) at fr_opens (Johnson/Prover/Link/ChainAtFull.lean);
the encoding is honestTab (OnBytes/Slice/Honest.lean), by unfolding.

Limits. Nothing on the third premise (what the stored strings mean). Nothing on the decision.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.LinkFitsHome
import Johnson.Prover.Link.ChainAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD Rom
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run (ckP)
open TypedOracleCompiler.Run.PQ (drawnSL symbolsCarryTheirPositions uL)
open _root_.Run.PQ (everyOpeningHasItsDraws SgX)
open _root_.Iop (twoExternalStrings Rho)
open PV.EntryFive (dsF xsF)

/-- Round number 3 of the written rounds' data counts 124 positions. -/
theorem at_three : ∃ w, dsF[3]? = some w ∧ w.entry.poss = 124 := by
  refine ⟨TypedOracleCompiler.Run.PQ.ofLib (frRd 3), ?_, ?_⟩
  · show ((_root_.Run.PQ.rds wFull).map TypedOracleCompiler.Run.PQ.ofLib)[3]? = _
    rw [rdsFull_eq]
    rfl
  · decide +kernel

/-- **At what the kit draws, each of the two external openings reads as many positions as it
counts.** -/
theorem full_full (ρ : Rho (uL (ckP .two) dsF)) :
    everyOpeningHasItsDraws xsF (drawnSL (ckP .two) dsF ρ) = true := by
  obtain ⟨w, hw, hp⟩ := at_three
  have hF := Johnson.Prover.Link.fitsDrawn_run dsF ρ
  have hlt : 3 < dsF.length := by
    by_contra c
    rw [List.getElem?_eq_none (Nat.le_of_not_lt c)] at hw
    cases hw
  have hlt' : 3 < (drawnSL (ckP .two) dsF ρ).length := by rw [← hF.length_eq]; exact hlt
  have h3 := (List.forall₂_iff_get.1 hF).2 3 hlt hlt'
  have ew : dsF.get ⟨3, hlt⟩ = w := by
    have := List.getElem?_eq_getElem hlt
    rw [hw] at this
    exact (Option.some.inj this).symm
  rw [ew] at h3
  have hD : (drawnSL (ckP .two) dsF ρ)[3]? = some ((drawnSL (ckP .two) dsF ρ).get ⟨3, hlt'⟩) :=
    List.getElem?_eq_getElem hlt'
  have hl : ((drawnSL (ckP .two) dsF ρ).get ⟨3, hlt'⟩).poss.length = 124 := h3.poss.trans hp
  show everyOpeningHasItsDraws frD.xs _ = true
  rw [fr_xs]
  unfold everyOpeningHasItsDraws _root_.Run.PQ.XO.raw
  simp only [List.all_cons, List.all_nil, Bool.and_true, hD, List.length_take, List.length_drop, hl]
  decide

/-- Every symbol of an encoded index carries its position. -/
theorem enc_pos (b : PublicFiles → ℕ) (Z : PublicFiles) (i : (homeR b Z).Index) (r : (homeR b Z).protocol.EncodingRandomness)
    (x : Fin (2 ^ frS.P.T.a)) : ((homeR b Z).protocol.encodeIndex i r x).1 = x.val := rfl

/-- **Every stored symbol that is read carries its position.** -/
theorem carries_home (b : PublicFiles → ℕ) (Z : PublicFiles) (i : (homeR b Z).Index) (r r' : (homeR b Z).protocol.EncodingRandomness)
    (ρ : Rho (uL (ckP .two) dsF)) :
    symbolsCarryTheirPositions frS.P.T.a dsF xsF (drawnSL (ckP .two) dsF ρ)
      ((homeR b Z).protocol.encodeIndex i r, (homeR b Z).protocol.encodeIndex i r') = true :=
  Johnson.Prover.Link.carriesX_of dsF frS.P.T.a xsF _ _ Johnson.Prover.Link.fr_opens
    fun w x h => by
      cases w
      · exact enc_pos b Z i r ⟨x, h⟩
      · exact enc_pos b Z i r' ⟨x, h⟩

end FlashProve

#print axioms FlashProve.at_three
#print axioms FlashProve.full_full
#print axioms FlashProve.enc_pos
#print axioms FlashProve.carries_home
