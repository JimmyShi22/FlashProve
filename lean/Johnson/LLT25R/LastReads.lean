-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastReads.lean: THE TWO CONDITIONS ON THE TABLE's LETTERS THAT ROWS 1 AND 3 OF
THE LAST CHAIN ARE LEFT WITH (`PromReadsBelow`, Johnson/Desc/Last/ShapeRows.lean; `PinsReadBelow`,
Johnson/Desc/Sound/QuietRows.lean) FROM THE TABLE's FILES' OWN CONDITIONS
(`OcReadsBelow lo Oc`, Johnson/Desc/Sound/OcRides.lean; `ReadsTree Mg Pm`,
Johnson/Desc/Sound/OmegaCrosses.lean) AND THREE COMPARISONS OF NUMBERS. General in every letter.
  `promReadsBelow_of`: OcReadsBelow lo Oc, ReadsTree Mg Pm and "Omega's tree's number is below lo"
    give PromReadsBelow N Pm Oc lo.
  `pinsReadBelow_of`: ReadsTree Mg Pm, the table's files' premise (P) in their own words
    (Johnson/Desc/Sound/PointMake.lean:33, RidesMake.lean:37: the slot's pins read the oracles
    through their tenant's tree alone) and "W's, the index masks' and Omega's trees' numbers are
    below lo" give PinsReadBelow N Mg ML lo.
Why. The table's files pay their two conditions at their own fillings (`ocEndReadsBelow`,
`readsTree_sig`, `pin₁_col_sig`); the rules of ShapeRows.lean and QuietRows.lean ask theirs. This
file is the bridge: no new content.
Limits. The comparisons of numbers are premises: at a seated piece lo is its base. Nothing on
soundness.
-/
import Johnson.Desc.Last.ShapeRows
import Johnson.Desc.Sound.LastProm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LLT25
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last

variable {S₂ S₃ P₁ Wt : Type} (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt) (ML : MeaningL S₃ Wt)
  (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop)

/-- **The promise's two parts that read the strings read them below lo.** -/
theorem promReadsBelow_of {lo : Nat} (hOc : OcReadsBelow lo Oc) (hR : ReadsTree Mg Pm)
    (hO : (N.tenant .oOmega).1 < lo) : PromReadsBelow N Pm Oc lo :=
  fun y y' hc hl =>
    ⟨fun x h => hOc x y y' hc hl h,
      fun _ h => ⟨hR.1 _ _ y y' (fun x => hl _ x hO) h.1,
        hR.2.1 _ _ _ y y' (fun x => hl _ x hO) h.2⟩⟩

section
variable {P S₁ : Type} (Mg' : MeaningS S₂ (P × S₁) Wt)

/-- **The three pins read the strings below lo.** -/
theorem pinsReadBelow_of {lo : Nat} (hR : ReadsTree Mg' Pm)
    (h₁ : ∀ j t p (y y' : Strs) w, (∀ x, y'.col j x = y.col j x) → Mg'.pin₁ j t p y w →
      Mg'.pin₁ j t p y' w)
    (hw : N.w.1 < lo) (hi : N.index.1 < lo) (hO : (N.tenant .oOmega).1 < lo) :
    PinsReadBelow (S₃ := S₃) N Mg' ML lo := by
  intro i hi' p e s y y' w _ hl h
  rcases hi' with rfl | rfl | rfl
  · exact h₁ _ _ p y' y w (fun x => (hl _ x hi).symm) h
  · exact h₁ _ _ p y' y w (fun x => (hl _ x hw).symm) h
  · exact hR.2.2 _ _ e y' y w (fun x => (hl _ x hO).symm) h

end

end LLT25

#print axioms LLT25.promReadsBelow_of
#print axioms LLT25.pinsReadBelow_of
