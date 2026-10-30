-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/StepSideGaps.lean: FIVE OF THE SEVEN FIELDS OF THE STRUCTURE
Gaps (Johnson/Top/Fire/Code/KeyASideAtFk.lean)
ARE FILLED: g4 | g5 | g10 | g11 (Johnson/RunOne/Law/StepSideAtFk.lean) and g15
(Johnson/RunOne/Law/StepSide15At.lean), at H₀ | H₁ := the state holds what the kind K3's own block of
lookup 0 | 1 has left. The two others (g16 | g17) stay premises.

Main names:
  gaps_of: planOk · two lookups · the chain's first tree is 0 · g16 · g17 ⊢ Gaps X N P at_ (H₀ X)
    (H₁ X).

Limits. It is the state's side alone: no strings, no witness, no reading. Nothing on soundness.

-/
import Johnson.RunOne.Law.StepSideAtFk
import Johnson.RunOne.Law.StepSide15At
import Johnson.Top.Fire.Code.KeyASideAtFk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.StepSideGaps
open OnBytes OnBytes.Params
open VerifiableInference.Desc
open VerifiableInference.Desc.Key (FirstState Claim Source Where lookupsOf descriptionFromSource)
open Johnson.RunOne.KeyRows1 (ASide)
open Johnson.RunOne.KeyRows23 (Fk oneAt)
open Johnson.RunOne.Law.LinkAtCut (fk_admitted)
open Johnson.RunOne.Law.StepSideAtFk
open LPFD (StepInv Gaps)

variable (X : Source) (N : H2U.PlaceNums) (P : VerifiableInference.Desc.Key.LaterPlaces)
  (at_ : Where)

/-- **FIVE OF THE SEVEN.** -/
theorem gaps_of (hpl : (descriptionFromSource X N P).planOk = true) (hl : (lookupsOf X.Y.k.oneTime).length = 2)
    (hft : N.nums.firstTree = 0)
    (g16 : ∀ b, (Fk X N P).first.blocksInOrder[16]? = some b →
      StepInv b (ASide (oneAt X) at_ 16) (ASide (oneAt X) at_ 17))
    (g17 : ∀ b, (Fk X N P).first.blocksInOrder[17]? = some b →
      StepInv b (ASide (oneAt X) at_ 17) (ASide (oneAt X) at_ 18)) :
    Gaps X N P at_ (H₀ X) (H₁ X) := by
  have hW := fk_admitted X N P hpl
  have hn : (oneAt X).ranges.lookups.length = 2 := by
    have e : (lookupsOf (oneAt X)).length = (oneAt X).ranges.lookups.length := List.length_map _
    rw [← e]
    exact hl
  exact ⟨g4 X N P at_ hW (by omega), g5 X N P at_ hW (by omega), g10 X N P at_ hW (by omega),
    g11 X N P at_ hW (by omega), Johnson.RunOne.Law.StepSide15At.g15 X N P at_ hpl hl hft, g16, g17⟩

end Johnson.RunOne.Law.StepSideGaps

#print axioms Johnson.RunOne.Law.StepSideGaps.gaps_of
