-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Face/TheFinalStatementHolds.lean: all six lines of the final statement at the honest part.

 1. theFinalStatementHolds_at: FinalStatement honestProversAndSettings at every error above the sum; and at 2^-154.
 2. Completeness, zero knowledge and the replies' numbers come by finalAtT1_filled's form at room, which
    calls the compiled step at the two ends at the interactive level.
 3. statementAtStoredFiles_holds: the same at the stored files.
 4. These are calls. What they are worth is what the two ends beneath them are worth. 2^-154 is a number
    that fits the sum: nothing here sets it as a target. It is about honestProversAndSettings exactly as written,
    stand-in values included.
    The limits in the heads of those two ends go with every use: a share of the zero-knowledge end can
    hold for nothing, and nothing here says what a proof hides.
-/
import AtFullSide.Face.TheStoredLines
import AtFullSide.E2E.TheCompiledStepFilled
import AtFullSide.Face.ZeroKnowledgeNumber

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open scoped ENNReal

/-- **The six lines at the honest part**, at every error above the sum. -/
theorem theFinalStatementHolds_at {zeroKnowledgeError : ℝ≥0∞}
    (sum : (2⁻¹ : ℝ≥0∞) ^ 157 +
      (0 + 0 + (688127 : ℕ) * ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) ≤ zeroKnowledgeError) :
    FinalStatement honestProversAndSettings zeroKnowledgeError :=
  have lines := finalAtT1_filled_withRoom zeroKnowledgeError sum
  { sound := finalSound honestProversAndSettings
    complete := lines.1.1
    zeroKnowledge := lines.1.2
    binding := finalSoundAndBinding_value
    handsOutNoProof := finalHandsOutNoProof_value
    repliesFit := lines.2 }

/-- At 2^-154. -/
theorem theFinalStatementHolds : FinalStatement honestProversAndSettings finalZeroKnowledgeError :=
  theFinalStatementHolds_at stops_below_bar

/-- **The six lines at the stored files.** -/
theorem statementAtStoredFiles_holds : FinalStatementAtStoredFiles honestProversAndSettings finalZeroKnowledgeError :=
  atStoredFiles_of_finalStatement honestProversAndSettings finalZeroKnowledgeError
    filesInUse_stored.pass theFinalStatementHolds

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.theFinalStatementHolds
#print axioms VerifiableInference.Compilation.statementAtStoredFiles_holds
