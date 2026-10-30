-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Face/TheFinalStatementOneBitHolds.lean: the six lines, the simulator told one bit, at the
honest part.

 1. finalStatement_of_oneBit: at every honest part FinalStatementOneBit gives FinalStatement.
 2. theFinalStatementOneBitHolds_at: FinalStatementOneBit honestProversAndSettings at every error from the sum
    up; theFinalStatementOneBitHolds: at finalZeroKnowledgeError.
 3. theFinalStatementBothHold: that, and FinalStatement honestProversAndSettings at the same error, drawn from
    it: a service that chooses to say the label has that statement.
 4. The proofs here only combine theorems of other files. What they are worth is what completeness
    and zero knowledge at the interactive level are worth, and the limits in the heads of those
    files go with every use. It is about honestProversAndSettings exactly as written, default values included.
-/
import AtFullSide.Face.TheFinalStatementHolds
import AtFullSide.CompletenessAndZeroKnowledge.OneBitAtHonestProversAndSettings
import Johnson.Face.FinalStatementOneBit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open VerifiableInference.AtEveryRequest
open scoped ENNReal

set_option maxHeartbeats 2000000 in
/-- The line on the labelled reply follows from the
line at refused requests, at every honest part. -/
theorem finalHandsOutNoProof_of_refused (honest : HonestProversAndSettings)
    (refused : FinalRefusedHandsOutNoProof honest) : FinalHandsOutNoProof honest := by
  intro files parameters taken weights randomness request hash answer given
  exact reply_of_handsOut (system := finalSystem honest files (settingsOfRead parameters))
    (requestLabel (settingsOfRead parameters)) (requestOutcome (settingsOfRead parameters))
    noProofForm
    (fun weights request notServed =>
      (requestOutcome_served_or_refused (settingsOfRead parameters) weights request).resolve_left
        fun served => notServed
          ((requestLabel_eq_served_iff (settingsOfRead parameters) weights request).2 served))
    (refused files parameters taken) weights randomness request hash answer given

/-- The one-bit statement gives the final statement, at every honest part. -/
theorem finalStatement_of_oneBit (honest : HonestProversAndSettings) (zeroKnowledgeError : ℝ≥0∞)
    (statement : FinalStatementOneBit honest zeroKnowledgeError) :
    FinalStatement honest zeroKnowledgeError :=
  { sound := statement.sound
    complete := statement.complete
    zeroKnowledge := finalZeroKnowledge_of_oneBit honest zeroKnowledgeError statement.zeroKnowledge
    binding := statement.binding
    handsOutNoProof := finalHandsOutNoProof_of_refused honest statement.handsOutNoProof
    repliesFit := statement.repliesFit }

/-- At a refused request the honest part's prover returns the empty form. -/
theorem finalRefusedHandsOutNoProof_value : FinalRefusedHandsOutNoProof honestProversAndSettings :=
  handsOutNoProof_value

/-- **The six lines, the simulator told one bit, at the
honest part**, at every error from the sum up. -/
theorem theFinalStatementOneBitHolds_at {zeroKnowledgeError : ℝ≥0∞}
    (room : stepErrorAtTheStops ≤ zeroKnowledgeError) :
    FinalStatementOneBit honestProversAndSettings zeroKnowledgeError :=
  have lines := theFinalStatementHolds_at room
  { sound := lines.sound
    complete := lines.complete
    zeroKnowledge := finalZeroKnowledgeOneBit_at zeroKnowledgeError room
    binding := lines.binding
    handsOutNoProof := finalRefusedHandsOutNoProof_value
    repliesFit := lines.repliesFit }

/-- **The six lines, the simulator told one bit, at the honest part**, at 2^-154. -/
theorem theFinalStatementOneBitHolds : FinalStatementOneBit honestProversAndSettings finalZeroKnowledgeError :=
  theFinalStatementOneBitHolds_at stepError_below_bar

/-- **Both**: the one-bit statement, and, drawn from it, the statement with the label shown. -/
theorem theFinalStatementBothHold :
    FinalStatementOneBit honestProversAndSettings finalZeroKnowledgeError ∧
      FinalStatement honestProversAndSettings finalZeroKnowledgeError :=
  ⟨theFinalStatementOneBitHolds,
    finalStatement_of_oneBit honestProversAndSettings finalZeroKnowledgeError theFinalStatementOneBitHolds⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.finalHandsOutNoProof_of_refused
#print axioms VerifiableInference.Compilation.finalStatement_of_oneBit
#print axioms VerifiableInference.Compilation.finalRefusedHandsOutNoProof_value
#print axioms VerifiableInference.Compilation.theFinalStatementOneBitHolds_at
#print axioms VerifiableInference.Compilation.theFinalStatementOneBitHolds
#print axioms VerifiableInference.Compilation.theFinalStatementBothHold
