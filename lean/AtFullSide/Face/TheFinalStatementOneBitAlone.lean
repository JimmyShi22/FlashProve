-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Face/TheFinalStatementOneBitAlone.lean: the six lines, the simulator told one bit, at the
honest part, each from its own theorem and not through FinalStatement. The library beneath still
defines the label.

 1. theFinalStatementOneBitAlone: FinalStatementOneBit honestProversAndSettings at finalZeroKnowledgeError. Each field
    comes from its own theorem.
 2. The proofs here only combine theorems of other files. It is about honestProversAndSettings exactly as
    written, default values included.
-/
import AtFullSide.CompletenessAndZeroKnowledge.OneBitAtHonestProversAndSettings
import AtFullSide.Face.FinalBindingAtTheValue
import Johnson.Face.FinalSoundProof
import Johnson.Face.FinalStatementOneBit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open scoped ENNReal

/-- **The six lines, the simulator told one bit, at the honest part**, each from its own theorem. -/
theorem theFinalStatementOneBitAlone : FinalStatementOneBit honestProversAndSettings finalZeroKnowledgeError :=
  { sound := finalSound honestProversAndSettings
    complete := finalComplete_of_atEveryRequest honestProversAndSettings finalCompleteAtEveryRequest_value
    zeroKnowledge := finalZeroKnowledgeOneBit_value
    binding := finalSoundAndBinding_value
    handsOutNoProof := handsOutNoProof_value
    repliesFit := repliesFit_value }

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.theFinalStatementOneBitAlone
