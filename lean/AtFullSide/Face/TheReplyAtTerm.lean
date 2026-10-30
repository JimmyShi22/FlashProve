-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Face/TheReplyAtTerm.lean: the line on the reply at the honest part that has a value.
-/
import Johnson.Face.TheReply
import AtFullSide.CompletenessAndZeroKnowledge.HonestProversAndSettingsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace VerifiableInference.Compilation
open AtPublicFiles.AtFiles.HonestTerm

/-- **The line on the reply at honestProversAndSettingsOf.** -/
theorem finalHandsOutNoProof_term (parts : (files : VerifierAndGoals.PublicFiles) → Parts files) :
    FinalHandsOutNoProof (honestProversAndSettingsOf parts) :=
  finalHandsOutNoProof_honestPartOf parts (compiledPartAtHonestProvers parts)

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.finalHandsOutNoProof_term
