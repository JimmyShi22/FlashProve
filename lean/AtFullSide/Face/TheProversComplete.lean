-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Face/TheProversComplete.lean: the statement on completeness at the honest provers is the
«complete» of the three statements.
-/
import Johnson.CompletenessAndZeroKnowledge.TheProversEq
import E2E.CompleteAsIOPAtTheProvers
import Johnson.Face.OneProtocol

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm

/-- **Completeness at the honest part is the «complete» of the three statements.** -/
theorem theHonestPartIsComplete_iff (files : PublicFiles) {parameters : Inst.Model.ScalesAndPolicy}
    (read : readFiles files = .ok parameters) (parts : Parts files) :
    TheHonestPartIsComplete files parts read ↔
      (InScope files = true → protocolDataWellFormed (asDescriptionFiles files) = true →
        CompleteOnServedRequests files read
          (proversAtFiles files read (plainProvers files parts))) := by
  unfold TheHonestPartIsComplete
  rw [theProvers_eq files read parts]
  exact Iff.rfl

end VerifiableInference.Compilation
