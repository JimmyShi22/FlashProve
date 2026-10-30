-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Face/TheThreeAtTheFiles.lean: soundness, completeness and zero knowledge at one bound protocol, at
every set of files in use.

 1. threeAtFiles_in_use is one call of threeAtFiles_of_ends at the two ends at the interactive level.
 2. What it is worth is what those ends are worth, with their limits. It is about the Lean provers as
    written. Nothing here says what a proof hides.
-/
import AtFullSide.CompletenessAndZeroKnowledge.ThreeAtFilesOfEnds
import AtFullSide.E2E.CompleteAtEveryFilesInUse
import AtFullSide.E2E.ZeroKnowledgeFromTheRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm AtPublicFiles.OneProtocol
open scoped ENNReal

/-- **The three statements at one bound protocol, at files in use.** -/
theorem threeAtFiles_in_use (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (inUse : FilesInUse files parameters) :
    ThreeAtFiles files inUse.read (HonestProvers.ofThreeProvers (honestProvers files (thePartsAt files)))
      0 0 (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) := by
  have refusing := (completeOnServedRequests_refuse_iff files inUse.read _).2
    (completeOnServedRequests_at_every_files_in_use files parameters inUse)
  refine threeAtFiles_of_ends inUse.inScope inUse.pass inUse.read (thePartsAt files) ?_
    (zkOnServedRequests_inScope inUse.inScope inUse.pass inUse.read)
  show CompleteOnServedRequests files inUse.read
    (theProvers files (settingsOfRead parameters) (thePartsAt files))
  rw [theProvers_eq files inUse.read (thePartsAt files)]
  exact refusing

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.threeAtFiles_in_use
