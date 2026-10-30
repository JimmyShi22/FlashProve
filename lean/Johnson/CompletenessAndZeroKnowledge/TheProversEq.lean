-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/TheProversEq.lean: theProvers are the provers of which the two statements on the interactive protocol speak.

1.  WHAT IS CLAIMED: at settings read from the files, theProvers (Johnson/Face/HonestProversWithCompiledPart.lean), which refuse at ServedAt, are proversAtFiles of the
    term, which refuse at ServedRequest: by servedAt_eq.
-/
import Johnson.Face.HonestProversWithCompiledPart
import Johnson.CompletenessAndZeroKnowledge.ServedAtIff
import VerifiableInference.Final.ZeroKnowledgeAtTheProtocol

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve OnBytes.FrontRoad OnBytes.WholeKey OnBytes.Prover
open VerifiableInference.OnPublicFiles AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm

/-- **theProvers are proversAtFiles.** -/
theorem theProvers_eq (files : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp) (parts : Parts files) :
    theProvers files (settingsOfRead pp) parts =
      proversAtFiles files hr (HonestProvers.ofThreeProvers (honestProvers files parts)) := by
  have key : ∀ R : (flashProveDescription.C files).I → (flashProveDescription.C files).X → Prop, R = Seam.servedAt files hr →
      HonestProvers.refuseUnserved (HonestProvers.ofThreeProvers (honestProvers files parts)) R =
        proversAtFiles files hr (HonestProvers.ofThreeProvers (honestProvers files parts)) := by
    rintro _ rfl
    rfl
  exact key _ (Seam.servedAt_eq files hr)

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.theProvers_eq
