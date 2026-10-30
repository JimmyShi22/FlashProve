-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/FinalStatementOneBit.lean: the final statement, the simulator told one bit.

 1. FinalStatementOneBit has the six fields of FinalStatement. Four are the same definitions: sound,
    complete, binding and repliesFit.
 2. zeroKnowledge is FinalZeroKnowledgeOneBit: at every request, well-formed or not, the simulator
    is told whether the request is served or refused, and nothing stands beside the proofs.
 3. handsOutNoProof is FinalRefusedHandsOutNoProof: at a refused request every form that the prover
    can return is the empty form. It names no label.
 4. The bit depends on the weights, and it is declared, not hidden.
 5. finalZeroKnowledge_of_oneBit: the line with the label shown follows from the one-bit line.
-/
import Johnson.Face.Checks

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open VerifierAndGoals VerifiableInference.AtEveryRequest
open scoped ENNReal

/-- At given files: at a refused request every form that the prover can return is the empty form. -/
def RefusedHandsOutNoProofAtFiles (honest : HonestProversAndSettings) (files : PublicFiles)
    (parameters : Inst.Model.ScalesAndPolicy) : Prop :=
  HandsOutNoProof (finalSystem honest files (settingsOfRead parameters))
    (fun weights request => requestOutcome (settingsOfRead parameters) weights request = .refused)
    isNoProof

/-- **At a refused request every form that the prover can
return is the empty form.** The line names no label. -/
def FinalRefusedHandsOutNoProof (honest : HonestProversAndSettings) : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesTaken files parameters →
    RefusedHandsOutNoProofAtFiles honest files parameters

/-- **The final statement, the simulator told one bit**, of
one honest part within one error on zero knowledge. -/
structure FinalStatementOneBit (honest : HonestProversAndSettings) (zeroKnowledgeError : ℝ≥0∞) : Prop where
  sound : FinalSound honest
  complete : FinalComplete honest
  zeroKnowledge : FinalZeroKnowledgeOneBit honest zeroKnowledgeError
  binding : FinalSoundAndBinding honest
  handsOutNoProof : FinalRefusedHandsOutNoProof honest
  repliesFit : RepliesFit honest

/-- The line with the label shown follows from the one-bit line, at the same
error, at every honest part: a simulator told the label can compute the bit. -/
theorem finalZeroKnowledge_of_oneBit (honest : HonestProversAndSettings) (zeroKnowledgeError : ℝ≥0∞)
    (oneBit : FinalZeroKnowledgeOneBit honest zeroKnowledgeError) :
    FinalZeroKnowledge honest zeroKnowledgeError :=
  finalZeroKnowledge_of_atEveryRequest honest zeroKnowledgeError
    (finalZeroKnowledgeAtEveryRequest_of_oneBit honest zeroKnowledgeError oneBit)

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.finalZeroKnowledge_of_oneBit
