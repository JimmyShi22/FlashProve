-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/CompletenessAndZeroKnowledge/OneBitAtHonestProversAndSettings.lean: what holds of the compiled system at the honest part
honestProversAndSettings, in the form in which the simulator is told one bit of each request: served or
refused.

  termLeft_at, beneath_at, finalZeroKnowledgeOneBit_at
      the premise, the two statements and the one-bit line, at every error from stepErrorAtTheStops
      up
  termLeft_value
      the premise of beneath_at_T1 at thePartsAt and the number finalZeroKnowledgeError, at every set of
      public files in use
  beneath_value
      the two statements below together
  finalCompleteAtEveryRequest_value
      completeness at every request that is served (servedResult: the claimed output there)
  finalZeroKnowledgeOneBit_value
      zero knowledge at every request, the simulator told requestOutcome alone, within 2^-154, up to
      the definition's two counts of hash queries and replies
  handsOutNoProof_value
      at a refused request every form that the prover can return is the empty form
  finalZeroKnowledgeAtEveryRequest_of_oneBit_value, finalZeroKnowledge_of_oneBit_value
      the line with the label shown follows from the one-bit line, at the same honest part and error

From what. termLeft_at joins completeOnServedRequests_at_every_files_in_use and
termLeftLaterClauses_filled; stops_below_bar gives the room at finalZeroKnowledgeError. The rest is
beneath_at_T1 (AtFullSide/CompletenessAndZeroKnowledge/HonestProversAndSettingsOf.lean) at that premise, and flash_handsOut
(Johnson/Face/TheReply.lean). The last two theorems call finalZeroKnowledgeAtEveryRequest_of_oneBit
and finalZeroKnowledge_of_atEveryRequest (Johnson/Face/Checks.lean).

Limits. These are statements about compile (flashProveAtFiles …) at the honest provers as they are defined
in Lean, not about a program that runs. The one-bit line stands at public files in use; the line on
refused requests at public files that the verifier takes. The bit depends on the weights: a request
is served if it is well formed and the model's result on its window of 1,024 tokens, filled up with
zeros, is the claimed output; so a true output can be refused
(VerifiableInference/RequestOutcome.lean). In the one-bit statements no label stands beside a proof:
a failed run and other tokens are one value, refused, and the reply is the same at both: the empty
form. In the last two theorems the label of three values is shown beside each proof. Soundness and
binding are not reached here. The limits in the heads of Johnson/Face/FinalStatement.lean,
Johnson/Face/Checks.lean, VerifiableInference/AtEveryRequest.lean,
VerifiableInference/RequestOutcome.lean and AtFullSide/E2E/TheCompiledStepFilled.lean hold here too,
among them: one commitment, one copy of the table, exact match, one request to a proof, the
random-oracle model, and a simulator that may depend on the public files and whose work is not
bounded.
-/
import AtFullSide.E2E.TheCompiledStepFilled
import AtFullSide.Face.HonestProversAndSettingsValue
import AtFullSide.Face.ZeroKnowledgeNumber
import Johnson.Face.TheReply

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open VerifierAndGoals AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open VerifiableInference.AtEveryRequest (HandsOutNoProof requestOutcome)

/-- The number of the compiled step is at most finalZeroKnowledgeError. -/
theorem stepError_below_bar : stepErrorAtTheStops ≤ finalZeroKnowledgeError := stops_below_bar

/-- **The premise of beneath_at_T1, at thePartsAt, at every error from stepErrorAtTheStops up, at
every set of public files in use.** -/
theorem termLeft_at (error : ℝ≥0∞) (room : stepErrorAtTheStops ≤ error) (files : PublicFiles)
    (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters) :
    TermLeft thePartsAt files parameters inUse error := by
  obtain ⟨a, b, c, zero, below⟩ := termLeftLaterClauses_filled error room files parameters inUse
  exact ⟨⟨a, b, c, completeOnServedRequests_at_every_files_in_use files parameters inUse, zero,
      below⟩⟩

/-- **Completeness at every served request and zero knowledge told one bit, at the honest part, at
every such error.** -/
theorem beneath_at (error : ℝ≥0∞) (room : stepErrorAtTheStops ≤ error) :
    FinalCompleteAtEveryRequest honestProversAndSettings ∧ FinalZeroKnowledgeOneBit honestProversAndSettings error :=
  beneath_at_T1 thePartsAt error (termLeft_at error room)

/-- **Zero knowledge at every request, the simulator told one bit, at the honest part, at every such
error.** -/
theorem finalZeroKnowledgeOneBit_at (error : ℝ≥0∞) (room : stepErrorAtTheStops ≤ error) :
    FinalZeroKnowledgeOneBit honestProversAndSettings error :=
  (beneath_at error room).2

/-- **The premise of beneath_at_T1, at thePartsAt and finalZeroKnowledgeError, at every set of public files
in use.** -/
theorem termLeft_value (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (inUse : FilesInUse files parameters) :
    TermLeft thePartsAt files parameters inUse finalZeroKnowledgeError :=
  termLeft_at finalZeroKnowledgeError stepError_below_bar files parameters inUse

/-- **Completeness at every served request and zero knowledge told one bit, at the honest part.** -/
theorem beneath_value :
    FinalCompleteAtEveryRequest honestProversAndSettings ∧
      FinalZeroKnowledgeOneBit honestProversAndSettings finalZeroKnowledgeError :=
  beneath_at finalZeroKnowledgeError stepError_below_bar

/-- **Completeness at every served request, at the honest part.** Where a request is refused it says
nothing. -/
theorem finalCompleteAtEveryRequest_value : FinalCompleteAtEveryRequest honestProversAndSettings :=
    beneath_value.1

/-- **Zero knowledge at every request, the simulator told one bit, at the honest part.** -/
theorem finalZeroKnowledgeOneBit_value : FinalZeroKnowledgeOneBit honestProversAndSettings finalZeroKnowledgeError :=
    beneath_value.2

/-- **At a refused request the prover hands out the empty form alone**, at valid settings, for every
honest part that honestProversAndSettingsAtFiles makes. -/
theorem handsOutNoProof_of_honestPartOf (files : PublicFiles) {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) (parts : Parts files)
    (compiled : CompiledPart files settings parts) :
    HandsOutNoProof
      (compile (flashProveAtFiles files settings (honestProversAndSettingsAtFiles files settings parts compiled)))
      (fun weights request => requestOutcome settings weights request = .refused)
      (· = noProofForm) :=
  flash_handsOut files valid _ rfl (refusesUnserved_refuseUnserved _ _)

/-- **At a refused request the prover hands out the empty form alone**, at the honest part, with no
label beside it. -/
theorem handsOutNoProof_value (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (taken : FilesTaken files parameters) :
    HandsOutNoProof (finalSystem honestProversAndSettings files (settingsOfRead parameters))
      (fun weights request => requestOutcome (settingsOfRead parameters) weights request = .refused)
      (· = noProofForm) :=
  handsOutNoProof_of_honestPartOf files (valid_of_read taken.read) (thePartsAt files)
    (compiledPartAtHonestProvers thePartsAt files (settingsOfRead parameters))

/-- **The line at every request with the label shown follows from the one-bit line**, at the same
honest part and the same error. -/
theorem finalZeroKnowledgeAtEveryRequest_of_oneBit_value :
    FinalZeroKnowledgeAtEveryRequest honestProversAndSettings finalZeroKnowledgeError :=
  finalZeroKnowledgeAtEveryRequest_of_oneBit _ _ finalZeroKnowledgeOneBit_value

/-- **The line at the well-formed requests with the label shown follows from the one-bit line**, at
the same honest part and the same error. -/
theorem finalZeroKnowledge_of_oneBit_value : FinalZeroKnowledge honestProversAndSettings finalZeroKnowledgeError :=
  finalZeroKnowledge_of_atEveryRequest _ _ finalZeroKnowledgeAtEveryRequest_of_oneBit_value

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.stepError_below_bar
#print axioms VerifiableInference.Compilation.termLeft_at
#print axioms VerifiableInference.Compilation.beneath_at
#print axioms VerifiableInference.Compilation.finalZeroKnowledgeOneBit_at
#print axioms VerifiableInference.Compilation.termLeft_value
#print axioms VerifiableInference.Compilation.beneath_value
#print axioms VerifiableInference.Compilation.finalCompleteAtEveryRequest_value
#print axioms VerifiableInference.Compilation.finalZeroKnowledgeOneBit_value
#print axioms VerifiableInference.Compilation.handsOutNoProof_of_honestPartOf
#print axioms VerifiableInference.Compilation.handsOutNoProof_value
#print axioms VerifiableInference.Compilation.finalZeroKnowledgeAtEveryRequest_of_oneBit_value
#print axioms VerifiableInference.Compilation.finalZeroKnowledge_of_oneBit_value
