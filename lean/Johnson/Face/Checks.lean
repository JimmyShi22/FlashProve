-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/Checks.lean: beside the final statements of
Johnson/Face/FinalStatement.lean: why they are not empty, how completeness stands to
`CompleteOn`, and the form of zero knowledge beneath. Each `def … : Prop` here is a proposition,
as a definition; only what stands as a `theorem` is proved.
-/
import Johnson.Face.FinalStatement
import VerifiableInference.AtEveryRequestGuards
import VerifiableInference.WellFormedRequests
import Ladder.Ties

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open VerifierAndGoals VerifiableInference.AtEveryRequest
open scoped ENNReal

/-- Some public files meet the condition of the lines that ask `FilesInUse`. -/
def SomeFilesQualify : Prop :=
  ∃ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesInUse files parameters

/-- At valid settings some request is served at some weights. The weights are made up: their layers
are all zero. -/
theorem someRequestIsServed {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) : SomeRequestIsServed settings := by
  have both := voting_served valid 1 (by decide)
  exact ⟨_, ([0], [1]), (served_iff_canServe valid _ ([0], [1])).2 both⟩

/-- At every set of public files in use some request is served at some weights. -/
def SomeRequestIsServedInUse : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesInUse files parameters →
    SomeRequestIsServed (settingsOfRead parameters)

/-- At files in use some request is served; that some are in use is `SomeFilesQualify`. -/
theorem someRequestIsServedInUse : SomeRequestIsServedInUse :=
  fun _ _ inUse => someRequestIsServed (valid_of_read inUse.read)

set_option maxRecDepth 100000 in
/-- The output tokens of a served request are the model's, at every honest side. -/
theorem finalServedIsModelOutput (honest : HonestProversAndSettings) (files : PublicFiles)
    (parameters : Inst.Model.ScalesAndPolicy) (taken : FilesTaken files parameters) :
    ServedIsModelOutput (finalSystem honest files (settingsOfRead parameters))
      (requestOutcome (settingsOfRead parameters)) :=
  fun (weights : ModelWeights (settingsOfRead parameters)) request served =>
    ((served_iff_canServe (valid_of_read taken.read) weights request).1 served).2

set_option maxRecDepth 100000 in
/-- **The completeness line is `CompleteOn` on `CanServe`**, the form in which the library's
reductions conclude, at every honest side and error. -/
theorem finalComplete_iff_completeOn (honest : HonestProversAndSettings) (files : PublicFiles)
    (parameters : Inst.Model.ScalesAndPolicy) (taken : FilesTaken files parameters) (error : ℝ≥0∞) :
    ProofAcceptedWhere (finalSystem honest files (settingsOfRead parameters))
        (WellFormedRequest (settingsOfRead parameters)) (modelResult (settingsOfRead parameters))
        error ↔
      CompleteOn (finalSystem honest files (settingsOfRead parameters))
        (CanServe (settingsOfRead parameters)) error :=
  proofAcceptedWhere_iff_completeOn (finalSystem honest files (settingsOfRead parameters))
    (WellFormedRequest (settingsOfRead parameters)) (modelResult (settingsOfRead parameters))
    (CanServe (settingsOfRead parameters))
    (fun (weights : ModelWeights (settingsOfRead parameters)) prompt output =>
      wellFormed_and_result_iff (valid_of_read taken.read) weights prompt output)
    error

/-- **Completeness beneath**: at every request, with no hypothesis: a served request's honest proof
is accepted. -/
def FinalCompleteAtEveryRequest (honest : HonestProversAndSettings) : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesInUse files parameters →
    ProofAcceptedWhere (finalSystem honest files (settingsOfRead parameters)) (fun _ => True)
      (servedResult (settingsOfRead parameters)) finalCompletenessError

set_option maxRecDepth 100000 in
/-- The completeness line follows from the form beneath. -/
theorem finalComplete_of_atEveryRequest (honest : HonestProversAndSettings)
    (beneath : FinalCompleteAtEveryRequest honest) : FinalComplete honest :=
  fun files parameters inUse (weights : ModelWeights (settingsOfRead parameters)) request
      wellFormed isResult =>
    beneath files parameters inUse weights request trivial
      (servedResult_of_wellFormed (settingsOfRead parameters) weights request wellFormed isResult)

/-- **Zero knowledge beneath**: the line at every request, since a real client can send anything. -/
def FinalZeroKnowledgeAtEveryRequest (honest : HonestProversAndSettings)
    (zeroKnowledgeError : ℝ≥0∞) : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesInUse files parameters →
    ZeroKnowledgeShownBelowWhere (finalSystem honest files (settingsOfRead parameters))
      (fun _ => True) (requestLabel (settingsOfRead parameters)) finalVerifierQueries
      finalReplyCount zeroKnowledgeError

set_option maxRecDepth 100000 in
/-- The line at well-formed requests follows from the form beneath, by restriction. -/
theorem finalZeroKnowledge_of_atEveryRequest (honest : HonestProversAndSettings)
    (zeroKnowledgeError : ℝ≥0∞)
    (beneath : FinalZeroKnowledgeAtEveryRequest honest zeroKnowledgeError) :
    FinalZeroKnowledge honest zeroKnowledgeError :=
  fun files parameters inUse =>
    ZeroKnowledgeShownBelowWhere.narrow (fun _ _ => trivial) (beneath files parameters inUse)

/-- **The one-bit statement beneath**: the compiled prover's own proofs show two forms, a proof or
the empty form; here the simulator is told the bit alone, and nothing stands beside the proofs. -/
def FinalZeroKnowledgeOneBit (honest : HonestProversAndSettings) (zeroKnowledgeError : ℝ≥0∞) : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesInUse files parameters →
    ZeroKnowledgeBelowWhere (finalSystem honest files (settingsOfRead parameters)) (fun _ => True)
      (requestOutcome (settingsOfRead parameters)) finalVerifierQueries finalReplyCount
      zeroKnowledgeError

set_option maxRecDepth 100000 in
/-- The one-bit statement gives the form with the label shown. -/
theorem finalZeroKnowledgeAtEveryRequest_of_oneBit (honest : HonestProversAndSettings)
    (zeroKnowledgeError : ℝ≥0∞) (oneBit : FinalZeroKnowledgeOneBit honest zeroKnowledgeError) :
    FinalZeroKnowledgeAtEveryRequest honest zeroKnowledgeError := by
  intro files parameters inUse
  obtain ⟨error, bounded, zeroKnowledge⟩ := oneBit files parameters inUse
  exact ⟨error, bounded,
    zeroKnowledgeShown_of_told (finalSystem honest files (settingsOfRead parameters))
      (requestLabel (settingsOfRead parameters)) (requestOutcome (settingsOfRead parameters))
      bitOf (fun weights request => (bitOf_requestLabel _ weights request).symm)
      (fun _ => True) error zeroKnowledge⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.someRequestIsServedInUse
#print axioms VerifiableInference.Compilation.finalServedIsModelOutput
#print axioms VerifiableInference.Compilation.finalComplete_iff_completeOn
#print axioms VerifiableInference.Compilation.finalZeroKnowledge_of_atEveryRequest
#print axioms VerifiableInference.Compilation.finalComplete_of_atEveryRequest
#print axioms VerifiableInference.Compilation.finalZeroKnowledgeAtEveryRequest_of_oneBit
