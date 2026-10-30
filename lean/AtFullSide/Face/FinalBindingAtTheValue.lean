-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Face/FinalBindingAtTheValue.lean: the line on soundness with binding of the final statement, and
correctness of extraction, of honestProversAndSettings (AtFullSide/Face/HonestProversAndSettingsValue.lean: the honest part as
one closed term). Each is the line of AtFullSide/Face/FinalBindingAtHonestProversAndSettingsOf.lean, which holds at every
value of the key file's arguments, at thePartsAt. No premise beyond public files in use.
Limits. Those of Johnson/Face/FinalBindingStatement.lean's head and of
AtFullSide/Face/FinalBindingAtHonestProversAndSettingsOf.lean's.
These lines read no prover: so they say nothing on whether honestProversAndSettings's stand-ins are reached. At this
part coinBound + 1 is the committer's whole range (see that file's Limits).
-/
import AtFullSide.Face.HonestProversAndSettingsValue
import AtFullSide.Face.FinalBindingAtHonestProversAndSettingsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Compilation
open VerifierAndGoals AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open scoped ENNReal

/-- **SOUNDNESS WITH BINDING, OF THE HONEST PART.** It reads no prover and holds at every honest part
whose tables' salts have one length; honestProversAndSettings's provers hold stand-ins; a theorem of the
side library. -/
theorem finalSoundAndBinding_value : FinalSoundAndBinding honestProversAndSettings :=
  finalSoundAndBinding_termHonest thePartsAt

/-- Soundness for an opened commitment, of the honest part. -/
theorem finalSoundOpened_value : FinalSoundOpened honestProversAndSettings :=
  finalSoundOpened_termHonest thePartsAt

/-- **The six lines at one named extractor**, of the honest part. -/
theorem bindingOf_value (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (inUse : FilesInUse files parameters) :
    BindingOf (finalSystem honestProversAndSettings files (settingsOfRead parameters))
      (finalExtractor files (settingsOfRead parameters)) :=
  bindingOf_termHonest thePartsAt files parameters inUse

/-- **CORRECTNESS OF EXTRACTION, OF THE HONEST PART**: the error at 2^48 queries, about 2^-155.2. -/
theorem finalExtracts_value (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (inUse : FilesInUse files parameters) :
    ExtractsCommittedWeights (finalSystem honestProversAndSettings files (settingsOfRead parameters))
      (finalExtractor files (settingsOfRead parameters)) (finalOpeningError honestQueryBudget) :=
  finalExtracts_termHonest thePartsAt files parameters inUse

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.finalSoundAndBinding_value
#print axioms VerifiableInference.Compilation.finalSoundOpened_value
#print axioms VerifiableInference.Compilation.bindingOf_value
#print axioms VerifiableInference.Compilation.finalExtracts_value
