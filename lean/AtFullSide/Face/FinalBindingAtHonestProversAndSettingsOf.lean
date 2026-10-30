-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Face/FinalBindingAtHonestProversAndSettingsOf.lean: the line on soundness with binding of the final statement
(FinalSoundAndBinding, Johnson/Face/FinalStatement.lean), and correctness of extraction, at honestProversAndSettingsOf parts
(AtFullSide/CompletenessAndZeroKnowledge/HonestProversAndSettingsOf.lean: the honest part that the compiler's settings make of the protocol's
provers), whatever the key file's arguments parts. No premise is left on the honest part. A file of the
side library: honestProversAndSettingsOf stands above it.

 1. termHonest_is: honestProversAndSettingsOf parts files settings is theHonestPartOf (Johnson/CompletenessAndZeroKnowledge/TheSettings.lean) at the
    stand-in instance that no request builds, the protocol's provers made to refuse, their starts of
    salts under that refusal, the written search limits and the format's slots: by unfolding.
 2. settingsAreTheSettings_term: what compilation adds there is theSettings at starts of salts and
    slots that fit (SettingsAreTheSettings, FinalBindingAtHonestProversWithCompiledPart.lean). So
    tableSaltsOfOneLength_termHonest: the premise of finalSoundAndBinding (FinalBindingLines.lean) is paid.
 3. finalSoundAndBinding_termHonest : FinalSoundAndBinding (honestProversAndSettingsOf parts).
 4. bindingOf_termHonest: the six lines of BindingOf (FinalBindingStatement.lean) at one named
    extractor. finalSoundOpened_termHonest: soundness for an opened commitment.
 5. finalExtracts_termHonest: correctness of extraction at finalOpeningError 2^48, about 2^-155.2: the
    bound on the committer's own queries is the honest side's budget (compile_withinBudget,
    Johnson/CompletenessAndZeroKnowledge/OneHashByFirstBlockTestTies.lean).
Limits. All limits of FinalBindingStatement.lean's head go with these lines: among them: an opening
names one number, two digits of which reach the commitment; the 256 bits cover the first table's root
and out-of-domain sample, not the key file's proofs, copies or links; no line says that verify accepts
anything under such a commitment; no figure is 128 bits; no tie to a program. These lines read no
prover: they hold at every parts. They ask FilesInUse: that any public files pass the verifier's
test is no theorem of the main library. At this part coinBound + 1 is the committer's whole range
(theCoinBound, Johnson/CompletenessAndZeroKnowledge/TheSettings.lean): every encoding randomness of the first table and every member
of its list of salts has a number up to coinBound (everyRandomness_termHonest,
AtFullSide/Face/FinalBindingOpeningsAtHonestProversAndSettingsOf.lean). NO CONTROL STANDS AT THIS PART: that binding can
fail is a theorem at every honest part (never_does_not_bind_compile, Johnson/Face/FinalBindingProof.lean);
its instance at this part is neither stated nor proved in this library.
-/
import Johnson.Face.FinalBindingAtHonestProversWithCompiledPart
import AtFullSide.CompletenessAndZeroKnowledge.HonestProversAndSettingsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve
open AtPublicFiles.AtFiles.HonestTerm (Parts)
open Johnson.Face
open IntegerTransformer (Settings)
open scoped ENNReal

variable (parts : (files : PublicFiles) → Parts files)

/-- **The honest part at the protocol's provers is theHonestPartOf at these letters.** -/
theorem termHonest_is (files : PublicFiles) (settings : Settings) :
    honestProversAndSettingsOf parts files settings =
      theHonestPartOf files settings neverBuiltRequest (theProvers files settings (parts files))
        ((saltStartsAtHonestProvers files (parts files)).underRefusal (ServedAt files settings))
        (writtenLimits files) (flashProveRequestLeafSaltLayout files 40) := rfl

/-- The starts of salts have their lengths. -/
theorem termStarts_underRefusal_lengths (files : PublicFiles) (settings : Settings) :
    ((saltStartsAtHonestProvers files (parts files)).underRefusal (ServedAt files settings)).LengthsFit 256 256 :=
  (termStarts_lengths files (parts files)).underRefusal (ServedAt files settings)

/-- **What compilation adds there is theSettings**, at starts of salts and slots that fit. -/
theorem settingsAreTheSettings_term : SettingsAreTheSettings parts (compiledPartAtHonestProvers parts) :=
  fun files settings =>
    ⟨(saltStartsAtHonestProvers files (parts files)).underRefusal (ServedAt files settings), writtenLimits files,
      flashProveRequestLeafSaltLayout files 40, termStarts_underRefusal_lengths parts files settings,
      fun reading => formatSlotSalts_fit (flashLayout files settings neverBuiltRequest reading) 40,
      rfl⟩

/-- **The premise on salts is paid.** -/
theorem tableSaltsOfOneLength_termHonest : TableSaltsOfOneLength (honestProversAndSettingsOf parts) :=
  tableSaltsOfOneLength_honestPartOf (settingsAreTheSettings_term parts)

/-- **SOUNDNESS WITH BINDING AT THE HONEST PART OF THE PROTOCOL's PROVERS.** -/
theorem finalSoundAndBinding_termHonest : FinalSoundAndBinding (honestProversAndSettingsOf parts) :=
  finalSoundAndBinding _ (tableSaltsOfOneLength_termHonest parts)

/-- Soundness for an opened commitment, there. -/
theorem finalSoundOpened_termHonest : FinalSoundOpened (honestProversAndSettingsOf parts) :=
  finalSoundOpened _ (tableSaltsOfOneLength_termHonest parts)

/-- **The six lines at one named extractor**, there. -/
theorem bindingOf_termHonest (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (inUse : FilesInUse files parameters) :
    BindingOf (finalSystem (honestProversAndSettingsOf parts) files (settingsOfRead parameters))
      (finalExtractor files (settingsOfRead parameters)) :=
  (tableSaltsOfOneLength_termHonest parts files parameters inUse).elim fun length h =>
    finalBindingAtFinalSystem _ files parameters inUse.toFilesTaken length h

/-- The honest side stays within its budget, there. -/
theorem withinBudget_termHonest (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (inUse : FilesInUse files parameters) :
    AtEveryRequest.WithinBudget (finalSystem (honestProversAndSettingsOf parts) files (settingsOfRead parameters))
      honestQueryBudget := by
  show AtEveryRequest.WithinBudget (compile (flashProveAtFiles files (settingsOfRead parameters)
    (honestProversAndSettingsOf parts files (settingsOfRead parameters)))) honestQueryBudget
  rw [termHonest_is]
  exact compile_withinBudget files (settingsOfRead parameters) neverBuiltRequest _ _ _ inUse.inScope
    inUse.pass (termStarts_underRefusal_lengths parts files (settingsOfRead parameters))
    (fun reading => formatSlotSalts_fit
      (flashLayout files (settingsOfRead parameters) neverBuiltRequest reading) 40)

/-- **CORRECTNESS OF EXTRACTION**, there: the error at 2^48 queries, about 2^-155.2. -/
theorem finalExtracts_termHonest (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (inUse : FilesInUse files parameters) :
    ExtractsCommittedWeights (finalSystem (honestProversAndSettingsOf parts) files (settingsOfRead parameters))
      (finalExtractor files (settingsOfRead parameters)) (finalOpeningError honestQueryBudget) :=
  (bindingOf_termHonest parts files parameters inUse).extractsWithinBudget
    (withinBudget_termHonest parts files parameters inUse)

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.termHonest_is
#print axioms VerifiableInference.Compilation.settingsAreTheSettings_term
#print axioms VerifiableInference.Compilation.tableSaltsOfOneLength_termHonest
#print axioms VerifiableInference.Compilation.finalSoundAndBinding_termHonest
#print axioms VerifiableInference.Compilation.finalSoundOpened_termHonest
#print axioms VerifiableInference.Compilation.bindingOf_termHonest
#print axioms VerifiableInference.Compilation.withinBudget_termHonest
#print axioms VerifiableInference.Compilation.finalExtracts_termHonest
