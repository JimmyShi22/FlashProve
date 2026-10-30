-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/FinalBindingAtTheSettings.lean: binding and extraction at compile's own committer, at
the compiled settings theSettings (Johnson/CompletenessAndZeroKnowledge/TheSettings.lean): the premise on salts and the bound on
the committer's queries, both paid.

 1. theHonestPartOf (Johnson/CompletenessAndZeroKnowledge/TheSettings.lean) is an honest part of flashProveAtFiles with ANY provers and
    ANY stand-in instance, at the settings theSettings: one copy; a table's salt is a public start of
    256 bits with 320 free bits; the search limits are an argument.
 2. At public files in use the salts of a table's leaves have the length of the verifier's strict
    format there: tableSalts_atTheSettings, from theSettings_fit (Johnson/CompletenessAndZeroKnowledge/TheSettingsFit.lean).
 3. At the written search limits the honest side stays within 2^48 queries: compile_withinBudget
    (Johnson/CompletenessAndZeroKnowledge/OneHashByFirstBlockTestTies.lean). So N := 2^48 meets the premise of the line on extraction.
 4. bindingAtTheSettings: the six lines of BindingOf, with no premise left on salts.
    extractsAtTheSettings: correctness of extraction at finalOpeningError 2^48, about 2^-155.2.
 5. bindingAtPlainSettings: the premises on the starts of salts can be met (plain starts).
Limits. theHonestPartOf is not honestProversAndSettingsAtFiles (HonestProversWithCompiledPart.lean), the honest part that the top lines
mean: that the second, at these settings, is the first at its provers is no theorem here. These lines
ask FilesInUse: the test on the public files is read by both theorems that are called. All limits of
FinalBindingStatement.lean's head go with them.
-/
import Johnson.Face.FinalBindingProof
import Johnson.CompletenessAndZeroKnowledge.OneHashByFirstBlockTestTies
import Johnson.CompletenessAndZeroKnowledge.TheSettingsFit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve
open IntegerTransformer (Settings)
open scoped ENNReal

variable (files : PublicFiles) (settings : Settings) (fallbackInstance : (flashProveDescription.C files).X)
  (provers : HonestProvers (FlashProtocol files)) (starts : SaltStarts provers)
  (slotSalts : RequestLeafSaltLayout)

/-- **The law on salts at theSettings**, at public files in use, whatever the search limits. -/
theorem tableSalts_atTheSettings (limits : SearchLimits) (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) (h : starts.LengthsFit 256 256)
    (slots : ∀ reading, slotSalts.Fit (flashLayout files settings fallbackInstance reading)) :
    TableSaltsHaveLength
      (theHonestPartOf files settings fallbackInstance provers starts limits slotSalts)
      (R₀ files).compilerParameters.sMT :=
  fun reading => (theSettings_fit files settings fallbackInstance provers limits slotSalts scope live
    starts h reading (slots reading)).coins.len₀

variable {files} (parameters : Inst.Model.ScalesAndPolicy) (fallbackInstance : (flashProveDescription.C files).X)

attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate

/-- **BINDING AT compile's OWN COMMITTER, AT theSettings**: the six lines. -/
theorem bindingAtTheSettings (inUse : FilesInUse files parameters) (limits : SearchLimits)
    (h : starts.LengthsFit 256 256)
    (slots : ∀ reading,
      slotSalts.Fit (flashLayout files (settingsOfRead parameters) fallbackInstance reading)) :
    BindingOf (compile (flashProveAtFiles files (settingsOfRead parameters)
        (theHonestPartOf files (settingsOfRead parameters) fallbackInstance provers starts limits
          slotSalts)))
      (finalExtractor files (settingsOfRead parameters)) :=
  finalBindingGoal files parameters inUse.toFilesTaken _ _
    (tableSalts_atTheSettings files (settingsOfRead parameters) fallbackInstance provers starts
      slotSalts limits inUse.inScope inUse.pass h slots)

/-- **CORRECTNESS OF EXTRACTION AT compile's OWN COMMITTER, AT theSettings AND THE WRITTEN SEARCH
LIMITS**: the error at 2^48 queries, about 2^-155.2. -/
theorem extractsAtTheSettings (inUse : FilesInUse files parameters)
    (h : starts.LengthsFit 256 256)
    (slots : ∀ reading,
      slotSalts.Fit (flashLayout files (settingsOfRead parameters) fallbackInstance reading)) :
    ExtractsCommittedWeights (compile (flashProveAtFiles files (settingsOfRead parameters)
        (theHonestPartOf files (settingsOfRead parameters) fallbackInstance provers starts
          (writtenLimits files) slotSalts)))
      (finalExtractor files (settingsOfRead parameters)) (finalOpeningError honestQueryBudget) :=
  (bindingAtTheSettings provers starts slotSalts parameters fallbackInstance inUse
    (writtenLimits files) h slots).extractsWithinBudget
    (compile_withinBudget files (settingsOfRead parameters) fallbackInstance provers starts slotSalts
      inUse.inScope inUse.pass h slots)

/-- **The premises on the starts of salts can be met**: at plain starts nothing is asked but the
public files in use. -/
theorem bindingAtPlainSettings (inUse : FilesInUse files parameters) :
    BindingOf (compile (flashProveAtFiles files (settingsOfRead parameters)
        (theHonestPartOf files (settingsOfRead parameters) fallbackInstance provers
          (zeroSaltStarts provers) (writtenLimits files) plainSlotSalts)))
      (finalExtractor files (settingsOfRead parameters)) ∧
    ExtractsCommittedWeights (compile (flashProveAtFiles files (settingsOfRead parameters)
        (theHonestPartOf files (settingsOfRead parameters) fallbackInstance provers
          (zeroSaltStarts provers) (writtenLimits files) plainSlotSalts)))
      (finalExtractor files (settingsOfRead parameters)) (finalOpeningError honestQueryBudget) :=
  ⟨bindingAtTheSettings provers (zeroSaltStarts provers) plainSlotSalts parameters fallbackInstance
      inUse (writtenLimits files) (plainStarts_lengthsFit provers 256)
      (fun _ => plainSlotSalts_fit _),
    extractsAtTheSettings provers (zeroSaltStarts provers) plainSlotSalts parameters fallbackInstance
      inUse (plainStarts_lengthsFit provers 256) (fun _ => plainSlotSalts_fit _)⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.compile_withinBudget
#print axioms VerifiableInference.Compilation.theSettings_fit
#print axioms VerifiableInference.Compilation.tableSalts_atTheSettings
#print axioms VerifiableInference.Compilation.bindingAtTheSettings
#print axioms VerifiableInference.Compilation.extractsAtTheSettings
#print axioms VerifiableInference.Compilation.bindingAtPlainSettings
