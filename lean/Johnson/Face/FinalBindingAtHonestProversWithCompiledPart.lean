-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/FinalBindingAtHonestProversWithCompiledPart.lean: the line on soundness with binding of the final statement
(FinalSoundAndBinding, FinalStatement.lean) at honestProversAndSettingsAtFiles (HonestProversWithCompiledPart.lean: the honest part that is
made of the protocol's honest provers), at every value of the key file's arguments, wherever the
compiled settings are theSettings (Johnson/CompletenessAndZeroKnowledge/TheSettings.lean) at starts of salts and slots that fit.

 1. SettingsAreTheSettings parts compiled: at all public files and settings the compiled part's settings
    are theSettings at the stand-in instance that no request builds and the protocol's provers, at
    some starts of salts of lengths 256 and 256, some search limits and some slots that fit. Three
    letters under ∃; nothing on the provers.
 2. tableSaltsOfOneLength_honestPartOf: then, at public files in use, the salts of a table's leaves have
    the length of the verifier's strict format.
 3. finalSoundAndBinding_honestPartOf, finalSoundOpened_honestPartOf, bindingOf_honestPartOf: so the line,
    soundness for an opened commitment, and the six lines of BindingOf at one named extractor.
 4. settingsAreTheSettings_met: the premise has a member, at every parts (plain starts and slots).
Limits. All limits of FinalBindingStatement.lean's head go with these lines. They read no prover. Nothing
here on correctness of extraction at a number: that is extractsAtTheSettings
(FinalBindingAtTheSettings.lean), at theHonestPartOf. They ask FilesInUse: that any public files pass
the verifier's test is no theorem of the main library.
-/
import Johnson.Face.FinalBindingAtTheSettings
import Johnson.Face.FinalBindingLines
import Johnson.Face.HonestProversWithCompiledPart

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve
open AtPublicFiles.AtFiles.HonestTerm (Parts)
open IntegerTransformer (Settings)
open scoped ENNReal

variable (parts : (files : PublicFiles) → Parts files)
  (compiled : (files : PublicFiles) → (settings : Settings) → CompiledPart files settings (parts files))

/-- **The compiled settings are theSettings**, at starts of salts and slots that fit. -/
def SettingsAreTheSettings : Prop :=
  ∀ (files : PublicFiles) (settings : Settings),
    ∃ (starts : SaltStarts (theProvers files settings (parts files))) (limits : SearchLimits)
      (slotSalts : RequestLeafSaltLayout),
      starts.LengthsFit 256 256 ∧
      (∀ reading, slotSalts.Fit (flashLayout files settings neverBuiltRequest reading)) ∧
      (compiled files settings).compiledSettings =
        theSettings files settings neverBuiltRequest (theProvers files settings (parts files))
          starts limits slotSalts

variable {parts compiled}

/-- **The premise on salts is paid.** -/
theorem tableSaltsOfOneLength_honestPartOf (is : SettingsAreTheSettings parts compiled) :
    TableSaltsOfOneLength
      (fun files settings => honestProversAndSettingsAtFiles files settings (parts files) (compiled files settings)) :=
  fun files parameters inUse => by
    obtain ⟨starts, limits, slotSalts, lengths, slots, e⟩ := is files (settingsOfRead parameters)
    refine ⟨(R₀ files).compilerParameters.sMT, fun reading => ?_⟩
    show ((compiled files (settingsOfRead parameters)).compiledSettings reading).coinNumbers.pre₀.length
      + ((compiled files (settingsOfRead parameters)).compiledSettings reading).coinNumbers.ℓ = _
    rw [e]
    exact tableSalts_atTheSettings files (settingsOfRead parameters) neverBuiltRequest _ starts
      slotSalts limits inUse.inScope inUse.pass lengths slots reading

/-- **SOUNDNESS WITH BINDING AT THE HONEST PART OF THE PROTOCOL's PROVERS.** -/
theorem finalSoundAndBinding_honestPartOf (is : SettingsAreTheSettings parts compiled) :
    FinalSoundAndBinding
      (fun files settings => honestProversAndSettingsAtFiles files settings (parts files) (compiled files settings)) :=
  finalSoundAndBinding _ (tableSaltsOfOneLength_honestPartOf is)

/-- Soundness for an opened commitment, there. -/
theorem finalSoundOpened_honestPartOf (is : SettingsAreTheSettings parts compiled) :
    FinalSoundOpened
      (fun files settings => honestProversAndSettingsAtFiles files settings (parts files) (compiled files settings)) :=
  finalSoundOpened _ (tableSaltsOfOneLength_honestPartOf is)

/-- **The six lines at one named extractor**, there. -/
theorem bindingOf_honestPartOf (is : SettingsAreTheSettings parts compiled) (files : PublicFiles)
    (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters) :
    BindingOf
      (finalSystem
        (fun files settings => honestProversAndSettingsAtFiles files settings (parts files) (compiled files settings))
        files (settingsOfRead parameters))
      (finalExtractor files (settingsOfRead parameters)) :=
  (tableSaltsOfOneLength_honestPartOf is files parameters inUse).elim fun length h =>
    finalBindingAtFinalSystem _ files parameters inUse.toFilesTaken length h

variable (parts)

/-- **The premise has a member**, at every value of the key file's arguments. -/
theorem settingsAreTheSettings_met :
    ∃ compiled : (files : PublicFiles) → (settings : Settings) → CompiledPart files settings (parts files),
      SettingsAreTheSettings parts compiled :=
  ⟨fun files settings =>
      ⟨theSettings files settings neverBuiltRequest (theProvers files settings (parts files))
        (zeroSaltStarts _) (writtenLimits files) plainSlotSalts, 0, 0⟩,
    fun _ _ => ⟨zeroSaltStarts _, _, plainSlotSalts, plainStarts_lengthsFit _ 256,
      fun _ => plainSlotSalts_fit _, rfl⟩⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.SettingsAreTheSettings
#print axioms VerifiableInference.Compilation.tableSaltsOfOneLength_honestPartOf
#print axioms VerifiableInference.Compilation.finalSoundAndBinding_honestPartOf
#print axioms VerifiableInference.Compilation.finalSoundOpened_honestPartOf
#print axioms VerifiableInference.Compilation.bindingOf_honestPartOf
#print axioms VerifiableInference.Compilation.settingsAreTheSettings_met
