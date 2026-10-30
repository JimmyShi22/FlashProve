-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/AtName.lean: G8 at the name from three hypotheses.
`carries_name`: `carries` at `thePhiO`. `G8_at_name`: G8 at `VerifierAndGoals.theDescription` from the key
file's, the entry file's and the proof file's soundness, each asked where `protocolDataWellFormed` says yes:
`G8_theDescription_numbers` (Johnson/Goal/Conditions/NumbersAtThe.lean) with `hext_the`, `claimThe`,
`meaning_the`, `carries_name`, and the bound and ceiling at `epsFrame 0 theQueries`. So the name and
`theBound K` (AtBound.lean) ask the same three.
Limits. Those of AtBound.lean: the three are hypotheses here (where they are proved, and how far:
the head of Johnson/Goal/TopOfThree.lean, limit (1)); the ceiling is one quarter; what sits in the
three seats is told in their own files; where `protocolDataWellFormed` says no it holds emptily; it does not read
its argument. G9 stands at `theBound K` alone: the name's honest side is hollow.

-/
import Johnson.Goal.Description.AtBound
import Johnson.Goal.Description.Hext

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section
open scoped ENNReal

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.Tie
open TypedOracleCompiler.Compile.Batch.Cms

/-- `carries` at `thePhiO`. -/
theorem carries_name (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) (i : (dataAtFiles flashProveData
                         Z).A.Mat)
    (prompt output : List Token) (h : claimThe Z i prompt output) :
    ∃ w, thePhiO Z (settingsOfRead pp) (valid_of_read hr) i = some w ∧
      Policy.MeetsPolicy (settingsOfRead pp) pp.pol w prompt output := by
  have h' : VerifierAndGoals.Fit.claimPolicyO (ppAtFiles Z.pol Z.KL) (lawful_ppAtFiles Z.pol Z.KL) i prompt
      output := h
  exact VerifierAndGoals.Fit.carriesPolicyO (ppAtFiles_of_read hr) _ (valid_of_read hr) i prompt output h'

/- Lean compares these names and does not open them. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
    theProofGate theLinkGate
  theProvers theNamed theKeyRun theProofRun linkDecisionAtFiles theClaims theExtractor LPFD.Full.GF
  FlashProve.thePlan FlashProve.theItem

/-- **G8 at the name, from three hypotheses.** -/
theorem G8_at_name
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0)))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0)))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0))) :
    G8 theDescription :=
  G8_theDescription_numbers theC0 theM0 thePhiO thePsi (epsFrame 0 theQueries)
    (frameError_le_ceiling 0 theQueries (by norm_num) (by unfold theQueries; norm_num)) kS eS pS claimThe
    (fun Z _ => meaning_the Z) (fun Z pp _ hr => carries_name Z pp hr) hext_the
    (fun Z h t n => errorBound_descriptionDataAtFiles (dataAtFiles flashProveData Z) theC0 theM0 theQueries (fit_theLay Z) 1 128 0 rfl
        (he_the Z h)
      le_self_add t n)

end FlashProve
