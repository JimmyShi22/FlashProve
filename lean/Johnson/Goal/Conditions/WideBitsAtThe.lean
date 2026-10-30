-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/WideBitsAtThe.lean: THE ROW `top_SoundAndBinding` IN ITS FORM, WITH A
SECURITY LEVEL IN BOTH HALVES, AT THE ONE CLOSED DESCRIPTION WITH THE NUMBER OF THE COMMITTER'S
COINS A LETTER (`theWide K W`, Johnson/Goal/Conditions/WideAtThe.lean). Statements and proofs.
Nothing new is shown: `soundUnderPolicyAt_bits_theBound`
(Johnson/Goal/Conditions/SoundBitsAtThe.lean) is carried over by `soundUnderPolicyAt_reBound`
(Johnson/Goal/Conditions/ReBound.lean) and joined with `bindLaws_wide`.

Why. The row's form in WideAtThe.lean stands at `epsFrame 0 theQueries`, of which the goals ask no
more than a quarter: it has no level.

Main names (namespace `FlashProve`).
  `he2_the`: the named side's error of a round, 2^-128, is at most 2 / 2^128.
  `soundUnderPolicyAt_bits_theWide`: soundness under the files' policy of `theWide K W` at `soundnessErrorInQueries`.
  **`nearestSoundAndBinding_theWide_bits`**: `NearestSoundAndBinding (theWide K W)` at
    `joinError soundnessErrorInQueries fun t => epsBind honestBudget (t + 2)`.
  `nearestSoundOpened_theWide_bits`: `NearestSoundOpened (theWide K W)` at twice that error.

THE DEBTS, ALL: kS, eS, pS, each where `protocolDataWellFormed` says yes. K and W stand under "for all".

Limits. Those of WideAtThe.lean and SoundBitsAtThe.lean, all. What level `soundnessErrorInQueries` spells is said in
Ladder/Bits.lean, not here; `joinError` charges the description's own parser its whole budget,
though it asks once. THE THREE DEBTS ARE ALL OF SOUNDNESS: hypotheses here; where they are proved,
and how far: the head of Johnson/Goal/TopOfThree.lean, limits (1), (3) and (4): this error of a
round is a letter there, no price.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.WideAtThe
import Johnson.Goal.Conditions.SoundBitsAtThe

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice

/-- The named side's error of a round lies in the window. -/
theorem he2_the (Z : PublicFiles) (_ : InScope Z = true) :
    (dataAtFiles flashProveData Z).N.εs ≤ 2 * ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  rw [eps_the, ENNReal.inv_pow]
  exact le_mul_of_one_le_left (zero_le _) (by norm_num)

/- Lean compares these names and does not unfold them. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF
  FlashProve.thePlan FlashProve.theItem

variable (K : TheCoins) (W : WideCoins K)

/-- Soundness under the files' policy at the error soundnessErrorInQueries. -/
theorem soundUnderPolicyAt_bits_theWide
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []))) :
    SoundUnderPolicyAt ((flashProveDescription.reBound W.bound).withTerms (theWideTerms K W)) soundnessErrorInQueries :=
  soundUnderPolicyAt_reBound (theTerms K) W.bound _ soundnessErrorInQueries
    (soundUnderPolicyAt_bits_theBound K OnBytes.secondHashFunction he2_the kS eS pS)

/-- **THE ROW's FORM WITH A LEVEL IN BOTH HALVES, FROM THREE DEBTS.** -/
theorem nearestSoundAndBinding_theWide_bits
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []))) :
    NearestSoundAndBinding (theWide K W)
      (joinError soundnessErrorInQueries fun t => epsBind honestBudget (t + 2)) :=
  nearestSoundAndBinding_withTerms (fun _ => flashProveDescription.reBound W.bound) (fun _ => theWideTerms K W) 8 2
    soundnessErrorInQueries (soundUnderPolicyAt_bits_theWide K W kS eS pS)
    fun Z pp _ h₂ => bindLaws_wide K W Z pp h₂

/-- Likewise `SoundOpened`, at twice that error. -/
theorem nearestSoundOpened_theWide_bits
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []))) :
    NearestSoundOpened (theWide K W) fun t =>
      2 * joinError soundnessErrorInQueries (fun t => epsBind honestBudget (t + 2)) t :=
  nearestSoundOpened_of_at (theWide K W) soundnessErrorInQueries _ (soundUnderPolicyAt_bits_theWide K W kS eS pS)
    (bindsAt_withTerms (theWideTerms K W) 8 2 fun Z pp _ h₂ => bindLaws_wide K W Z pp h₂)

end FlashProve

#print axioms FlashProve.he2_the
#print axioms FlashProve.soundUnderPolicyAt_bits_theWide
#print axioms FlashProve.nearestSoundAndBinding_theWide_bits
#print axioms FlashProve.nearestSoundOpened_theWide_bits
