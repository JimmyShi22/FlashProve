-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/AllAtDigits.lean: THE STORED GOALS ON SOUNDNESS UNDER THE FILES' POLICY AND
ON BINDING, AND THE ROW'S FORM WITH A LEVEL IN BOTH HALVES, AT ONE CLOSED TERM: `theWideDigits`
(Johnson/Goal/Conditions/WideDigits.lean). Statements and proofs: each first at `theWide K W`, K and
W letters, then applied.

Why. Which term stands behind `VerifierAndGoals.theDescription` is others' to say. Whoever weighs
`theWideDigits` for it wants to see that what is shown at `theBound K` is had there too, and that
Lean's kernel passes it (the head of WideDigits.lean tells of a trap).

Main names (namespace `FlashProve`). THE THREE DEBTS, in every statement that names them:
`keySound`, `entrySound`, `proofSound` of the named side, each asked where `protocolDataWellFormed` says yes:
HYPOTHESES HERE; where they are proved, and how far: the head of Johnson/Goal/TopOfThree.lean, limit
(1).
  `G8_theWide`, `G8bits_theWide`: at every K and W, from the three debts: by `G8_wide_iff`,
    `G8bits_wide_iff` (Johnson/Goal/Conditions/ReBoundGoals.lean) from `G8_at`
    (Johnson/Goal/Description/AtBound.lean) and `G8bits_theBound`
    (Johnson/Goal/Conditions/SoundBitsAtThe.lean).
  `verify_digits`: the verifier of `theWideDigits` is `descriptionOfDataOnBytes flashProveData`'s. (Its statement hands a
    parser of the one to the other. A first text ended in "maximum recursion depth" there; it
    passes, the kernel too, with `digitCoins` and `digitWide` compared by their names.)
  **`allFourGoals_atCoinsListedByDigits`**: G8 ∧ G8bits ∧ G9 ∧ G9bits at `theWideDigits`, from the three debts (the last two
    need none).
  `nearestSoundAndBinding_digits_bits`, `nearestSoundOpened_digits_bits`: the row's form there with
    the error `soundnessErrorInQueries` in the half on soundness.

Limits. Those of WideDigits.lean, WideBitsAtThe.lean, AtBound.lean and SoundBitsAtThe.lean, all.
Nothing new is proved here: instances. Nothing on completeness or hiding: the goal G3'pol and its
kin are not stated at this term, whose sampler gives 0 and whose provers hand over empty things.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.WideDigits
import Johnson.Goal.Conditions.WideBitsAtThe
import Johnson.Goal.Conditions.ReBoundGoals

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

/- Lean compares these names and does not unfold them. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF descriptionOfDataOnBytes
  FlashProve.thePlan FlashProve.theItem

variable (K : TheCoins) (W : WideCoins K)

/-- The stored G8 at every K and W, from the three debts. -/
theorem G8_theWide
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []))) :
    G8 (theWide K W) :=
  (G8_wide_iff (fun _ => theTerms K) W.bound
    fun _ Z => coinsAnchor Z (K.shape Z) (W.gen Z)).2 (G8_at K kS eS pS)

/-- The stored G8bits at every K and W, from the three debts. -/
theorem G8bits_theWide
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []))) :
    G8bits (theWide K W) :=
  (G8bits_wide_iff (fun _ => theTerms K) W.bound
    fun _ Z => coinsAnchor Z (K.shape Z) (W.gen Z)).2 (G8bits_theBound K he2_the kS eS pS)

/- Lean compares the closed value of the letters by its two names. -/
attribute [local irreducible] digitCoins digitWide

/-- The verifier of `theWideDigits` is `descriptionOfDataOnBytes flashProveData`'s. -/
theorem verify_digits (o : SecondHashFunctionType) (Z : PublicFiles) {Form : Type} (parse : Parser flashProveDescription Z Form) :
    verify (theWideDigits o) Z parse = verify flashProveDescription Z parse :=
  verify_theWide digitCoins digitWide o Z parse

/-- **ALL FOUR AT THE ONE CLOSED TERM.** -/
theorem allFourGoals_atCoinsListedByDigits
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []))) :
    G8 theWideDigits ∧ G8bits theWideDigits ∧ G9 theWideDigits ∧ G9bits theWideDigits :=
  ⟨G8_theWide digitCoins digitWide kS eS pS, G8bits_theWide digitCoins digitWide kS eS pS,
    G9_digits, G9bits_digits⟩

/-- The row's form with a level in both halves. -/
theorem nearestSoundAndBinding_digits_bits
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []))) :
    NearestSoundAndBinding theWideDigits
      (joinError soundnessErrorInQueries fun t => epsBind honestBudget (t + 2)) :=
  nearestSoundAndBinding_theWide_bits digitCoins digitWide kS eS pS

/-- Likewise `SoundOpened`, at twice that error. -/
theorem nearestSoundOpened_digits_bits
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []))) :
    NearestSoundOpened theWideDigits fun t =>
      2 * joinError soundnessErrorInQueries (fun t => epsBind honestBudget (t + 2)) t :=
  nearestSoundOpened_theWide_bits digitCoins digitWide kS eS pS

end FlashProve

#print axioms FlashProve.G8_theWide
#print axioms FlashProve.G8bits_theWide
#print axioms FlashProve.verify_digits
#print axioms FlashProve.allFourGoals_atCoinsListedByDigits
#print axioms FlashProve.nearestSoundAndBinding_digits_bits
#print axioms FlashProve.nearestSoundOpened_digits_bits
