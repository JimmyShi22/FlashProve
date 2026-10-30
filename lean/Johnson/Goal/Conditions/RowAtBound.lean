-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/RowAtBound.lean: THE ROW `top_SoundAndBinding` IN ITS FORM, AT THE ONE
CLOSED DESCRIPTION WITH THE TERMS LAID IN (`theBound K`, Johnson/Goal/Conditions/BindsAtThe.lean),
FROM THREE DEBTS ALONE, AT AN ERROR THAT IS NAMED IN BOTH HALVES. Statements and proofs. Nothing new
is shown: Johnson/Goal/Conditions/RowAtTheDebts.lean is called at what
Johnson/Goal/Description/AtBound.lean pays: `hE_the` (the coding of an index is the written one:
rfl), `he_the` (the named side's error of a round is 2^-128) and the filler `thePsi`
(Johnson/Goal/Description/Letters.lean).

Main names (namespace `FlashProve`).
  **`nearestSoundAndBinding_at`**: `NearestSoundAndBinding (theBound K)` (Ladder/Package.lean) at
    `joinError (epsFrame 0 theQueries) fun t => epsBind honestBudget (t + 2)`.
  `nearestSoundOpened_at`: `NearestSoundOpened (theBound K)` at twice that error.
The goals G8, G9 and G9bits at the same term: `G8_at`, `G9_at`, `G9bits_at`, in AtBound.lean.

THE DEBTS, ALL: kS, eS, pS: `CompilerSoundnessConditionStatements.keySound`, `entrySound`, `proofSound` at the description's own
names, at every Z in scope WHERE `protocolDataWellFormed` SAYS YES. K stands under "for all".
NO "THERE IS" STANDS IN A CONCLUSION HERE BUT THE ONE ON THE EXTRACTOR INSIDE THE TOP STATEMENT
`SoundAndBinding`, WHICH THE DESCRIPTION'S NAMED EXTRACTOR MEETS.

Limits. Those of the files named above, all. THE THREE DEBTS ARE ALL OF SOUNDNESS: hypotheses here;
where they are proved, and how far: the head of Johnson/Goal/TopOfThree.lean, limits (1), (3) and
(4): this error of a round is a letter there, no price; the coding of an index is the written one
(`hE_the`). The provers and the honest side of `flashProveData` are place-holders
(Johnson/Goal/Description/Lay.lean), and its named side is hollow.
Where `protocolDataWellFormed` says no the verifier refuses all and the statement holds emptily; that it says yes
at the release's files no sheet has printed. A verifier that refuses everything meets the first
clause for nothing: the statement weighs only beside completeness of this very description. The
nearest form speaks at the files whose policy is exact match. No level in bits is concluded for
soundness. `theBound K` is not `VerifierAndGoals.theDescription`.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.RowAtTheDebts
import Johnson.Goal.Description.AtBound

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
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF
  FlashProve.thePlan FlashProve.theItem

variable (K : TheCoins)

/-- **THE ROW's FORM AT THE DESCRIPTION, FROM THREE DEBTS, AT A NAMED ERROR.** -/
theorem nearestSoundAndBinding_at
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []))) :
    NearestSoundAndBinding (theBound K)
      (joinError (epsFrame 0 theQueries) fun t => epsBind honestBudget (t + 2)) :=
  nearestSoundAndBinding_theBound_debts K thePsi 1 128 0 rfl le_self_add he_the kS eS pS hE_the

/-- Likewise `SoundOpened`, at twice that error. -/
theorem nearestSoundOpened_at
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []))) :
    NearestSoundOpened (theBound K) fun t =>
      2 * joinError (epsFrame 0 theQueries) (fun t => epsBind honestBudget (t + 2)) t :=
  nearestSoundOpened_theBound_debts K thePsi 1 128 0 rfl le_self_add he_the kS eS pS hE_the

end FlashProve

#print axioms FlashProve.nearestSoundAndBinding_at
#print axioms FlashProve.nearestSoundOpened_at
