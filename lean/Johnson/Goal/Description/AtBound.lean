-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/AtBound.lean: the tie and three goals at one closed term,
`FlashProve.theBound K` (Johnson/Goal/Conditions/BindsAtThe.lean): the built D* at `flashProveData` with the
extractor, the committer's form and the prover's slot laid in.
`hE_the`, `he_the`: two hypotheses proved: the coding by unfolding; the named error 2^-128 lies in
the
window. `G9_at`, `G9bits_at`: binding, at every K, no hypothesis left. `G8_at`: G8 from the key
file's, the entry file's and the proof file's soundness, each asked where `protocolDataWellFormed` says yes.
`all_at`: the three goals in one statement. `theBound_tie`, `theBound_refused`, `theBound_out`,
`theBound_within`: Description.lean's four at this term.
Limits. The three hypotheses are not proved here; where they are proved, and how far: the head of
Johnson/Goal/TopOfThree.lean, limit (1). G8's ceiling is one quarter: no level in bits is concluded.
What sits in
the three seats is told in their own files. Where `protocolDataWellFormed` says no all of this holds emptily. At
`placeHolderCoins` nothing is hidden and no program's commitment is bound. That no hypothesis is
left at G9 is no measure of content: the number of the commitment's coins is 0, so an opener that
picks its own coins stands in no G9. It does not read its argument.

-/
import Johnson.Goal.Conditions.SoundAtThe
import Johnson.Goal.Conditions.RowAtThe
import Johnson.Goal.Conditions.PlaceHolderCoins
import Johnson.Goal.Description.Letters

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
open PV.Head (cThru sevenThru)

/-- The coding is the honest one: by unfolding. -/
theorem hE_the : ∀ Zk, theCoding Zk = codingCells frS frZ 402653181 numsRef (ppAtFiles Zk.pol
    Zk.KL) Subtype.val :=
  fun _ => rfl

/-- The named side's error, by unfolding. -/
theorem eps_the (Z : PublicFiles) : (dataAtFiles flashProveData Z).N.εs = (2 : ℝ≥0∞)⁻¹ ^ 128 := rfl

/- Lean compares these names and does not open them. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
    theProofGate theLinkGate
  theProvers theNamed theKeyRun theProofRun linkDecisionAtFiles theClaims LPFD.Full.GF
  FlashProve.thePlan FlashProve.theItem

variable (K : TheCoins)

/-- **G9 at the one term, at every K.** -/
theorem G9_at : G9 (theBound K) := G9_theBound K hE_the

/-- **G9bits at the one term, at every K.** -/
theorem G9bits_at : G9bits (theBound K) := G9bits_theBound K hE_the

theorem he_the (Z : PublicFiles) (_ : InScope Z = true) : (dataAtFiles flashProveData Z).N.εs ≤ 1 * ((2 : ℝ≥0∞) ^ 128)⁻¹
    := by
  rw [eps_the, one_mul, ENNReal.inv_pow]

/-- **G8 at the one term, at every K, from three hypotheses.** -/
theorem G8_at
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []))) :
    G8 (theBound K) :=
  G8_theBound K thePsi 1 128 0 rfl (by norm_num) le_self_add he_the kS eS pS

/-- **All three goals at the one term.** -/
theorem all_at
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []))) :
    G8 (theBound K) ∧ G9 (theBound K) ∧ G9bits (theBound K) :=
  ⟨G8_at K kS eS pS, G9_at K, G9bits_at K⟩

/-- Its own parser asks once. -/
theorem theBound_within (o : SecondHashFunctionType) (Z : PublicFiles) : Parser.Within ((theBound K o).parse Z) 1 :=
  descriptionOfDataOnBytes_within flashProveData Z

/-- **The run's call at flashProveData's five letters and the format's own hash is its verify.** -/
theorem theBound_tie (o : SecondHashFunctionType) (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true) (live : protocolDataWellFormed
                             (asDescriptionFiles Z) = true)
    (B : FormBytes) (commitment : Commitment) (prompt output : List Token) (f : DecodedProof)
    (hf : decodeD (cThru _root_.Fmt.oracle (asDescriptionFiles Z)) B = some f) (s : FastSteps)
    (hs : PV.RunPure.Full.stepsFullAllAt {} (thePlan (asDescriptionFiles Z))
      (PV.MFull.spI (theItem (asDescriptionFiles Z))) _root_.Fmt.oracle
      (cThru _root_.Fmt.oracle (asDescriptionFiles Z))
      (sevenThru _root_.Fmt.oracle recordGround (asDescriptionFiles Z) (cThru _root_.Fmt.oracle (asDescriptionFiles Z)))
      (theKeyData (asDescriptionFiles Z)) (theProofData (asDescriptionFiles Z)) (theKeyRun (asDescriptionFiles Z)) (theProofRun
                                           (asDescriptionFiles Z))
      (linkDecisionAtFiles (asDescriptionFiles Z)) commitment prompt output f.aux f.cm f.rcd f.copy f.fT f.e f.fB =
          some s) :
    s.yes =
      (VerifierAndGoals.verify (theBound K o) Z ((theBound K o).parse Z) commitment prompt output B).evaluate
        (hashOf _root_.Fmt.oracle) :=
  theBuilt_tie Z scope live B commitment prompt output f hf s hs

/-- Where the decoders refuse it says no. -/
theorem theBound_refused (o : SecondHashFunctionType) (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true) (B : FormBytes)
    (commitment : Commitment) (prompt output : List Token)
    (hdec : decodeD (cThru _root_.Fmt.oracle (asDescriptionFiles Z)) B = none) :
    (VerifierAndGoals.verify (theBound K o) Z ((theBound K o).parse Z) commitment prompt output B).evaluate
        (hashOf _root_.Fmt.oracle) = false :=
  theBuilt_refused Z scope B commitment prompt output hdec

/-- Out of the goals' scope it says no. -/
theorem theBound_out (o : SecondHashFunctionType) (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = false) (hash :
                             VerifiableInference.Hash)
    (B : FormBytes) (commitment : Commitment) (prompt output : List Token) :
    (VerifierAndGoals.verify (theBound K o) Z ((theBound K o).parse Z) commitment prompt output B).evaluate
        hash = false :=
  verify_out_of_scope flashProveData Z scope hash commitment prompt output B

end FlashProve
