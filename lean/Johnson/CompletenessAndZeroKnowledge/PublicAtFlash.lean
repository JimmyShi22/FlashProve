-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/PublicAtFlash.lean: WHAT IS PUBLIC, AT flashProveAtFiles.

1.  At public files in scope, at every value of the public reading: the laws of the readings, and the
    public conditions for index privacy and completeness, at the numbers of the release.
2.  Of the wiring alone: no prover, no coin, no simulator is read.
3.  The family's input at a reading is the description's input there: so what holds of the description
    at every pair of readings holds of the layout at every reading.
4.  This file claims nothing of a protocol: this file proves neither completeness nor zero
    knowledge of the protocol.


-/
import Johnson.CompletenessAndZeroKnowledge.TheSettings
import VerifiableInference.Final.CompilerTheoremsAtVerify
import VerifiableInference.Final.CompilerPublicAtFiles
import VerifiableInference.Final.PublicForCompletenessAtHome
import E2E.StringsAtInput
import Johnson.CompletenessAndZeroKnowledge.OneHashByFirstBlockTestBudget
import Johnson.CompletenessAndZeroKnowledge.PassAtBuilt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open Prob _root_.Iop OnBytes.Slice OnBytes.Flat
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.FrontRoad OnBytes.WholeKey OnBytes.Prover
open IntegerTransformer (Settings)

attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem

/-- What holds of the description's input at every pair of readings holds of the family's input at
every value of the reading. -/
theorem flash_at_of_all (files : PublicFiles) (P : InnerCompilerInput → Prop)
    (h : ∀ c m, P (flashProveDescription.input files c m)) (reading : FlashReading files) :
    P ((layoutsOfBuiltDescription flashProveData allZeroDigest [] files).at reading) := by
  obtain ⟨c, m, rfl⟩ := (familyLaws_the files).onto reading
  rw [(familyLaws_the files).eq c m]
  exact h c m

variable (files : PublicFiles) (settings : Settings) (fallbackInstance : (flashProveDescription.C files).X)

/-- **The public conditions for index privacy**, at every reading, within the bounds on copies and
sessions, at any search limits. -/
theorem flash_forIndexPrivacy (scope : InScope files = true) (M sessions : ℕ)
    (hM : M + 1 ≤ 710324) (hs : sessions ≤ 688127) (offlineStops linkStops onlineStops : ℝ≥0∞)
    (capT capL capB : ℕ → ℕ) (reading : FlashReading files) :
    PublicForIndexPrivacy (flashLayout files settings fallbackInstance reading)
      (budgetAtFiles offlineStops linkStops onlineStops) M sessions capT capL capB :=
  (publicForIndexPrivacy_iff _ _ _ _ _ _ _).2
    (flash_at_of_all files
      (fun r => AtPublicFiles.Premises.NoProverSide r.queryLayout r.seedQueries r.answerCode (fun _ => True)
        (numbersOf (budgetAtFiles offlineStops linkStops onlineStops) sessions) M capT capL capB)
      (fun c m => AtPublicFiles.Premises.noProverSide_built files scope M sessions hM hs 0 0 0 offlineStops
        linkStops onlineStops capT capL capB c m) reading)

/-- **The public conditions for completeness**, at every reading, at any search limits. -/
theorem flash_forCompleteness (capT capL capB : ℕ → ℕ) (reading : FlashReading files) :
    PublicForCompleteness (flashLayout files settings fallbackInstance reading) capT capL capB :=
  have h := flash_at_of_all files
    (fun r => (∀ capT capL capB, LawFit r.queryLayout r.seedQueries capT capL capB) ∧ WiresFit r.queryLayout r.answerCode)
    (fun c m => AtPublicFiles.Shown.fits_built files c m) reading
  ⟨h.1 capT capL capB, h.2⟩

/-- **At every honest side the first-block test fits.** -/
theorem flash_firstBlockFits
    (side : (layoutsOfBuiltDescription flashProveData allZeroDigest [] files).D → HonestSide 256 (flashProveDescription.input files allZeroDigest []).protocol
      (flashProveDescription.input files allZeroDigest []).LeafBody (flashProveDescription.input files allZeroDigest []).offlineRoundSplits (flashProveDescription.input files allZeroDigest []).linkRoundSplits) :
    FactorsAt (layoutsOfBuiltDescription flashProveData allZeroDigest [] files) side (flashFirstBlockTest files) :=
  factorsAt_of_pass _ side (fun d => firstIs_built flashProveData allZeroDigest [] files d)
    fun d => passFits_built flashProveData allZeroDigest [] files d

/-- **ALL OF WHAT IS PUBLIC AT flashProveAtFiles**, at public files in scope. -/
theorem flash_publicPremises (honest : HonestProversAndSettingsAtFiles files settings)
    (scope : InScope files = true)
    (copies : ∀ reading, (honest.compiledSettings reading).furtherCopies + 1 ≤ 710324)
    (sessions : honest.onlineRunsPerCopy ≤ 688127) (offlineStops linkStops onlineStops : ℝ≥0∞) :
    PublicPremises (flashProveAtFiles files settings honest)
      (budgetAtFiles offlineStops linkStops onlineStops) honest.onlineRunsPerCopy where
  noCoin := (familyLaws_the files).noCoin
  asks := (familyLaws_the files).asks
  once := (familyLaws_the files).once
  spare := (familyLaws_the files).spare
  reads := (familyLaws_the files).reads
  total := (familyLaws_the files).total
  inScope := scope
  firstBlockFits := flash_firstBlockFits files
  forIndexPrivacy := fun reading => flash_forIndexPrivacy files settings honest.fallbackInstance scope _
    _ (copies reading) sessions offlineStops linkStops onlineStops _ _ _ reading
  forCompleteness := fun reading => flash_forCompleteness files settings honest.fallbackInstance _ _ _
    reading

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.flash_at_of_all
#print axioms VerifiableInference.Compilation.flash_forIndexPrivacy
#print axioms VerifiableInference.Compilation.flash_forCompleteness
#print axioms VerifiableInference.Compilation.flash_publicPremises
