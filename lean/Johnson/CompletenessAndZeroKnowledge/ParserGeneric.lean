-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/ParserGeneric.lean: UndoUpTo at any provers before refusal, from UndoOnBut and the mass of ZeroRun. Stated for any provers, so that no proof unfolds the term honestProvers.
-/
import Johnson.CompletenessAndZeroKnowledge.ThePlug
import Johnson.CompletenessAndZeroKnowledge.ZeroRunAtTerm
import Johnson.Face.ByteSettings
import Johnson.CompletenessAndZeroKnowledge.TheProversEq

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 20000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve FlashProve OnBytes.FrontRoad OnBytes.WholeKey OnBytes.Prover
open VerifiableInference.OnPublicFiles AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest.Term (OnlineReturn)
open VerifiableInference.Desc (Chain)
open P5J
open Johnson.Face
open IntegerTransformer (Settings)

section Left
variable (files : PublicFiles) {pp : Inst.Model.ScalesAndPolicy}

theorem starts_eq (provers : HonestProvers (FlashProtocol files)) (Served : (flashProveDescription.C files).I → (flashProveDescription.C files).X → Prop)
    (runsT : provers.offlineProver.Coin → FormatRuns) (runsB : provers.onlineProver.Coin → FormatRuns) :
    (formatStarts provers (flashRounds files) runsT runsB (linkRun, linkRun)
      (pvKey (dataAtFiles flashProveData files).DK (dataAtFiles flashProveData files).G.rec₀) (pvZ files (dataAtFiles flashProveData files).P)).underRefusal Served =
      flashStartsOfBytes files (provers.refuseUnserved Served) runsT runsB := rfl

theorem sideAt_eq (settings : Settings) (honest : HonestProversAndSettingsAtFiles files settings) :
    sideAt files settings honest = honestPartSide files settings honest := rfl

/-- The strategies at an arm print: StratsPrint at each value of the reading. -/
def ArmPrints (settings : Settings) (files : PublicFiles) (Tr : (flashProveDescription.input files allZeroDigest []).Index → (flashProveDescription.input files allZeroDigest []).Instance → Prop)
    (provers : HonestProvers (FlashProtocol files))
    (runsT : provers.offlineProver.Coin → ByteArray × ByteArray)
    (runsB : provers.onlineProver.Coin → ByteArray × ByteArray) : Prop :=
  ∀ d, StratsPrint (flashS files) allZeroDigest []
    (sideAt files settings (flashHonestPart files settings neverBuiltRequest provers runsT runsB (writtenLimits files)) d)
    runsT runsB (fun i => ∃ x, Tr i x) Tr

/-- The same, at provers before refusal: their coins are the run values' domain. -/
def ArmPrintsRefuse (settings : Settings) (files : PublicFiles)
    (Tr : (flashProveDescription.input files allZeroDigest []).Index → (flashProveDescription.input files allZeroDigest []).Instance → Prop)
    (provers : HonestProvers (FlashProtocol files)) (Served : (flashProveDescription.C files).I → (flashProveDescription.C files).X → Prop)
    (runsT : provers.offlineProver.Coin → ByteArray × ByteArray)
    (runsB : provers.onlineProver.Coin → ByteArray × ByteArray) : Prop :=
  ArmPrints settings files Tr (provers.refuseUnserved Served) runsT runsB

/-- **The parser, at any provers before refusal.** Stated for any provers, so that no proof unfolds the term honestProvers. -/
theorem parser_generic (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (provers : HonestProvers (FlashProtocol files)) (Served : (flashProveDescription.C files).I → (flashProveDescription.C files).X → Prop)
    (Tr : (flashProveDescription.input files allZeroDigest []).Index → (flashProveDescription.input files allZeroDigest []).Instance → Prop)
    (runsT : provers.offlineProver.Coin → FormatRuns) (runsB : provers.onlineProver.Coin → FormatRuns)
    (sizeT : ∀ κ, (runsT κ).1.size = 32 ∧ (runsT κ).2.size = 32)
    (sizeB : ∀ κ, (runsB κ).1.size = 32 ∧ (runsB κ).2.size = 32)
    (hS : SendsItsRunValues provers
      (formatStarts provers (flashRounds files) runsT runsB (linkRun, linkRun)
        (pvKey (dataAtFiles flashProveData files).DK (dataAtFiles flashProveData files).G.rec₀) (pvZ files (dataAtFiles flashProveData files).P)) fun _ => True)
    {εOffline εOnline : ℝ≥0∞}
    (massOffline : Prob.pr (Prob.unif provers.offlineProver.Coin) {κ | RefusedRuns (runsT κ)} ≤ εOffline)
    (massOnline : Prob.pr (Prob.unif provers.onlineProver.Coin) {κ | RefusedRuns (runsB κ)} ≤ εOnline)
    (hPrint : ArmPrintsRefuse (settingsOfRead pp) files Tr provers Served runsT runsB) :
    UndoUpTo flashProveDescription files allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] files)
      (honestPartSide files (settingsOfRead pp)
        (theHonestPartOf files (settingsOfRead pp) neverBuiltRequest (provers.refuseUnserved Served)
          ((formatStarts provers (flashRounds files) runsT runsB (linkRun, linkRun)
            (pvKey (dataAtFiles flashProveData files).DK (dataAtFiles flashProveData files).G.rec₀)
            (pvZ files (dataAtFiles flashProveData files).P)).underRefusal Served) (writtenLimits files) (flashProveRequestLeafSaltLayout files 40)))
      (backThe files (settingsOfRead pp)) Tr (flashProveDescription.parse files) (bytesWriter files)
      ((((2 : ℝ≥0∞) ^ 256)⁻¹ + εOffline) + (((2 : ℝ≥0∞) ^ 256)⁻¹ + εOnline)) := by
  obtain ⟨limT, limL, limB⟩ := byteLimits_lt files scope live
  have hT : ∀ j, (writtenLimits files).offline j < 2 ^ 64 := limT
  have hL : ∀ j, (writtenLimits files).link j < 2 ^ 64 := limL
  have hB : ∀ j, (writtenLimits files).online j < 2 ^ 64 := limB
  have hU := undoOn_at_theSettings files (settingsOfRead pp) neverBuiltRequest (provers.refuseUnserved Served) runsT runsB
    (writtenLimits files) scope live sizeT sizeB hT hL hB Tr (fun i => ∃ x, Tr i x) (fun i x h => ⟨x, h⟩) hPrint
  have hM := fun i x => zeroRun_mass files (settingsOfRead pp) neverBuiltRequest (provers.refuseUnserved Served)
    (flashRounds files) runsT runsB (linkRun, linkRun) (writtenLimits files) (flashProveRequestLeafSaltLayout files 40)
    (SendsItsRunValues.refuse hS Served) massOffline massOnline i x
  rw [starts_eq]
  exact undoUpTo_of_face files (settingsOfRead pp) neverBuiltRequest (provers.refuseUnserved Served)
    (flashStartsOfBytes files (provers.refuseUnserved Served) runsT runsB) (writtenLimits files) (flashProveRequestLeafSaltLayout files 40)
    (flashProveDescription.parse files) (bytesWriter files) (backThe files (settingsOfRead pp)) Tr _ hU fun i x _ => hM i x


end Left

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.parser_generic
