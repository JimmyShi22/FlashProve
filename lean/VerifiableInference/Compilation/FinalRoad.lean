-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Compilation/FinalRoad.lean: from the two statements on the interactive provers to the
two honest lines of the final statement.

 1. The final statement speaks of one argument system, compile flashProveAtFiles. Two of its lines are
    completeness and zero knowledge.
 2. This file states what these two follow from. Statements only.
 3. ON THE PROVERS, three things: they are complete as interactive oracle proofs; they are
    honest-verifier zero knowledge as such; and they withhold at a request that is not served.
 4. ON THE PROVERS AND THE FORMAT TOGETHER, two things: strings from which salts start are sent in
    the clear; and, up to a stated error, the byte parser reads back what the byte writer writes of
    this committer's keys and this prover's proofs.
 5. ON THE COMPILER's SETTINGS: lengths, the range of the committer's one number, and two bounds, on
    copies and on requests a copy.
 6. ON THE MODEL: a request that can be served builds an instance that the provers serve, at the
    index of the weights; the weights' index is in range; a refused request is not served.
 7. ON NUMBERS: the two written errors lie below the final statement's.
 8. What is public, on the protocol and its layout alone, is no premise here.
 9. One request a proof. Fresh coins.
10. This file proves neither completeness nor zero knowledge of the protocol.
-/
import Johnson.Face.Checks
import VerifiableInference.Final.RefuseUnserved
import VerifiableInference.Final.CompilerTheorems
import Johnson.FrontRoad.CompleteUpTo
import Johnson.FrontRoad.FromPremisesSpec

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve OnBytes.FrontRoad OnBytes.WholeKey OnBytes.Prover
open VerifiableInference.AtEveryRequest (WithinBudget)
open IntegerTransformer (Settings)

/-- The protocol at public files. -/
abbrev protocolAt (files : PublicFiles) := (flashProveDescription.F files).withProvers (flashProveDescription.P files)

/-- The layout at a value of the public reading, of the honest part at hand. -/
abbrev layoutAtReading (files : PublicFiles) (settings : Settings)
    (honest : HonestProversAndSettingsAtFiles files settings)
    (reading : (layoutsOfBuiltDescription flashProveData allZeroDigest [] files).D) :=
  (flashProveWiring files settings honest.fallbackInstance).layoutAtReading reading

/-- The parameters that the premises share. Served: the instances that the provers serve. inRange: the
indices spoken of. -/
structure RoadLetters (files : PublicFiles) where
  inRange : (flashProveDescription.C files).I → Prop
  Served : (flashProveDescription.C files).I → (flashProveDescription.C files).X → Prop
  simulators : RunSimulators (protocolAt files)
  /-- the three numbers for the stops; the five counts are the release's -/
  offlineStops : ℝ≥0∞
  linkStops : ℝ≥0∞
  onlineStops : ℝ≥0∞
  errors : CompletenessErrors
  /-- the chance that the parser does not undo the writer in an accepted honest run -/
  parserError : ℝ≥0∞
  back : (flashProveDescription.C files).X → List Token × List Token

def RoadLetters.budget {files : PublicFiles} (l : RoadLetters files) : Budget :=
  ⟨44040191, 62, 62, 62, 64, l.offlineStops, l.linkStops, l.onlineStops⟩

structure RoadPremises (files : PublicFiles) (settings : Settings)
    (honest : HonestProversAndSettingsAtFiles files settings) (zeroKnowledgeError : ℝ≥0∞)
    (l : RoadLetters files) : Prop where
  /- THE PROVERS -/
  /-- complete as interactive oracle proofs, coins and challenges together, on the served instances -/
  complete : ∀ reading, CompleteBeforeHashingAt (layoutAtReading files settings honest reading)
    honest.provers l.Served l.errors
  /-- honest-verifier zero knowledge as interactive oracle proofs -/
  zeroKnowledge : ∀ reading, HonestVerifierZeroKnowledge
    (layoutAtReading files settings honest reading).work honest.provers l.simulators l.inRange
    l.Served l.budget
  /-- the online prover withholds at every message of a request that is not served -/
  refusesUnserved : honest.provers.RefusesUnserved l.Served
  /- THE PROVERS WITH THE SETTINGS AND THE FORMAT -/
  runValues : ∀ reading, RunValuesAreSent (layoutAtReading files settings honest reading)
    honest.provers (honest.compiledSettings reading) l.inRange
  parserUpTo : UndoUpTo flashProveDescription files allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] files)
    (fun reading => (honestSide (layoutAtReading files settings honest reading) honest.provers
      (honest.compiledSettings reading)).side) (backThe files settings)
    l.Served (flashProveDescription.parse files) (bytesWriter files) l.parserError
  /- THE SETTINGS -/
  settingsFit : ∀ reading, SettingsFit (layoutAtReading files settings honest reading)
    honest.provers (honest.compiledSettings reading)
  copies : ∀ reading, (honest.compiledSettings reading).furtherCopies + 1 ≤ 710324
  sessions : honest.onlineRunsPerCopy ≤ 688127
  coinRange : ∀ reading, coinsRange (honestSide (layoutAtReading files settings honest reading)
    honest.provers (honest.compiledSettings reading)).side ∣ honest.coinBound + 1
  /- THE MODEL -/
  range : ∀ weights, l.inRange (backThe files settings weights)
  tie : TieOn flashProveDescription files allZeroDigest [] settings (backThe files settings) l.back (CanServe settings) l.Served
  /-- a refused request is not served: at the instance that it builds, or at the fallback instance -/
  refusedIsUnserved : ∀ weights request,
    VerifiableInference.AtEveryRequest.requestOutcome settings weights request = .refused →
    ¬ l.Served (backThe files settings weights)
      (instOf (flashProveDescription.input files allZeroDigest []) honest.fallbackInstance request)
  /- THE NUMBERS -/
  completenessBelow : ∀ reading, completenessError (layoutAtReading files settings honest reading)
    honest.provers (honest.compiledSettings reading) l.errors + l.parserError ≤
      finalCompletenessError
  hidingBelow : ∀ reading asked replies, asked ≤ finalVerifierQueries → replies ≤ finalReplyCount →
    indexPrivacyError (layoutAtReading files settings honest reading) honest.provers
      (honest.compiledSettings reading) l.budget honest.onlineRunsPerCopy (asked + 1) replies ≤
      zeroKnowledgeError

/-- **From the premises to two lines.** If at all public files in use the premises hold, for some values of the parameters,
then completeness at every request and zero knowledge told one bit hold of the honest part; Checks.lean carries these to
the final statement's fields on completeness and zero knowledge. With the theorem on soundness these are three of
FinalStatement's six fields; binding, the reply and the replies' numbers are not reached by this statement. -/
def Spec.final_of_the_two : Prop :=
  ∀ (honest : HonestProversAndSettings) (zeroKnowledgeError : ℝ≥0∞),
    (∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesInUse files parameters →
      ∃ l : RoadLetters files,
        RoadPremises files (settingsOfRead parameters) (honest files (settingsOfRead parameters))
          zeroKnowledgeError l) →
    FinalCompleteAtEveryRequest honest ∧ FinalZeroKnowledgeOneBit honest zeroKnowledgeError

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.RoadLetters
#print axioms VerifiableInference.Compilation.RoadPremises
#print axioms VerifiableInference.Compilation.Spec.final_of_the_two
