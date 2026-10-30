-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/TheReply.lean: the line on the reply, at the protocol's honest provers.

 1. An honest part may run any provers, so the line is no fact of every part.
 2. It holds of a part whose stand-in is neverBuiltRequest and whose provers refuse at ServedAt.
 3. The word is requestLabel's by the definition of the reply.
 4. Outside served the request is not served at the instance that the prover runs on: at the
    instance that it builds, by servedAt_backThe_iff, and at the stand-in if it builds none, which
    ServedAt does not hold of.
 5. So the prover's run stops at every message, and the writer gives the empty form, whatever the
    hash function and the coins: with certainty, not up to an error.
 6. It asks that the files read, for valid settings, and no premise on a run.
 7. That a proof comes out at a served request is another line: completeness.
-/
import Johnson.CompletenessAndZeroKnowledge.RoadRefusal
import Johnson.CompletenessAndZeroKnowledge.FinalRoadProof
import Johnson.Face.HonestProversWithCompiledPart
import VerifiableInference.LabelledCarry
import Ladder.Ties

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve OnBytes.FrontRoad OnBytes.WholeKey OnBytes.Prover VerifiableInference.OnPublicFiles
open VerifiableInference.AtEveryRequest (HandsOutNoProof Label Outcome Request requestLabel
  requestLabel_eq_served_iff requestOutcome requestOutcome_served_or_refused)
open AtPublicFiles.AtFiles.HonestTerm
open IntegerTransformer (Settings)

/-- Outside served, the request is not served at the instance that the prover runs on. -/
theorem notServed_at_instOf (files : PublicFiles) {settings : Settings}
    (valid : settingsAreValid settings = true) (weights : ModelWeights settings)
    (request : Request) (fallback : (flashProveDescription.C files).X) (isStandIn : fallback = neverBuiltRequest)
    (notServed : requestLabel settings weights request ≠ .served) :
    ¬ ServedAt files settings (backThe files settings weights)
      (instOf (flashProveDescription.input files allZeroDigest []) fallback request) := by
  cases built : (flashProveDescription.input files allZeroDigest []).buildInstance request [] with
  | none =>
    have isFallback : instOf (flashProveDescription.input files allZeroDigest []) fallback request = fallback := by
      unfold instOf
      rw [built]
      rfl
    rw [isFallback, isStandIn]
    exact not_servedAt_neverBuilt files settings _
  | some instance_ =>
    have isBuilt : instOf (flashProveDescription.input files allZeroDigest []) fallback request = instance_ := by
      unfold instOf
      rw [built]
      rfl
    rw [isBuilt]
    intro served
    exact notServed ((requestLabel_eq_served_iff settings weights request).2
      ((servedAt_backThe_iff files valid weights request instance_ built).1 served))

/-- At any system: if the prover hands out one form at refused requests, and a label other than
served means refused, then the reply is the word beside that form outside served. -/
theorem reply_of_handsOut {system : ArgumentSystem} (label : system.Weights → Request → Label)
    (outcome : system.Weights → Request → Outcome) (noProof : system.Proof)
    (refused : ∀ weights request, label weights request ≠ .served →
      outcome weights request = .refused)
    (hands : HandsOutNoProof system (fun weights request => outcome weights request = .refused)
      (· = noProof))
    (weights : system.Weights) (randomness : system.CommitmentRandomness) (request : Request)
    (hash : Hash) (answer : Label × system.Proof)
    (given : (reply system label weights randomness request.1 request.2).run hash answer ≠ 0) :
    answer.1 = label weights request ∧ (answer.1 ≠ .served → answer.2 = noProof) := by
  obtain ⟨word, proved⟩ := reply_gives system label weights randomness request.1 request.2 hash
    answer given
  exact ⟨word, fun notServed => hands weights randomness request hash answer.2
    (refused weights request fun served => notServed (word.trans served)) proved⟩

/-- Compile's prover hands out the empty form where a part with the stand-in refuses, at the letter
of that part. -/
theorem flash_handsOut (files : PublicFiles) {settings : Settings}
    (valid : settingsAreValid settings = true) (honest : HonestProversAndSettingsAtFiles files settings)
    (isStandIn : honest.fallbackInstance = neverBuiltRequest)
    (refuses : honest.provers.RefusesUnserved (ServedAt files settings)) :
    HandsOutNoProof (compile (flashProveAtFiles files settings honest))
      (fun weights request => requestOutcome settings weights request = .refused)
      (· = noProofForm) :=
  handsOut_atCompile flashProveDescription files settings (backThe files settings) allZeroDigest []
    (layoutsOfBuiltDescription flashProveData allZeroDigest [] files) Prod.mk (familyLaws_the files).eq honest.fallbackInstance
    honest.provers honest.compiledSettings (flashFirstBlockTest files) honest.coinBound flashProveDescription.Form
    (flashProveDescription.parse files) (bytesWriter files) (requestOutcome settings) noProofForm
    (road_handsOut_atSlot files settings honest (ServedAt files settings) refuses
      fun weights request isRefused =>
        notServed_at_instOf files valid weights request _ isStandIn fun served =>
          Outcome.noConfusion
            (isRefused.symm.trans ((requestLabel_eq_served_iff settings weights request).1 served)))

set_option maxHeartbeats 2000000 in
/-- **The line on the reply, at a part with the stand-in that refuses at ServedAt.** -/
theorem replyAtFiles_of_refuses (honest : HonestProversAndSettings) (files : PublicFiles)
    (parameters : Inst.Model.ScalesAndPolicy) (read : readFiles files = .ok parameters)
    (isStandIn : (honest files (settingsOfRead parameters)).fallbackInstance = neverBuiltRequest)
    (refuses : (honest files (settingsOfRead parameters)).provers.RefusesUnserved
      (ServedAt files (settingsOfRead parameters))) :
    ReplyAtFiles honest files parameters := by
  have hands := flash_handsOut files (valid_of_read read)
    (honest files (settingsOfRead parameters)) isStandIn refuses
  intro weights randomness request hash answer given
  exact reply_of_handsOut (system := finalSystem honest files (settingsOfRead parameters))
    (requestLabel (settingsOfRead parameters)) (requestOutcome (settingsOfRead parameters))
    noProofForm
    (fun weights request notServed =>
      (requestOutcome_served_or_refused (settingsOfRead parameters) weights request).resolve_left
        fun served => notServed
          ((requestLabel_eq_served_iff (settingsOfRead parameters) weights request).2 served))
    hands weights randomness request hash answer given

/-- **The line on the reply holds of the protocol's honest provers**, at every value of the key
file's arguments and of what compilation adds. -/
theorem finalHandsOutNoProof_honestPartOf (parts : (files : PublicFiles) → Parts files)
    (compiled : (files : PublicFiles) → (settings : Settings) → CompiledPart files settings (parts files)) :
    FinalHandsOutNoProof (fun files settings =>
      honestProversAndSettingsAtFiles files settings (parts files) (compiled files settings)) :=
  fun files parameters taken =>
    replyAtFiles_of_refuses _ files parameters taken.read rfl
      (refusesUnserved_refuseUnserved _ _)

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.notServed_at_instOf
#print axioms VerifiableInference.Compilation.reply_of_handsOut
#print axioms VerifiableInference.Compilation.flash_handsOut
#print axioms VerifiableInference.Compilation.replyAtFiles_of_refuses
#print axioms VerifiableInference.Compilation.finalHandsOutNoProof_honestPartOf
