-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/LabelledZeroKnowledge.lean: zero knowledge of a system gives it of the labelled
system, told the label.

 1. If what the simulator is told at the system is a function of the label, telling it the label
    tells it no less.
 2. Its simulator: the same state and the same answers; it makes the proof as before, at what the
    label tells it, and pairs the label back on.
 3. A labelled verifier and chooser are plain ones with the label built in: both are picked after the
    weights. The labelled view is a fixed function of the plain view, in both experiments.
-/
import VerifiableInference.Labelled
import VerifiableInference.AtEveryRequest
import VerifiableInference.LabelledZeroKnowledgeTools

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference
open AtEveryRequest

/-! ## 1 The simulator -/

/-- **The simulator of the labelled system**: the same state, start and answers to queries; told a label,
it makes the proof as the given simulator does at what the label tells, and pairs the label on. -/
def labelledSimulator {PublicParameters Label Told Proof : Type}
    (simulator : AtEveryRequest.Simulator PublicParameters Told Proof) (tell : Label → Told) :
    AtEveryRequest.Simulator PublicParameters Label (Label × Proof) where
  State := simulator.State
  start := simulator.start
  answerQuery := simulator.answerQuery
  simulateProof := fun state request word =>
    (simulator.simulateProof state request (tell word)).map fun simulated =>
      ((word, simulated.1), simulated.2)

/-- The simulated steps of VerifiableInference/AtEveryRequest.lean are "simulatedStepsWith" at the
simulator's answers and at its proofs, told what "told" says. -/
theorem toldSteps_eq_simulatedStepsWith {PublicParameters Told Proof : Type}
    (simulator : AtEveryRequest.Simulator PublicParameters Told Proof) (told : Request → Told)
    (chooser : View Proof → Option Request) :
    ∀ (verifier : MaliciousVerifier Proof) (remaining : ℕ) (view : View Proof)
      (state : simulator.State),
      AtEveryRequest.simulatedSteps simulator told chooser verifier remaining view state
        = simulatedStepsWith simulator.answerQuery
            (fun state request => simulator.simulateProof state request (told request)) chooser
            verifier remaining view state
  | .stop, _, _, _ => by
      simp only [AtEveryRequest.simulatedSteps, simulatedStepsWith]
  | .query input next, remaining, view, state => by
      have ih := fun (answered : Digest × simulator.State) =>
        toldSteps_eq_simulatedStepsWith simulator told chooser (next answered.1) remaining
          { view with queryLog := view.queryLog ++ [(input, answered.1)] } answered.2
      simp only [AtEveryRequest.simulatedSteps, simulatedStepsWith]
      exact congrArg _ (funext fun answered => ih answered)
  | .sample bound next, remaining, view, state => by
      have ih := fun draw =>
        toldSteps_eq_simulatedStepsWith simulator told chooser (next draw) remaining
          { view with randomDraws := view.randomDraws ++ [draw.val] } state
      simp only [AtEveryRequest.simulatedSteps, simulatedStepsWith]
      exact congrArg _ (funext fun draw => ih draw)
  | .requestProof _, 0, _, _ => by
      simp only [AtEveryRequest.simulatedSteps, simulatedStepsWith]
  | .requestProof next, remaining + 1, view, state => by
      have ih := fun request (simulated : Proof × simulator.State) =>
        toldSteps_eq_simulatedStepsWith simulator told chooser (next request simulated.1)
          remaining { view with proofs := view.proofs ++ [(request, simulated.1)] } simulated.2
      cases hChoice : chooser view with
      | none => simp only [AtEveryRequest.simulatedSteps, simulatedStepsWith, hChoice]
      | some request =>
          simp only [AtEveryRequest.simulatedSteps, simulatedStepsWith, hChoice]
          exact congrArg _ (funext fun simulated => ih request simulated)

/-! ## 2 The two experiments -/

section
variable {Label Told : Type} (system : ArgumentSystem)
  (label : system.Weights → List Token × List Token → Label)

/-- The label of a request at the weights, laid beside a proof. -/
def pairLabel (weights : system.Weights) : Request → system.Proof → Label × system.Proof :=
  fun request proof => (label weights request, proof)

/-- **The labelled view**: the plain view with each request's label beside its proof. -/
abbrev labelView (weights : system.Weights) : View system.Proof → View (Label × system.Proof) :=
  View.mapProofs (pairLabel system label weights)

/-- **The real experiment of the labelled system is the image, under the labelled view, of the real
experiment of the system**, at the verifier and the chooser that lay the labels themselves. An equation
of trees. -/
theorem realExperiment_labelled (verifier : Commitment → MaliciousVerifier (Label × system.Proof))
    (chooser : View (Label × system.Proof) → Option Request) (weights : system.Weights)
    (proofCount : ℕ) :
    (realExperiment (labelled system label) verifier chooser weights proofCount :
        RandomizedAlgorithm (View (Label × system.Proof)))
      = (realExperiment system
          (fun commitment => (verifier commitment).comapProofs (pairLabel system label weights))
          (fun plain => chooser (labelView system label weights plain)) weights
          proofCount).mapResult (labelView system label weights) := by
  show (system.sampleCommitmentRandomness.bind fun randomness =>
      (system.commit weights randomness).toRandomized.bind fun commitment =>
        realSteps (labelled system label) chooser weights randomness (verifier commitment) proofCount
          ⟨commitment, [], [], []⟩)
    = (system.sampleCommitmentRandomness.bind fun randomness =>
      (system.commit weights randomness).toRandomized.bind fun commitment =>
        realSteps system (fun plain => chooser (labelView system label weights plain)) weights
          randomness ((verifier commitment).comapProofs (pairLabel system label weights)) proofCount
          ⟨commitment, [], [], []⟩).mapResult (labelView system label weights)
  rw [RandomizedAlgorithm.mapResult_bind]
  refine congrArg _ (funext fun randomness => ?_)
  rw [RandomizedAlgorithm.mapResult_bind]
  refine congrArg _ (funext fun commitment => ?_)
  rw [realSteps_eq_stepsWith (labelled system label), realSteps_eq_stepsWith system]
  exact stepsWith_mapProofs (pairLabel system label weights)
    (fun request => system.prove weights randomness request.1 request.2) chooser
    (verifier commitment) proofCount ⟨commitment, [], [], []⟩

/-- **The simulated experiment of the labelled system, told the label, is the image, under the labelled
view, of the simulated experiment of the system**, told what the label tells. -/
theorem simulatedExperiment_labelled (told : system.Weights → Request → Told) (tell : Label → Told)
    (same : ∀ weights request, told weights request = tell (label weights request))
    (simulator : AtEveryRequest.Simulator system.PublicParameters Told system.Proof)
    (verifier : Commitment → MaliciousVerifier (Label × system.Proof))
    (chooser : View (Label × system.Proof) → Option Request) (weights : system.Weights)
    (proofCount : ℕ) :
    (AtEveryRequest.simulatedExperiment (labelled system label) (labelledSimulator simulator tell)
        label verifier chooser weights proofCount : PMF (View (Label × system.Proof)))
      = (AtEveryRequest.simulatedExperiment system simulator told
          (fun commitment => (verifier commitment).comapProofs (pairLabel system label weights))
          (fun plain => chooser (labelView system label weights plain)) weights proofCount).map
          (labelView system label weights) := by
  show ((simulator.start (system.publicParameters weights) proofCount).bind fun started =>
      AtEveryRequest.simulatedSteps (labelledSimulator simulator tell) (label weights) chooser
        (verifier started.1) proofCount ⟨started.1, [], [], []⟩ started.2)
    = ((simulator.start (system.publicParameters weights) proofCount).bind fun started =>
      AtEveryRequest.simulatedSteps simulator (told weights)
        (fun plain => chooser (labelView system label weights plain))
        ((verifier started.1).comapProofs (pairLabel system label weights)) proofCount
        ⟨started.1, [], [], []⟩ started.2).map (labelView system label weights)
  rw [PMF.map_bind]
  refine congrArg _ (funext fun started => ?_)
  rw [toldSteps_eq_simulatedStepsWith (labelledSimulator simulator tell),
    toldSteps_eq_simulatedStepsWith simulator]
  have tellsSame : (fun (state : simulator.State) (request : Request) =>
      simulator.simulateProof state request (told weights request))
      = fun state request => simulator.simulateProof state request (tell (label weights request)) :=
    funext fun state => funext fun request => by rw [same]
  rw [tellsSame]
  exact simulatedStepsWith_mapProofs (pairLabel system label weights) simulator.answerQuery
    (fun state request => simulator.simulateProof state request (tell (label weights request)))
    chooser (verifier started.1) proofCount ⟨started.1, [], [], []⟩ started.2

end

/-! ## 3 The theorem -/

/-- **Zero knowledge carries over to the labelled system, told the label.** -/
theorem zeroKnowledge_labelled {Label Told : Type} (system : ArgumentSystem)
    (label : system.Weights → List Token × List Token → Label)
    (told : system.Weights → Request → Told) (tell : Label → Told)
    (same : ∀ weights request, told weights request = tell (label weights request))
    (hypothesis : Request → Prop) (error : ℕ → ℕ → ENNReal)
    (zeroKnowledge : ZeroKnowledgeWhere system hypothesis told error) :
    ZeroKnowledgeWhere (labelled system label) hypothesis label error := by
  obtain ⟨simulator, holds⟩ := zeroKnowledge
  refine ⟨labelledSimulator simulator tell,
    fun weights chooser picks queries verifier proofCount bounded => ?_⟩
  obtain ⟨close, consistent⟩ := holds weights
    (fun plain => chooser (labelView system label weights plain))
    (fun plain request chosen => picks (labelView system label weights plain) request chosen)
    queries
    (fun commitment => (verifier commitment).comapProofs (pairLabel system label weights))
    proofCount
    (fun commitment => MaliciousVerifier.queryBound_comapProofs (pairLabel system label weights)
      (verifier commitment) queries (bounded commitment))
  have real := realExperiment_labelled system label verifier chooser weights proofCount
  have simulated := simulatedExperiment_labelled system label told tell same simulator verifier
    chooser weights proofCount
  constructor
  · refine le_trans (le_of_eq ?_) ((statisticalDistance_images_le
      (realExperiment system
        (fun commitment => (verifier commitment).comapProofs (pairLabel system label weights))
        (fun plain => chooser (labelView system label weights plain)) weights proofCount)
      (AtEveryRequest.simulatedExperiment system simulator told
        (fun commitment => (verifier commitment).comapProofs (pairLabel system label weights))
        (fun plain => chooser (labelView system label weights plain)) weights proofCount)
      (labelView system label weights)).trans close)
    exact congrArg₂ (fun experiment distribution =>
      statisticalDistance (Prob experiment) (eventProbability distribution)) real simulated
  · exact ((congrArg (fun distribution => eventProbability distribution
        {view : View (Label × system.Proof) | ¬ view.queryLog.Consistent}) simulated).trans
      (eventProbability_map _ (labelView system label weights) _)).trans consistent

/-- **Zero knowledge, told less, gives zero knowledge with the label shown.** -/
theorem zeroKnowledgeShown_of_told {Label Told : Type} (system : ArgumentSystem)
    (label : system.Weights → List Token × List Token → Label)
    (told : system.Weights → Request → Told) (tell : Label → Told)
    (same : ∀ weights request, told weights request = tell (label weights request))
    (hypothesis : Request → Prop) (error : ℕ → ℕ → ENNReal)
    (zeroKnowledge : ZeroKnowledgeWhere system hypothesis told error) :
    ZeroKnowledgeShownWhere system hypothesis label error :=
  zeroKnowledge_labelled system label told tell same hypothesis error zeroKnowledge

end VerifiableInference

#print axioms VerifiableInference.toldSteps_eq_simulatedStepsWith
#print axioms VerifiableInference.realExperiment_labelled
#print axioms VerifiableInference.simulatedExperiment_labelled
#print axioms VerifiableInference.zeroKnowledge_labelled
