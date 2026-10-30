-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/MapWeightsZeroKnowledge.lean

For every argument system: `ZeroKnowledgeOn` (MoreStatements.lean) carries over to a system with
another type of weights and of public parameters (`ArgumentSystem.withWeights`, MapWeights.lean),
along a map `back` from the new weights to the old ones.
`ZeroKnowledgeOn.mapWeights`: the new honest committer and prover are the old ones at
`back weights`, and the old public parameters of `back weights` are a function `toOld` of the new
public parameters of `weights` (two of its four conditions: see its statement). The bound is the
same. In the proof the new simulator is the old one, started at `toOld` of the public parameters
that it is given (`Simulator.mapPublicParameters`).
-/
import VerifiableInference.MapWeights
import VerifiableInference.ZeroKnowledgeOn

set_option autoImplicit false

open scoped ENNReal

namespace VerifiableInference

/-! ## 1. The simulator -/

/-- The same simulator for other public parameters: it is started at `toOld` of the public
parameters that it is given. -/
def Simulator.mapPublicParameters {Old New Proof : Type} (simulator : Simulator Old Proof)
    (toOld : New → Old) : Simulator New Proof where
  State := simulator.State
  start := fun parameters proofCount => simulator.start (toOld parameters) proofCount
  answerQuery := simulator.answerQuery
  simulateProof := simulator.simulateProof

/-- After the start the two simulators take the same steps. -/
theorem simulatedSteps_mapPublicParameters {Old New Proof : Type} (simulator : Simulator Old Proof)
    (toOld : New → Old) (chooser : View Proof → Option (List Token × List Token)) :
    ∀ (verifier : MaliciousVerifier Proof) (remaining : ℕ) (view : View Proof)
      (state : simulator.State),
      simulatedSteps (simulator.mapPublicParameters toOld) chooser verifier remaining view state
        = simulatedSteps simulator chooser verifier remaining view state
  | .stop, _, _, _ => by
      simp only [simulatedSteps]
  | .query input next, remaining, view, state => by
      have ih := fun (answered : Digest × simulator.State) =>
        simulatedSteps_mapPublicParameters simulator toOld chooser (next answered.1) remaining
          { view with queryLog := view.queryLog ++ [(input, answered.1)] } answered.2
      simp only [simulatedSteps]
      exact congrArg _ (funext fun answered => ih answered)
  | .sample bound next, remaining, view, state => by
      have ih := fun draw =>
        simulatedSteps_mapPublicParameters simulator toOld chooser (next draw) remaining
          { view with randomDraws := view.randomDraws ++ [draw.val] } state
      simp only [simulatedSteps]
      exact congrArg _ (funext fun draw => ih draw)
  | .requestProof _, 0, _, _ => by
      simp only [simulatedSteps]
  | .requestProof next, remaining + 1, view, state => by
      have ih := fun request (simulated : Proof × simulator.State) =>
        simulatedSteps_mapPublicParameters simulator toOld chooser (next request simulated.1)
          remaining { view with proofs := view.proofs ++ [(request, simulated.1)] } simulated.2
      cases hChoice : chooser view with
      | none => simp only [simulatedSteps, hChoice]
      | some request =>
          simp only [simulatedSteps, hChoice]
          exact congrArg _ (funext fun simulated => ih request simulated)

/-! ## 2. The two experiments -/

section
variable (system : ArgumentSystem) (NewWeights NewPublicParameters : Type)
  (publicParameters : NewWeights → NewPublicParameters)
  (nextToken : NewWeights → List Token → Option Token) (back : NewWeights → system.Weights)

local notation "mapped" =>
  ArgumentSystem.withWeights system NewWeights NewPublicParameters publicParameters nextToken
    (fun weights => system.commit (back weights)) (fun weights => system.prove (back weights))

/-- The verifier's steps of the real experiment of the new system (`mapped`: its honest committer
and prover are the old ones at `back weights`) at `weights` are those of the old system at
`back weights`. -/
theorem realSteps_withWeights (chooser : View system.Proof → Option (List Token × List Token))
    (weights : NewWeights) (randomness : system.CommitmentRandomness) :
    ∀ (verifier : MaliciousVerifier system.Proof) (remaining : ℕ) (view : View system.Proof),
      (realSteps mapped chooser weights randomness verifier remaining view :
          RandomizedAlgorithm (View system.Proof))
        = realSteps system chooser (back weights) randomness verifier remaining view
  | .stop, _, _ => rfl
  | .query input next, remaining, view => by
      have ih := fun answer => realSteps_withWeights chooser weights randomness (next answer)
        remaining { view with queryLog := view.queryLog ++ [(input, answer)] }
      simp only [realSteps]
      exact congrArg _ (funext fun answer => ih answer)
  | .sample bound next, remaining, view => by
      have ih := fun draw => realSteps_withWeights chooser weights randomness (next draw)
        remaining { view with randomDraws := view.randomDraws ++ [draw.val] }
      simp only [realSteps]
      exact congrArg _ (funext fun draw => ih draw)
  | .requestProof _, 0, _ => rfl
  | .requestProof next, remaining + 1, view => by
      have ih := fun request proof => realSteps_withWeights chooser weights randomness
        (next request proof) remaining { view with proofs := view.proofs ++ [(request, proof)] }
      cases hChoice : chooser view with
      | none => simp only [ArgumentSystem.withWeights, realSteps, hChoice]
      | some request =>
          simp only [ArgumentSystem.withWeights, realSteps, hChoice]
          exact congrArg _ (funext fun proof => ih request proof)

/-- The real experiment of the new system at `weights` is that of the old system at
`back weights`. -/
theorem realExperiment_withWeights (verifier : Commitment → MaliciousVerifier system.Proof)
    (chooser : View system.Proof → Option (List Token × List Token)) (weights : NewWeights)
    (proofCount : ℕ) :
    (realExperiment mapped verifier chooser weights proofCount :
        RandomizedAlgorithm (View system.Proof))
      = realExperiment system verifier chooser (back weights) proofCount := by
  show (system.sampleCommitmentRandomness.bind fun randomness =>
      (system.commit (back weights) randomness).toRandomized.bind fun commitment =>
        realSteps mapped chooser weights randomness (verifier commitment) proofCount
          ⟨commitment, [], [], []⟩)
    = system.sampleCommitmentRandomness.bind fun randomness =>
      (system.commit (back weights) randomness).toRandomized.bind fun commitment =>
        realSteps system chooser (back weights) randomness (verifier commitment) proofCount
          ⟨commitment, [], [], []⟩
  exact congrArg _ (funext fun randomness => congrArg _ (funext fun commitment =>
    realSteps_withWeights system NewWeights NewPublicParameters publicParameters nextToken back
      chooser weights randomness (verifier commitment) proofCount ⟨commitment, [], [], []⟩))

/-- If the old public parameters of `back weights` are `toOld` of the new public parameters of
`weights` (`hPublic`): the simulated experiment of the new system at `weights`, with the simulator
started at `toOld` of the public parameters that it is given, is that of the old system at
`back weights`. -/
theorem simulatedExperiment_withWeights (toOld : NewPublicParameters → system.PublicParameters)
    (hPublic : ∀ weights, toOld (publicParameters weights) = system.publicParameters (back weights))
    (simulator : Simulator system.PublicParameters system.Proof)
    (verifier : Commitment → MaliciousVerifier system.Proof)
    (chooser : View system.Proof → Option (List Token × List Token)) (weights : NewWeights)
    (proofCount : ℕ) :
    (simulatedExperiment mapped (simulator.mapPublicParameters toOld) verifier chooser weights
        proofCount : PMF (View system.Proof))
      = simulatedExperiment system simulator verifier chooser (back weights) proofCount := by
  show ((simulator.start (toOld (publicParameters weights)) proofCount).bind fun started =>
      simulatedSteps (simulator.mapPublicParameters toOld) chooser (verifier started.1) proofCount
        ⟨started.1, [], [], []⟩ started.2)
    = (simulator.start (system.publicParameters (back weights)) proofCount).bind fun started =>
      simulatedSteps simulator chooser (verifier started.1) proofCount ⟨started.1, [], [], []⟩
        started.2
  rw [hPublic weights]
  exact congrArg _ (funext fun started =>
    simulatedSteps_mapPublicParameters simulator toOld chooser (verifier started.1) proofCount
      ⟨started.1, [], [], []⟩ started.2)

/-! ## 3. The theorem `ZeroKnowledgeOn.mapWeights` -/

/-- `ZeroKnowledgeOn` carries over, with the same ζ, along a map `back` from new weights to old
ones, on four conditions. The new honest committer and prover are the old ones at `back weights`.
The old public parameters of `back weights` are `toOld` of the new public parameters of `weights`.
The new domain implies the old one at `back weights`. On the new domain, "the output tokens are the
model's" for the new model function implies the same for the old one at `back weights`.
Nothing is asked of `publicParameters` but `hPublic`: the new public parameters may contain more
than the old ones. They are handed to the simulator, so whatever they hold is outside what is
hidden. -/
theorem ZeroKnowledgeOn.mapWeights
    (domain : system.Weights → List Token → List Token → Prop) (ζ : ℕ → ℕ → ℝ≥0∞)
    (zeroKnowledge : ZeroKnowledgeOn system domain ζ)
    (toOld : NewPublicParameters → system.PublicParameters)
    (hPublic : ∀ weights, toOld (publicParameters weights) = system.publicParameters (back weights))
    (newDomain : NewWeights → List Token → List Token → Prop)
    (hDomain : ∀ (weights : NewWeights) (prompt output : List Token),
      newDomain weights prompt output → domain (back weights) prompt output)
    (hOutput : ∀ (weights : NewWeights) (prompt output : List Token),
      newDomain weights prompt output →
      (∀ position (h : position < output.length),
        nextToken weights (prompt ++ output.take position) = some output[position]) →
      system.IsModelOutput (back weights) prompt output) :
    ZeroKnowledgeOn mapped newDomain ζ := by
  obtain ⟨simulator, h⟩ := zeroKnowledge
  refine ⟨simulator.mapPublicParameters toOld,
    fun weights chooser hChooser queries verifier proofCount hV => ?_⟩
  have key := h (back weights) chooser
    (fun view prompt output hc =>
      ⟨hDomain weights prompt output (hChooser view prompt output hc).1,
        hOutput weights prompt output (hChooser view prompt output hc).1
          (hChooser view prompt output hc).2⟩)
    queries verifier proofCount hV
  rw [← realExperiment_withWeights system NewWeights NewPublicParameters publicParameters nextToken
      back verifier chooser weights proofCount,
    ← simulatedExperiment_withWeights system NewWeights NewPublicParameters publicParameters
      nextToken back toOld hPublic simulator verifier chooser weights proofCount] at key
  exact key

end

end VerifiableInference

#print axioms VerifiableInference.ZeroKnowledgeOn.mapWeights
#print axioms VerifiableInference.simulatedSteps_mapPublicParameters
#print axioms VerifiableInference.realSteps_withWeights
#print axioms VerifiableInference.realExperiment_withWeights
#print axioms VerifiableInference.simulatedExperiment_withWeights
