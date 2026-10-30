-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/AtEveryRequest.lean: completeness and zero knowledge of an argument system at
the requests that meet a hypothesis.

 1. A request is a prompt with a claimed output. Every pair of lists of tokens is a request.
 2. A hypothesis says of which requests a statement speaks. The trivial one gives every request.
 3. ProofAcceptedWhere: at such a request, if the result is the claimed output, the honest proof is
    accepted, up to the error.
 4. The result is an argument of the statement: it reads the weights, as a prover can.
 5. ZeroKnowledgeWhere compares two experiments, in which a verifier sees a commitment and proofs.
 6. In the real one the honest prover runs at every request that the chooser picks.
 7. In the other a simulator makes them, and answers the hash queries.
 8. What the simulator is told of each request is an argument of the statement.
 9. A chooser picks requests that meet the hypothesis, from all that the verifier has seen.
10. A statement at a hypothesis follows from the same statement at a wider one, at the same error.
-/
import VerifiableInference.Statements

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.AtEveryRequest

open scoped ENNReal

/-! ## 1. Requests -/

/-- A request: a prompt with a claimed output. -/
abbrev Request : Type := List Token × List Token

/-- The bit of a request: served or refused. -/
inductive Outcome : Type where
  | served : Outcome
  | refused : Outcome
  deriving DecidableEq

/-! ## 2. Completeness -/

/-- Completeness on proofs: for all weights and every request that meets the hypothesis, if the
result is the claimed output: with the honest committer and prover, the proof is rejected with
probability at most `error`. The probability is over a hash function drawn at random and the honest
side's coins. -/
def ProofAcceptedWhere (system : ArgumentSystem) (hypothesis : Request → Prop)
    (result : system.Weights → Request → Option (List Token)) (error : ℝ≥0∞) : Prop :=
  ∀ (weights : system.Weights) (request : Request), hypothesis request →
    result weights request = some request.2 →
    Prob (do
        let randomness ← system.sampleCommitmentRandomness
        let commitment ← (system.commit weights randomness).toRandomized
        let proof ← system.prove weights randomness request.1 request.2
        (system.verify commitment request.1 request.2 proof).toRandomized)
      {accepted | accepted = false}
      ≤ error

/-- The honest side stays within a budget of hash queries: one run of the sampler, one of the
committer and one of the prover. -/
def WithinBudget (system : ArgumentSystem) (budget : ℕ) : Prop :=
  ∃ sampling committing proving : ℕ,
    sampling + committing + proving ≤ budget ∧
    system.sampleCommitmentRandomness.QueryBound sampling ∧
    (∀ weights randomness,
      (system.commit weights randomness).toRandomized.QueryBound committing) ∧
    (∀ weights randomness prompt output,
      (system.prove weights randomness prompt output).QueryBound proving)

/-! ## 3. Zero knowledge -/

/-- A simulator. From the public parameters and the largest number of proofs it makes a commitment;
it answers the verifier's queries to the hash function; it makes each proof from the request and
from what it is told of that request. Beyond these it is given neither the weights nor the
committer's randomness. Its work is not bounded. -/
structure Simulator (PublicParameters Told Proof : Type) where
  State : Type
  start : PublicParameters → ℕ → PMF (Commitment × State)
  answerQuery : State → BitString → PMF (Digest × State)
  simulateProof : State → Request → Told → PMF (Proof × State)

/-- The simulated experiment after the commitment: the steps of `realSteps`
(VerifiableInference/Statements.lean), with the simulator in the place of the hash function and of
the prover. -/
def simulatedSteps {PublicParameters Told Proof : Type}
    (simulator : Simulator PublicParameters Told Proof) (told : Request → Told)
    (chooser : View Proof → Option Request) :
    MaliciousVerifier Proof → ℕ → View Proof → simulator.State → PMF (View Proof)
  | .stop, _, view, _ => PMF.pure view
  | .query input next, remaining, view, state =>
      (simulator.answerQuery state input).bind fun answered =>
        simulatedSteps simulator told chooser (next answered.1) remaining
          { view with queryLog := view.queryLog ++ [(input, answered.1)] } answered.2
  | .sample bound next, remaining, view, state =>
      (PMF.uniformOfFintype (Fin (bound + 1))).bind fun draw =>
        simulatedSteps simulator told chooser (next draw) remaining
          { view with randomDraws := view.randomDraws ++ [draw.val] } state
  | .requestProof _, 0, view, _ => PMF.pure view
  | .requestProof next, remaining + 1, view, state =>
      match chooser view with
      | none => PMF.pure view
      | some request =>
        (simulator.simulateProof state request (told request)).bind fun simulated =>
          simulatedSteps simulator told chooser (next request simulated.1) remaining
            { view with proofs := view.proofs ++ [(request, simulated.1)] } simulated.2

/-- The simulated experiment: the simulator is given the public parameters of the weights and the
largest number of proofs; it is told of each request what `told` says at the weights. -/
def simulatedExperiment {Told : Type} (system : ArgumentSystem)
    (simulator : Simulator system.PublicParameters Told system.Proof)
    (told : system.Weights → Request → Told)
    (verifier : Commitment → MaliciousVerifier system.Proof)
    (chooser : View system.Proof → Option Request)
    (weights : system.Weights) (proofCount : ℕ) : PMF (View system.Proof) :=
  (simulator.start (system.publicParameters weights) proofCount).bind fun started =>
    simulatedSteps simulator (told weights) chooser (verifier started.1) proofCount
      ⟨started.1, [], [], []⟩ started.2

/-- Zero knowledge at the requests that meet a hypothesis, where the simulator is told `told`. The
real experiment is `realExperiment` (VerifiableInference/Statements.lean): the honest prover runs at
every request that the chooser picks, and nothing there reads `told`. There is one simulator such
that, for all weights, every chooser of such requests, and every verifier with at most `queries`
queries to the hash function: the statistical distance between the verifier's view with the honest
committer and prover and what the simulator produces is at most `error queries proofCount`; and the
simulator never answers one query in two ways. A chooser picks each request from all that the
verifier has seen; it may know the weights, and it is the same in both experiments. The verifier has
no query before the commitment. -/
def ZeroKnowledgeWhere {Told : Type} (system : ArgumentSystem) (hypothesis : Request → Prop)
    (told : system.Weights → Request → Told) (error : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∃ simulator : Simulator system.PublicParameters Told system.Proof,
    ∀ (weights : system.Weights) (chooser : View system.Proof → Option Request),
      (∀ view request, chooser view = some request → hypothesis request) →
      ∀ (queries : ℕ) (verifier : Commitment → MaliciousVerifier system.Proof) (proofCount : ℕ),
      (∀ commitment, (verifier commitment).QueryBound queries) →
        statisticalDistance
            (Prob (realExperiment system verifier chooser weights proofCount))
            (eventProbability (simulatedExperiment system simulator told verifier chooser weights
                proofCount))
          ≤ error queries proofCount
        ∧ eventProbability (simulatedExperiment system simulator told verifier chooser weights
            proofCount)
            {view | ¬ view.queryLog.Consistent} = 0

/-- The same with a bar on the error: at most `bar`, up to `queries` hash queries and `proofs`
proofs. -/
def ZeroKnowledgeBelowWhere {Told : Type} (system : ArgumentSystem) (hypothesis : Request → Prop)
    (told : system.Weights → Request → Told) (queries proofs : ℕ) (bar : ℝ≥0∞) : Prop :=
  ∃ error : ℕ → ℕ → ℝ≥0∞,
    (∀ asked replies, asked ≤ queries → replies ≤ proofs → error asked replies ≤ bar) ∧
      ZeroKnowledgeWhere system hypothesis told error

/-! ## 4. A narrower hypothesis -/

/-- `ProofAcceptedWhere` at a hypothesis gives it at a narrower one. -/
theorem ProofAcceptedWhere.narrow {system : ArgumentSystem} {wide narrow : Request → Prop}
    {result : system.Weights → Request → Option (List Token)} {error : ℝ≥0∞}
    (inside : ∀ request, narrow request → wide request)
    (accepted : ProofAcceptedWhere system wide result error) :
    ProofAcceptedWhere system narrow result error :=
  fun weights request holds isResult => accepted weights request (inside request holds) isResult

/-- `ZeroKnowledgeWhere` at a hypothesis gives it at a narrower one, with the same simulator. -/
theorem ZeroKnowledgeWhere.narrow {Told : Type} {system : ArgumentSystem}
    {wide narrow : Request → Prop} {told : system.Weights → Request → Told}
    {error : ℕ → ℕ → ℝ≥0∞} (inside : ∀ request, narrow request → wide request)
    (zeroKnowledge : ZeroKnowledgeWhere system wide told error) :
    ZeroKnowledgeWhere system narrow told error := by
  obtain ⟨simulator, holds⟩ := zeroKnowledge
  exact ⟨simulator, fun weights chooser picks =>
    holds weights chooser fun view request chosen => inside request (picks view request chosen)⟩

/-- `ZeroKnowledgeBelowWhere` at a hypothesis gives it at a narrower one. -/
theorem ZeroKnowledgeBelowWhere.narrow {Told : Type} {system : ArgumentSystem}
    {wide narrow : Request → Prop} {told : system.Weights → Request → Told}
    {queries proofs : ℕ} {bar : ℝ≥0∞} (inside : ∀ request, narrow request → wide request)
    (below : ZeroKnowledgeBelowWhere system wide told queries proofs bar) :
    ZeroKnowledgeBelowWhere system narrow told queries proofs bar := by
  obtain ⟨error, bounded, zeroKnowledge⟩ := below
  exact ⟨error, bounded, ZeroKnowledgeWhere.narrow inside zeroKnowledge⟩

end VerifiableInference.AtEveryRequest
