-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Statements.lean

The statements for an argument system for the output tokens of a committed model: soundness,
completeness, zero-knowledge.

Statements only. `Sound`, `SoundAndBinding`, `SoundOpened`, `Complete`, `ZeroKnowledge` and
`CompleteSoundZeroKnowledge` below are properties that an argument system may have. They are general
definitions, stated before any system; nothing in this file is proved about any.
Which of them are proved, of which system: lean/GAPS.md, 39. The theorem on the Lean verifier:
lean/THEOREM.md.
The file imports VerifiableInference/RandomOracleModel.lean and nothing else.
-/
import VerifiableInference.RandomOracleModel
noncomputable section -- markers lifted: Lean tags what it cannot compile

set_option autoImplicit false

open scoped ENNReal

namespace VerifiableInference

/-! ## 1. An argument system: one model, one committer, one prover, one verifier -/

/-- A token. -/
abbrev Token : Type := ℕ

/-- A commitment to the weights of a model: 256 bits. The committer publishes it. -/
abbrev Commitment : Type := Digest

/-- An argument system for the output tokens of a committed model:
the model, the honest committer, the honest prover and the verifier that the three statements are
about. -/
structure ArgumentSystem where
  /-- What a commitment commits to: the weights of one model. -/
  Weights : Type
  /-- What proofs may reveal of the weights (exactly: what `simulatedExperiment` hands to
  `Simulator.start`, which makes the commitment from it). -/
  PublicParameters : Type
  /-- The part of the weights that proofs may reveal. -/
  publicParameters : Weights → PublicParameters
  /-- The committer's randomness. -/
  CommitmentRandomness : Type
  /-- A proof. -/
  Proof : Type
  /-- The model: the next token after the given tokens; `none` where the model has no value on
  them. -/
  nextToken : Weights → List Token → Option Token
  /-- The honest committer, first step: it samples its randomness. -/
  sampleCommitmentRandomness : RandomizedAlgorithm CommitmentRandomness
  /-- The honest committer, second step: the commitment to the weights under that randomness. -/
  commit : Weights → CommitmentRandomness → DeterministicAlgorithm Commitment
  /-- The honest prover: from the weights, the committer's randomness, a prompt and output tokens, a
  proof. -/
  prove : Weights → CommitmentRandomness → List Token → List Token → RandomizedAlgorithm Proof
  /-- The verifier: from a commitment, a prompt, output tokens and a proof, a decision. -/
  verify : Commitment → List Token → List Token → Proof → DeterministicAlgorithm Bool

/-- The verifier's decision under a hash function: the verifier, evaluated with it. -/
def ArgumentSystem.accepts (system : ArgumentSystem) (hash : Hash) (commitment : Commitment)
    (prompt output : List Token)
    (proof : system.Proof) : Bool :=
  (system.verify commitment prompt output proof).evaluate hash

/-- The output tokens are the model's: each of them is the model's next token after the prompt and
the output tokens before it. -/
def ArgumentSystem.IsModelOutput (system : ArgumentSystem) (weights : system.Weights)
    (prompt output : List Token) : Prop :=
  ∀ position (h : position < output.length),
    system.nextToken weights (prompt ++ output.take position) = some output[position]

/-! ## 2. Soundness -/

/-- Soundness. There is one extractor such that, for every committer with at most `committerQueries`
queries to the hash function and every prover with at most `proverQueries` queries: the probability
that the verifier accepts output tokens that are not those of the model with the weights that the
extractor gives, from the committer's commitment and queries, is at most ε (committerQueries +
proverQueries).
The prover picks the prompt and the output tokens. If the extractor gives no weights, every accepted
proof counts as a failure. The committer passes its state to the prover, so the two may act as one
adversary. -/
def Sound (system : ArgumentSystem) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∃ extractor : Commitment → QueryLog → Option system.Weights,
    ∀ (committerQueries proverQueries : ℕ) (State : Type)
      (committer : RandomizedAlgorithm (Commitment × State)),
      committer.QueryBound committerQueries →
      ∀ prover : State → RandomizedAlgorithm (List Token × List Token × system.Proof),
        (∀ state, (prover state).QueryBound proverQueries) →
        Prob (do
            let ((commitment, state), queryLog) ← committer.withQueryLog
            let (prompt, output, proof) ← prover state
            let accepted ← (system.verify commitment prompt output proof).toRandomized
            pure (extractor commitment queryLog, prompt, output, accepted))
          {(extracted, prompt, output, accepted) |
            accepted = true ∧
            ¬ ∃ weights, extracted = some weights ∧ system.IsModelOutput weights prompt output}
          ≤ ε (committerQueries + proverQueries)

/-- Soundness with the commitment bound to the weights. There is one extractor such that, for every
committer with at most `committerQueries` queries to the hash function:
(1) As in `Sound`: for every prover with at most `proverQueries` queries, the probability that the
    verifier accepts output tokens that are not those of the model with the weights that the
    extractor gives is at most ε (committerQueries + proverQueries);
(2) For every opener with at most `proverQueries` queries, the probability that it returns weights
    and randomness whose commitment is the committer's, while the extractor does not give these
    weights, is at most ε (committerQueries + proverQueries). -/
def SoundAndBinding (system : ArgumentSystem) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∃ extractor : Commitment → QueryLog → Option system.Weights,
    ∀ (committerQueries proverQueries : ℕ) (State : Type)
      (committer : RandomizedAlgorithm (Commitment × State)),
      committer.QueryBound committerQueries →
      (∀ prover : State → RandomizedAlgorithm (List Token × List Token × system.Proof),
        (∀ state, (prover state).QueryBound proverQueries) →
        Prob (do
            let ((commitment, state), queryLog) ← committer.withQueryLog
            let (prompt, output, proof) ← prover state
            let accepted ← (system.verify commitment prompt output proof).toRandomized
            pure (extractor commitment queryLog, prompt, output, accepted))
          {(extracted, prompt, output, accepted) |
            accepted = true ∧
            ¬ ∃ weights, extracted = some weights ∧ system.IsModelOutput weights prompt output}
          ≤ ε (committerQueries + proverQueries)) ∧
      (∀ opener : State → RandomizedAlgorithm (system.Weights × system.CommitmentRandomness),
        (∀ state, (opener state).QueryBound proverQueries) →
        Prob (do
            let ((commitment, state), queryLog) ← committer.withQueryLog
            let (weights, randomness) ← opener state
            let recomputed ← (system.commit weights randomness).toRandomized
            pure (extractor commitment queryLog, commitment, weights, recomputed))
          {(extracted, commitment, weights, recomputed) |
            recomputed = commitment ∧ extracted ≠ some weights}
          ≤ ε (committerQueries + proverQueries))

/-- Soundness for an opened commitment (it follows from `SoundAndBinding` with 2 ε for ε:
VerifiableInference/Checks.lean, soundOpened_of_soundAndBinding).
One adversary with at most `queries` queries to the hash function returns a commitment, weights with
randomness, a prompt, output tokens and a proof.
The probability that the commitment to these weights under this randomness is the returned one, the
verifier accepts, and the output tokens are not the model's is at most ε queries. -/
def SoundOpened (system : ArgumentSystem) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (queries : ℕ)
    (adversary : RandomizedAlgorithm
      (Commitment × (system.Weights × system.CommitmentRandomness) ×
          (List Token × List Token × system.Proof))),
    adversary.QueryBound queries →
      Prob (do
          let (commitment, (weights, randomness), (prompt, output, proof)) ← adversary
          let recomputed ← (system.commit weights randomness).toRandomized
          let accepted ← (system.verify commitment prompt output proof).toRandomized
          pure (commitment, recomputed, weights, prompt, output, accepted))
        {(commitment, recomputed, weights, prompt, output, accepted) |
          recomputed = commitment ∧ accepted = true ∧ ¬ system.IsModelOutput weights prompt output}
        ≤ ε queries

/-! ## 3. Completeness -/

/-- Completeness. For all weights, every prompt and every list of output tokens that is the model's
on it (the empty list is one): a committer and a prover that are both honest are rejected with
probability at most α. A verifier that refuses a request whose output is the model's, whatever the
proof, meets it at no α < 1 (`not_complete_of_rejected`, NotComplete.lean); a form on a stated set
of requests is `CompleteOn` (lean/GAPS.md, 39). -/
def Complete (system : ArgumentSystem) (α : ℝ≥0∞) : Prop :=
  ∀ (weights : system.Weights) (prompt output : List Token),
    system.IsModelOutput weights prompt output →
      Prob (do
          let randomness ← system.sampleCommitmentRandomness
          let commitment ← (system.commit weights randomness).toRandomized
          let proof ← system.prove weights randomness prompt output
          (system.verify commitment prompt output proof).toRandomized)
        {accepted | accepted = false}
        ≤ α

/-! ## 4. Zero-knowledge: the two experiments -/

/-- What a verifier has seen: the commitment; the proofs that it obtained, each with its prompt and
output tokens; its queries to the hash function with their answers; its own random choices. -/
structure View (Proof : Type) where
  commitment : Commitment
  proofs : List ((List Token × List Token) × Proof)
  queryLog : QueryLog
  randomDraws : List ℕ

/-- A malicious verifier: any strategy of one who is given the commitment and then proofs. It is a
tree. At each step it
* stops, or
* queries the hash function at a bit string and continues with the answer, or
* samples a number uniformly from 0, …, `bound` and continues with it, or
* requests the next proof and continues with the prompt, the output tokens and the proof that it is
  given. -/
inductive MaliciousVerifier (Proof : Type) : Type
  | stop : MaliciousVerifier Proof
  | query (input : BitString) (next : Digest → MaliciousVerifier Proof) : MaliciousVerifier Proof
  | sample (bound : ℕ) (next : Fin (bound + 1) → MaliciousVerifier Proof) : MaliciousVerifier Proof
  | requestProof (next : List Token × List Token → Proof → MaliciousVerifier Proof) :
      MaliciousVerifier Proof

/-- The verifier makes at most `queries` queries to the hash function, in all, on every path. -/
def MaliciousVerifier.QueryBound {Proof : Type} : MaliciousVerifier Proof → ℕ → Prop
  | .stop, _ => True
  | .query _ _, 0 => False
  | .query _ next, queries + 1 => ∀ answer, (next answer).QueryBound queries
  | .sample _ next, queries => ∀ draw, (next draw).QueryBound queries
  | .requestProof next, queries => ∀ request proof, (next request proof).QueryBound queries

/-- The real experiment after the commitment: the verifier's steps. `remaining` is the number of
proofs that it may still request. A request beyond it ends the experiment.
For each request, `chooser` picks the prompt and the output tokens from the verifier's view so far
(or nothing, which ends the experiment), and the honest prover makes the proof. -/
def realSteps (system : ArgumentSystem) (chooser : View system.Proof → Option
    (List Token × List Token))
    (weights : system.Weights) (randomness : system.CommitmentRandomness) :
    MaliciousVerifier system.Proof → ℕ → View system.Proof → RandomizedAlgorithm (View system.Proof)
  | .stop, _, view => pure view
  | .query input next, remaining, view =>
      .query input fun answer =>
        realSteps system chooser weights randomness (next answer) remaining
          { view with queryLog := view.queryLog ++ [(input, answer)] }
  | .sample bound next, remaining, view =>
      .sample bound fun draw =>
        realSteps system chooser weights randomness (next draw) remaining
          { view with randomDraws := view.randomDraws ++ [draw.val] }
  | .requestProof _, 0, view => pure view
  | .requestProof next, remaining + 1, view =>
      match chooser view with
      | none => pure view
      | some request =>
        (system.prove weights randomness request.1 request.2).bind fun proof =>
          realSteps system chooser weights randomness (next request proof) remaining
            { view with proofs := view.proofs ++ [(request, proof)] }

/-- The real experiment: the honest committer commits to the weights; the verifier is given the
commitment and up to `proofCount` proofs of the honest prover. The result is the verifier's view. -/
def realExperiment (system : ArgumentSystem) (verifier : Commitment → MaliciousVerifier
    system.Proof)
    (chooser : View system.Proof → Option (List Token × List Token))
    (weights : system.Weights) (proofCount : ℕ) : RandomizedAlgorithm (View system.Proof) := do
  let randomness ← system.sampleCommitmentRandomness
  let commitment ← (system.commit weights randomness).toRandomized
  realSteps system chooser weights randomness (verifier commitment) proofCount
      ⟨commitment, [], [], []⟩

/-- A simulator: from the public parameters and the largest number of proofs it makes a commitment;
it answers the verifier's queries to the hash function; it makes each proof from the prompt and the
output tokens.
Beyond these it is given neither the weights nor the committer's randomness. -/
structure Simulator (PublicParameters Proof : Type) where
  State : Type
  start : PublicParameters → ℕ → PMF (Commitment × State)
  answerQuery : State → BitString → PMF (Digest × State)
  simulateProof : State → List Token × List Token → PMF (Proof × State)

/-- The simulated experiment after the commitment: the same steps, with the simulator in the place
of the hash function and of the prover. -/
def simulatedSteps {PublicParameters Proof : Type}
    (simulator : Simulator PublicParameters Proof)
    (chooser : View Proof → Option (List Token × List Token)) :
    MaliciousVerifier Proof → ℕ → View Proof → simulator.State → PMF (View Proof)
  | .stop, _, view, _ => PMF.pure view
  | .query input next, remaining, view, state =>
      (simulator.answerQuery state input).bind fun answered =>
        simulatedSteps simulator chooser (next answered.1) remaining
          { view with queryLog := view.queryLog ++ [(input, answered.1)] } answered.2
  | .sample bound next, remaining, view, state =>
      (PMF.uniformOfFintype (Fin (bound + 1))).bind fun draw =>
        simulatedSteps simulator chooser (next draw) remaining
          { view with randomDraws := view.randomDraws ++ [draw.val] } state
  | .requestProof _, 0, view, _ => PMF.pure view
  | .requestProof next, remaining + 1, view, state =>
      match chooser view with
      | none => PMF.pure view
      | some request =>
        (simulator.simulateProof state request).bind fun simulated =>
          simulatedSteps simulator chooser (next request simulated.1) remaining
            { view with proofs := view.proofs ++ [(request, simulated.1)] } simulated.2

/-- The simulated experiment: the simulator is given the public parameters of the weights and the
largest number of proofs.
The result is the verifier's view. -/
def simulatedExperiment (system : ArgumentSystem)
    (simulator : Simulator system.PublicParameters system.Proof)
    (verifier : Commitment → MaliciousVerifier system.Proof)
    (chooser : View system.Proof → Option (List Token × List Token))
    (weights : system.Weights) (proofCount : ℕ) : PMF (View system.Proof) :=
  (simulator.start (system.publicParameters weights) proofCount).bind fun started =>
    simulatedSteps simulator chooser (verifier started.1) proofCount ⟨started.1, [], [], []⟩
        started.2

/-- No query of the log has two different answers. -/
def QueryLog.Consistent (queryLog : QueryLog) : Prop :=
  ∀ input answer answer', (input, answer) ∈ queryLog → (input, answer') ∈ queryLog → answer =
      answer'

/-! ## 5. Zero-knowledge -/

/-- Zero-knowledge. There is one simulator, which is given the public parameters of the weights, the
largest number of proofs, each query of the verifier to the hash function, which it answers in the
hash function's place, and, for each proof, the prompt and the output tokens, such that for all
weights and every verifier with at most `queries` queries to the hash function, which is given the
commitment and up to `proofCount` proofs, each for a prompt and output tokens that are picked from
the verifier's view so far by a chooser, which may know the weights and is the same in both
experiments, among those whose output tokens are the model's: the statistical distance between its
view with the honest committer and prover and what the simulator produces is at most
ζ queries proofCount; and the simulator never answers one query in two ways. A general definition:
this library proves it of no system. The form on a stated set of requests is `ZeroKnowledgeOn`
(VerifiableInference/MoreStatements.lean). -/
def ZeroKnowledge (system : ArgumentSystem) (ζ : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∃ simulator : Simulator system.PublicParameters system.Proof,
    ∀ (weights : system.Weights)
      (chooser : View system.Proof → Option (List Token × List Token)),
      (∀ view prompt output, chooser view = some (prompt, output) → system.IsModelOutput weights
          prompt output) →
      ∀ (queries : ℕ) (verifier : Commitment → MaliciousVerifier system.Proof) (proofCount : ℕ),
        (∀ commitment, (verifier commitment).QueryBound queries) →
          statisticalDistance
              (Prob (realExperiment system verifier chooser weights proofCount))
              (eventProbability (simulatedExperiment system simulator verifier chooser weights
                  proofCount))
            ≤ ζ queries proofCount
          ∧ eventProbability (simulatedExperiment system simulator verifier chooser weights
              proofCount)
              {view | ¬ view.queryLog.Consistent} = 0

/-! ## 6. The three together -/

/-- The three statements together, with their bounds, in one line:
`CompleteSoundZeroKnowledge system α ε ζ`. A general definition: this library proves that line of no
system. The form on a stated set of requests is `CompleteSoundZeroKnowledgeOn`
(VerifiableInference/MoreStatements.lean).
-/
structure CompleteSoundZeroKnowledge (system : ArgumentSystem) (α : ℝ≥0∞) (ε : ℕ → ℝ≥0∞)
    (ζ : ℕ → ℕ → ℝ≥0∞) : Prop where
  sound : Sound system ε
  complete : Complete system α
  zeroKnowledge : ZeroKnowledge system ζ

end VerifiableInference
