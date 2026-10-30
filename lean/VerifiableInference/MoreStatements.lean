-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/MoreStatements.lean

Further statements about an argument system, beside those of VerifiableInference/Statements.lean:
soundness with the extractor named and for any claim; that the extractor gives back honestly
committed weights; soundness after an honest commitment; zero-knowledge on a stated set of requests;
that the commitment binds to the extractor's weights; that nobody opens one commitment to two
different weights; soundness for several proofs and for several commitments; the three statements
together, two of them on a stated set of requests.
Completeness on a stated set of requests, `CompleteOn`, stands in VerifiableInference/Steps.lean.
Statements only. Every `def ... : Prop` or `structure ... : Prop` below is a property that an
argument system may have; nothing in this file is proved about any. The four theorems say how two
definitions relate:
`sound_iff_soundFor` and `zeroKnowledge_iff_zeroKnowledgeOn` tie a definition here to one of
Statements.lean, the other two tie two definitions of this file. Each holds by unfolding them.
What is proved, of which system: lean/GAPS.md, 39; lean/THEOREM.md.
The file imports VerifiableInference/Statements.lean and VerifiableInference/Steps.lean, which
imports that file alone.
-/
import VerifiableInference.Statements
import VerifiableInference.Steps
noncomputable section -- markers lifted: Lean tags what it cannot compile

set_option autoImplicit false

open scoped ENNReal

namespace VerifiableInference

/-! ## Soundness with the extractor named, and for any claim

Soundness for a claim: the statement `Sound` of VerifiableInference/Statements.lean, with any claim
on weights, a prompt and output tokens in place of "the output tokens are the model's". -/

/-- Soundness for a claim, for a given extractor. For every committer with at most
`committerQueries` queries to the hash function and every prover with at most `proverQueries`
queries: the probability that the verifier accepts, while the extractor gives no weights from the
committer's commitment and queries, or gives weights for which the claim does not hold for the
prompt and the output tokens, is at most ε (committerQueries + proverQueries). -/
def SoundForWith (system : ArgumentSystem) (extractor : Commitment → QueryLog → Option
    system.Weights)
    (claim : system.Weights → List Token → List Token → Prop) (ε : ℕ → ℝ≥0∞) : Prop :=
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
            ¬ ∃ weights, extracted = some weights ∧ claim weights prompt output}
          ≤ ε (committerQueries + proverQueries)

/-- Soundness for a claim. There is one extractor for which soundness for the claim holds. The
statement says as much as the claim says: the claim is part of what a reader has to read. A claim
that some weights meet for every prompt and all output tokens makes the statement true of every
argument system, with ε = 0 (an argument; no theorem of this library states it). -/
def SoundFor (system : ArgumentSystem) (claim : system.Weights → List Token → List Token → Prop)
    (ε : ℕ → ℝ≥0∞) : Prop :=
  ∃ extractor : Commitment → QueryLog → Option system.Weights, SoundForWith system extractor claim ε

/-- `Sound` is soundness for the claim that the output tokens are the model's. -/
theorem sound_iff_soundFor (system : ArgumentSystem) (ε : ℕ → ℝ≥0∞) : Sound system ε ↔ SoundFor
    system system.IsModelOutput ε := Iff.rfl

/-! ## The extractor gives back honestly committed weights

A statement beside `Sound`: the extractor gives back the weights of an honest commitment. -/

/-- That the extractor gives back the honest committer's own weights, but for probability α.
For all weights: run the honest committer on them, and give the extractor the commitment and all
queries of that run. The probability that it does not return these weights is at most α.
`Sound` says that, but for a probability of at most ε, an accepted output is the output of the
weights that the extractor returns from the commitment and the committer's queries. This statement,
for the same extractor, says which weights these are when the committer is the honest one. It does
not join the two. -/
def ExtractsCommittedWeights (system : ArgumentSystem)
    (extractor : Commitment → QueryLog → Option system.Weights) (α : ℝ≥0∞) : Prop :=
  ∀ weights : system.Weights,
    Prob (do
        let (commitment, queryLog) ←
          (system.sampleCommitmentRandomness.bind fun randomness =>
            (system.commit weights randomness).toRandomized).withQueryLog
        pure (extractor commitment queryLog))
      {extracted | extracted ≠ some weights}
      ≤ α

/-! ## Soundness after an honest commitment

A statement beside `Sound`: soundness after an honest commitment, with no extractor in it. -/

/-- Soundness after an honest commitment, for a claim. Fix any weights, before the hash function is
sampled. The honest committer commits to them; a prover is given the commitment and the committer's
randomness and returns a prompt, output tokens and a proof; the verifier decides. Let the honest
committer make at most `committerQueries` queries to the hash function at these weights, and the
prover at most `proverQueries`. The probability that the verifier accepts while the claim does not
hold for these weights, the prompt and the output tokens is at most
ε committerQueries proverQueries.
The prover is chosen after the weights, so it may know them; with the randomness it can make honest
proofs itself; the queries for that count in `proverQueries`. The probability is also over the
committer's randomness: it is an average over honest commitments and says nothing of a single one.
That a given commitment was made honestly is outside the statement. No extractor occurs. One
commitment, one proof. -/
def SoundAfterHonestCommitmentFor (system : ArgumentSystem)
    (claim : system.Weights → List Token → List Token → Prop) (ε : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (weights : system.Weights) (committerQueries proverQueries : ℕ),
    (system.sampleCommitmentRandomness.bind fun randomness =>
      (system.commit weights randomness).toRandomized).QueryBound committerQueries →
    ∀ prover : Commitment → system.CommitmentRandomness →
        RandomizedAlgorithm (List Token × List Token × system.Proof),
      (∀ commitment randomness, (prover commitment randomness).QueryBound proverQueries) →
      Prob (do
          let randomness ← system.sampleCommitmentRandomness
          let commitment ← (system.commit weights randomness).toRandomized
          let (prompt, output, proof) ← prover commitment randomness
          let accepted ← (system.verify commitment prompt output proof).toRandomized
          pure (prompt, output, accepted))
        {(prompt, output, accepted) | accepted = true ∧ ¬ claim weights prompt output}
        ≤ ε committerQueries proverQueries

/-- Soundness after an honest commitment: the claim is that the output tokens are the model's. -/
def SoundAfterHonestCommitment (system : ArgumentSystem) (ε : ℕ → ℕ → ℝ≥0∞) : Prop :=
  SoundAfterHonestCommitmentFor system system.IsModelOutput ε

/-! ## Zero-knowledge on a stated set of requests

`ZeroKnowledgeOn system domain ζ` is the text of `ZeroKnowledge system ζ` with one more condition on
the requests for which the verifier obtains proofs: they meet `domain`.
`domain` may depend on the weights. Then whether a request meets it is not hidden: the chooser
(`chooser`: `realSteps`, VerifiableInference/Statements.lean), which knows the weights, is the same
in both experiments. Outside `domain` nothing is said about what the honest prover's output shows.
-/

/-- Zero-knowledge on a stated set of requests. As `ZeroKnowledge`, for verifiers that obtain proofs
only for prompts and output tokens that meet `domain` at the weights and whose output tokens are the
model's; each is picked from the verifier's view so far by a chooser, which may know the weights and
is the same in both experiments.
There is one simulator, which is given the public parameters of the weights, the largest number of
proofs, each query of the verifier to the hash function, which it answers in the hash function's
place, and, for each proof, the prompt and the output tokens. For all weights and every verifier
with at most `queries` queries to the hash function,
which is given the commitment and up to `proofCount` proofs: the statistical distance between its
view with the honest committer and prover and what the simulator produces is at most `ζ queries
proofCount`; and the simulator never answers one query in two ways. -/
def ZeroKnowledgeOn (system : ArgumentSystem) (domain : system.Weights → List Token → List Token →
    Prop) (ζ : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∃ simulator : Simulator system.PublicParameters system.Proof,
    ∀ (weights : system.Weights)
      (chooser : View system.Proof → Option (List Token × List Token)),
      (∀ view prompt output, chooser view = some (prompt, output) → domain weights prompt output ∧
          system.IsModelOutput weights prompt output) →
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

/-- `ZeroKnowledge` is `ZeroKnowledgeOn` with no condition. -/
theorem zeroKnowledge_iff_zeroKnowledgeOn (system : ArgumentSystem) (ζ : ℕ → ℕ → ℝ≥0∞) :
    ZeroKnowledge system ζ ↔ ZeroKnowledgeOn system (fun _ _ _ => True) ζ :=
  ⟨fun ⟨simulator, h⟩ => ⟨simulator, fun weights chooser hChooser => h weights chooser fun view
      prompt output hc => (hChooser view prompt output hc).2⟩,
   fun ⟨simulator, h⟩ => ⟨simulator, fun weights chooser hChooser => h weights chooser fun view
       prompt output hc => ⟨trivial, hChooser view prompt output hc⟩⟩⟩

/-! ## The commitment binds to the extractor's weights

The second clause of `SoundAndBinding` (Statements.lean), for a given extractor. `BindsWith`: an
opener of the committer's commitment opens it to the extractor's weights. -/

/-- The commitment binds to the extractor's weights, for a given extractor. For every committer with
at most `committerQueries` queries to the hash function and every opener with at most
`proverQueries` queries: the probability that the opener returns weights and randomness whose
commitment is the committer's, while the extractor does not give these weights from the committer's
commitment and queries, is at most ε (committerQueries + proverQueries). The committer passes its
state to the opener, so the two may act as one adversary. -/
def BindsWith (system : ArgumentSystem)
    (extractor : Commitment → QueryLog → Option system.Weights) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (committerQueries proverQueries : ℕ) (State : Type)
    (committer : RandomizedAlgorithm (Commitment × State)),
    committer.QueryBound committerQueries →
    ∀ opener : State → RandomizedAlgorithm (system.Weights × system.CommitmentRandomness),
      (∀ state, (opener state).QueryBound proverQueries) →
      Prob (do
          let ((commitment, state), queryLog) ← committer.withQueryLog
          let (weights, randomness) ← opener state
          let recomputed ← (system.commit weights randomness).toRandomized
          pure (extractor commitment queryLog, commitment, weights, recomputed))
        {(extracted, commitment, weights, recomputed) |
          recomputed = commitment ∧ extracted ≠ some weights}
        ≤ ε (committerQueries + proverQueries)

/-! ## Nobody opens one commitment to two different weights

To open a commitment is to name weights and randomness from which the argument system's committer,
run again, computes that commitment.
The committer's two runs are not among the adversary's queries: a bound ε has to cover them. Nothing
is said of two openings with the same weights and different randomness. This statement is not among
those of VerifiableInference/Statements.lean. -/

/-- Nobody opens one commitment to two different weights. For every adversary with at most `queries`
queries to the hash function that outputs a commitment and two pairs of weights and randomness: the
probability that the committer computes the commitment from both, and that the two weights differ,
is at most ε queries. -/
def NoTwoOpenings (system : ArgumentSystem) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (queries : ℕ)
    (adversary : RandomizedAlgorithm (Commitment ×
      (system.Weights × system.CommitmentRandomness) ×
      (system.Weights × system.CommitmentRandomness))),
    adversary.QueryBound queries →
    Prob (do
        let (commitment, first, second) ← adversary
        let recomputed₁ ← (system.commit first.1 first.2).toRandomized
        let recomputed₂ ← (system.commit second.1 second.2).toRandomized
        pure (commitment, first.1, second.1, recomputed₁, recomputed₂))
      {(commitment, weights₁, weights₂, recomputed₁, recomputed₂) |
        recomputed₁ = commitment ∧ recomputed₂ = commitment ∧ weights₁ ≠ weights₂}
      ≤ ε queries

/-! ## Soundness for several proofs under one commitment

Soundness for several proofs under one commitment: the statement `Sound` of
VerifiableInference/Statements.lean, with a list of proofs in the place of one proof.
Proved from `Sound` and a bound on the verifier's queries, for every argument system:
ManyProofs.lean. -/

/-- The verifier on each entry of a list, in order, under one commitment. An entry is a prompt,
output tokens and a proof. The result has, for each entry, the prompt, the output tokens and the
verifier's decision. -/
def ArgumentSystem.verifyEach (system : ArgumentSystem) (commitment : Commitment) :
    List (List Token × List Token × system.Proof) →
      RandomizedAlgorithm (List (List Token × List Token × Bool))
  | [] => pure []
  | (prompt, output, proof) :: rest => do
      let accepted ← (system.verify commitment prompt output proof).toRandomized
      let others ← system.verifyEach commitment rest
      pure ((prompt, output, accepted) :: others)

/-- Soundness for several proofs under one commitment. There is one extractor such that, for every
number `proofCount`, every committer with at most `committerQueries` queries to the hash function
and every prover with at most `proverQueries` queries, which sends a list of entries (a prompt,
output tokens and a proof each): the probability that the verifier accepts, among the first
`proofCount` entries, one whose output tokens are not those of the model with the weights that the
extractor gives, from the committer's commitment and queries, is at most
ε (committerQueries + proverQueries) proofCount.
The extractor is fixed before `proofCount` and the adversary, and gives one result for the whole
list. If it gives no weights, every accepted proof counts as a failure. The committer passes its
state to the prover, so the two may act as one adversary. `proverQueries` bounds the prover's
queries for the whole list, whatever state it is given. The prover sends the list at once; it sees
no decision of the verifier before it sends the list. Entries after the first `proofCount` are not
checked. -/
def SoundManyProofs (system : ArgumentSystem) (ε : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∃ extractor : Commitment → QueryLog → Option system.Weights,
    ∀ (committerQueries proverQueries proofCount : ℕ) (State : Type)
      (committer : RandomizedAlgorithm (Commitment × State)),
      committer.QueryBound committerQueries →
      ∀ prover : State → RandomizedAlgorithm (List (List Token × List Token × system.Proof)),
        (∀ state, (prover state).QueryBound proverQueries) →
        Prob (do
            let ((commitment, state), queryLog) ← committer.withQueryLog
            let sent ← prover state
            let checked ← system.verifyEach commitment (sent.take proofCount)
            pure (extractor commitment queryLog, checked))
          {(extracted, checked) |
            ∃ prompt output, (prompt, output, true) ∈ checked ∧
              ¬ ∃ weights, extracted = some weights ∧ system.IsModelOutput weights prompt output}
          ≤ ε (committerQueries + proverQueries) proofCount

/-- `SoundManyProofs` for a given extractor, and for any claim on weights, a prompt and output
tokens in the place of "the output tokens are the model's": `SoundForWith`,
with a list of proofs in the place of one proof. -/
def SoundForManyProofsWith (system : ArgumentSystem)
    (extractor : Commitment → QueryLog → Option system.Weights)
    (claim : system.Weights → List Token → List Token → Prop) (ε : ℕ → ℕ → ℝ≥0∞) : Prop :=
    ∀ (committerQueries proverQueries proofCount : ℕ) (State : Type)
      (committer : RandomizedAlgorithm (Commitment × State)),
      committer.QueryBound committerQueries →
      ∀ prover : State → RandomizedAlgorithm (List (List Token × List Token × system.Proof)),
        (∀ state, (prover state).QueryBound proverQueries) →
        Prob (do
            let ((commitment, state), queryLog) ← committer.withQueryLog
            let sent ← prover state
            let checked ← system.verifyEach commitment (sent.take proofCount)
            pure (extractor commitment queryLog, checked))
          {(extracted, checked) |
            ∃ prompt output, (prompt, output, true) ∈ checked ∧
              ¬ ∃ weights, extracted = some weights ∧ claim weights prompt output}
          ≤ ε (committerQueries + proverQueries) proofCount

/-- `SoundManyProofs` says that some extractor meets `SoundForManyProofsWith` for the claim that the
output tokens are the model's. -/
theorem soundManyProofs_iff (system : ArgumentSystem) (ε : ℕ → ℕ → ℝ≥0∞) :
    SoundManyProofs system ε ↔
      ∃ extractor, SoundForManyProofsWith system extractor system.IsModelOutput ε := Iff.rfl

/-! ## Soundness with several commitments

Soundness when one committer publishes several commitments: the statement `Sound` of
VerifiableInference/Statements.lean, with a list of commitments in the place of one commitment.
Proved from `Sound` for every argument system: SeveralCommitments.lean. -/

/-- Soundness with several commitments. There is one extractor such that, for every number
`commitmentCount`, every committer that returns a list of commitments after at most
`committerQueries` queries to the hash function, and every prover that returns one commitment, a
prompt, output tokens and a proof after at most `proverQueries` queries: the probability that this
commitment is among the first `commitmentCount` of the committer's list, the verifier accepts under
it, and the output tokens are not those of the model with the weights that the extractor gives, from
this commitment and the committer's queries, is at most
ε (committerQueries + proverQueries) commitmentCount.
The extractor is fixed before `commitmentCount` and the adversary. It is given one commitment and
the query log of the committer's whole run; it is not told the other commitments. If it gives no
weights, every proof accepted under one of the first `commitmentCount` commitments counts as a
failure. The committer passes its state to the prover, so
the two may act as one adversary. The prover chooses the commitment after its queries.
`proverQueries` bounds the prover's queries at every state. A commitment that is not among the first
`commitmentCount` of the list is not in the event, and nothing is said about it. -/
def SoundSeveralCommitments (system : ArgumentSystem) (ε : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∃ extractor : Commitment → QueryLog → Option system.Weights,
    ∀ (committerQueries proverQueries commitmentCount : ℕ) (State : Type)
      (committer : RandomizedAlgorithm (List Commitment × State)),
      committer.QueryBound committerQueries →
      ∀ prover : State → RandomizedAlgorithm
          (Commitment × List Token × List Token × system.Proof),
        (∀ state, (prover state).QueryBound proverQueries) →
        Prob (do
            let ((commitments, state), queryLog) ← committer.withQueryLog
            let (commitment, prompt, output, proof) ← prover state
            let accepted ← (system.verify commitment prompt output proof).toRandomized
            pure (commitments.take commitmentCount, commitment, extractor commitment queryLog,
              prompt, output, accepted))
          {(commitments, commitment, extracted, prompt, output, accepted) |
            accepted = true ∧ commitment ∈ commitments ∧
            ¬ ∃ weights, extracted = some weights ∧ system.IsModelOutput weights prompt output}
          ≤ ε (committerQueries + proverQueries) commitmentCount

/-- `SoundSeveralCommitments` for a given extractor, and for any claim on weights, a prompt and
output tokens in the place of "the output tokens are the model's": `SoundForWith`,
with a list of commitments in the place of one commitment. -/
def SoundForSeveralCommitmentsWith (system : ArgumentSystem)
    (extractor : Commitment → QueryLog → Option system.Weights)
    (claim : system.Weights → List Token → List Token → Prop) (ε : ℕ → ℕ → ℝ≥0∞) : Prop :=
    ∀ (committerQueries proverQueries commitmentCount : ℕ) (State : Type)
      (committer : RandomizedAlgorithm (List Commitment × State)),
      committer.QueryBound committerQueries →
      ∀ prover : State → RandomizedAlgorithm
          (Commitment × List Token × List Token × system.Proof),
        (∀ state, (prover state).QueryBound proverQueries) →
        Prob (do
            let ((commitments, state), queryLog) ← committer.withQueryLog
            let (commitment, prompt, output, proof) ← prover state
            let accepted ← (system.verify commitment prompt output proof).toRandomized
            pure (commitments.take commitmentCount, commitment, extractor commitment queryLog,
              prompt, output, accepted))
          {(commitments, commitment, extracted, prompt, output, accepted) |
            accepted = true ∧ commitment ∈ commitments ∧
            ¬ ∃ weights, extracted = some weights ∧ claim weights prompt output}
          ≤ ε (committerQueries + proverQueries) commitmentCount

/-- `SoundSeveralCommitments` says that some extractor meets `SoundForSeveralCommitmentsWith` for
the claim that the output tokens are the model's. -/
theorem soundSeveralCommitments_iff (system : ArgumentSystem) (ε : ℕ → ℕ → ℝ≥0∞) :
    SoundSeveralCommitments system ε ↔
      ∃ extractor, SoundForSeveralCommitmentsWith system extractor system.IsModelOutput ε := Iff.rfl

/-! ## The three together, two of them on a stated set of requests -/

/-- The three statements together, two of them on a stated set of requests. `sound`:
`SoundAndBinding`, which asks more than `Sound`, for every prompt and output. `complete` and
`zeroKnowledge`: as `Complete` and `ZeroKnowledge`, for the requests that meet `domain` and whose
output tokens are the model's. A smaller `domain` asks less: at weights at which no request meets
it, `complete` says nothing and `zeroKnowledge` speaks of the commitment alone. `domain` may depend
on the weights. Then whether a request meets it is not hidden (see `ZeroKnowledgeOn`). With no
condition on the requests it gives `CompleteSoundZeroKnowledge`
(`CompleteSoundZeroKnowledgeOn.toCompleteSoundZeroKnowledge`,
VerifiableInference/TogetherOn.lean), which this library proves of no system. -/
structure CompleteSoundZeroKnowledgeOn (system : ArgumentSystem)
    (domain : system.Weights → List Token → List Token → Prop) (α : ℝ≥0∞) (ε : ℕ → ℝ≥0∞)
    (ζ : ℕ → ℕ → ℝ≥0∞) : Prop where
  sound : SoundAndBinding system ε
  complete : CompleteOn system domain α
  zeroKnowledge : ZeroKnowledgeOn system domain ζ

end VerifiableInference

#print axioms VerifiableInference.sound_iff_soundFor
#print axioms VerifiableInference.zeroKnowledge_iff_zeroKnowledgeOn
#print axioms VerifiableInference.soundManyProofs_iff
#print axioms VerifiableInference.soundSeveralCommitments_iff
