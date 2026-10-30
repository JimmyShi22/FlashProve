-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/MapWeights.lean

For every argument system: three statements carry over to a system with another type of weights and
another model function, and the same proofs and verifier (`ArgumentSystem.withWeights`).
`SoundForWith.mapWeights`, `SoundFor.mapWeights`, `Sound.mapWeights`: along a map from the old
weights to the new ones that preserves the claim.
`CompleteOn.mapWeights`: along a map `back` from the new weights to the old ones, on the three
conditions of its statement.
`ExtractsCommittedWeights.mapWeights`: for both maps, if the new honest committer is the old one at
`back weights` and `map (back weights) = weights`.
-/
import VerifiableInference.Bridge
import VerifiableInference.Steps
import VerifiableInference.MoreStatements

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

namespace VerifiableInference

open RandomizedAlgorithm

/-- The same proofs, verifier and committer's randomness, with another type of weights: its model
function, public parameters, honest committer and honest prover. -/
def ArgumentSystem.withWeights (system : ArgumentSystem) (NewWeights NewPublicParameters : Type)
    (publicParameters : NewWeights → NewPublicParameters)
    (nextToken : NewWeights → List Token → Option Token)
        (commit : NewWeights → system.CommitmentRandomness → DeterministicAlgorithm Commitment)
    (prove : NewWeights → system.CommitmentRandomness → List Token → List Token →
        RandomizedAlgorithm system.Proof) : ArgumentSystem where
  Weights := NewWeights
  PublicParameters := NewPublicParameters
  publicParameters := publicParameters
  CommitmentRandomness := system.CommitmentRandomness
  Proof := system.Proof
  nextToken := nextToken
  sampleCommitmentRandomness := system.sampleCommitmentRandomness
  commit := commit
  prove := prove
  verify := system.verify

/-- Soundness for a claim, for a given extractor, carries over along a map of weights that preserves
the claim. The new extractor is the old one followed by the map. -/
theorem SoundForWith.mapWeights (system : ArgumentSystem)
    (extractor : Commitment → QueryLog → Option system.Weights)
    (claim : system.Weights → List Token → List Token → Prop) (ε : ℕ → ℝ≥0∞)
        (sound : SoundForWith system extractor claim ε)
    (NewWeights NewPublicParameters : Type) (publicParameters : NewWeights → NewPublicParameters)
    (nextToken : NewWeights → List Token → Option Token)
        (commit : NewWeights → system.CommitmentRandomness → DeterministicAlgorithm Commitment)
    (prove : NewWeights → system.CommitmentRandomness → List Token → List Token →
        RandomizedAlgorithm system.Proof)
    (map : system.Weights → NewWeights) (newClaim : NewWeights → List Token → List Token → Prop)
    (carries : ∀ (weights : system.Weights) (prompt output : List Token), claim weights prompt
        output → newClaim (map weights) prompt output) :
    SoundForWith (system.withWeights NewWeights NewPublicParameters publicParameters nextToken
        commit prove)
      (fun commitment queryLog => (extractor commitment queryLog).map map) newClaim ε := by
  intro committerQueries proverQueries State committer committerBound prover proverBound
  refine le_trans ?_ (sound committerQueries proverQueries State committer committerBound prover
      proverBound)
  unfold Prob
  refine lintegral_mono fun hash => ?_
  show ZKCP.prob ((committer.withQueryLog.bind fun c => (prover c.1.2).bind fun y =>
        (system.verify c.1.1 y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done ((extractor c.1.1 c.2).map map, y.1, y.2.1, accepted)).run hash)
              _
    ≤ ZKCP.prob ((committer.withQueryLog.bind fun c => (prover c.1.2).bind fun y =>
        (system.verify c.1.1 y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (extractor c.1.1 c.2, y.1, y.2.1, accepted)).run hash) _
  rw [run_bind, run_bind, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun c => ?_
  rw [run_bind, run_bind, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun y => ?_
  rw [run_bind, run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, PMF.pure_bind,
      run_done, run_done, ZKCP.prob_pure, ZKCP.prob_pure]
  refine ind_le fun hb => ?_
  obtain ⟨h1, h2⟩ := hb
  refine ⟨h1, fun hw => h2 ?_⟩
  obtain ⟨weights, he, ho⟩ := hw
  exact ⟨map weights, by rw [he]; rfl, carries weights _ _ ho⟩

/-- Soundness for a claim carries over along a map of weights that preserves the claim. -/
theorem SoundFor.mapWeights (system : ArgumentSystem) (claim : system.Weights → List Token → List
    Token → Prop) (ε : ℕ → ℝ≥0∞) (sound : SoundFor system claim ε)
    (NewWeights NewPublicParameters : Type) (publicParameters : NewWeights → NewPublicParameters)
    (nextToken : NewWeights → List Token → Option Token)
        (commit : NewWeights → system.CommitmentRandomness → DeterministicAlgorithm Commitment)
    (prove : NewWeights → system.CommitmentRandomness → List Token → List Token →
        RandomizedAlgorithm system.Proof)
    (map : system.Weights → NewWeights) (newClaim : NewWeights → List Token → List Token → Prop)
    (carries : ∀ (weights : system.Weights) (prompt output : List Token), claim weights prompt
        output → newClaim (map weights) prompt output) :
    SoundFor (system.withWeights NewWeights NewPublicParameters publicParameters nextToken commit
        prove) newClaim ε := by
  obtain ⟨extractor, soundWith⟩ := sound
  exact ⟨_, SoundForWith.mapWeights system extractor claim ε soundWith NewWeights
      NewPublicParameters publicParameters nextToken commit prove map newClaim carries⟩

/-- `Sound` carries over along a map of weights that preserves "the output tokens are the model's".
-/
theorem Sound.mapWeights (system : ArgumentSystem) (ε : ℕ → ℝ≥0∞) (sound : Sound system ε)
    (NewWeights NewPublicParameters : Type) (publicParameters : NewWeights → NewPublicParameters)
    (nextToken : NewWeights → List Token → Option Token)
        (commit : NewWeights → system.CommitmentRandomness → DeterministicAlgorithm Commitment)
    (prove : NewWeights → system.CommitmentRandomness → List Token → List Token →
        RandomizedAlgorithm system.Proof)
    (map : system.Weights → NewWeights)
    (carries : ∀ (weights : system.Weights) (prompt output : List Token), system.IsModelOutput
        weights prompt output →
      (system.withWeights NewWeights NewPublicParameters publicParameters nextToken commit
          prove).IsModelOutput (map weights) prompt output) :
    Sound (system.withWeights NewWeights NewPublicParameters publicParameters nextToken commit
        prove) ε :=
  SoundFor.mapWeights system system.IsModelOutput ε sound NewWeights NewPublicParameters
      publicParameters nextToken commit prove map _ carries

/-- `CompleteOn` carries over along a map `back` from new weights to old ones, on three conditions.
The new honest committer and prover are the old ones at `back weights`. The new domain implies the
old one at `back weights`. On the new domain, "the output tokens are the model's" for the new model
function implies the same for the old one at `back weights`. -/
theorem CompleteOn.mapWeights (system : ArgumentSystem) (domain : system.Weights → List Token → List
    Token → Prop) (α : ℝ≥0∞) (complete : CompleteOn system domain α)
    (NewWeights NewPublicParameters : Type) (publicParameters : NewWeights → NewPublicParameters)
    (nextToken : NewWeights → List Token → Option Token) (back : NewWeights → system.Weights)
    (newDomain : NewWeights → List Token → List Token → Prop)
    (hDomain : ∀ (weights : NewWeights) (prompt output : List Token), newDomain weights prompt
        output → domain (back weights) prompt output)
    (hOutput : ∀ (weights : NewWeights) (prompt output : List Token), newDomain weights prompt
        output →
      (∀ position (h : position < output.length), nextToken weights (prompt ++ output.take position)
          = some output[position]) →
      system.IsModelOutput (back weights) prompt output) :
    CompleteOn (system.withWeights NewWeights NewPublicParameters publicParameters nextToken
        (fun weights => system.commit (back weights)) (fun weights => system.prove (back weights)))
      newDomain α :=
  fun weights prompt output hD hO => complete (back weights) prompt output
      (hDomain weights prompt output hD) (hOutput weights prompt output hD hO)

/-- "The extractor returns the honest committer's weights" carries over, if the new honest committer
is the old one at `back weights` and `map (back weights) = weights` for all new weights. The new
extractor is the old one followed by the map. -/
theorem ExtractsCommittedWeights.mapWeights (system : ArgumentSystem)
    (extractor : Commitment → QueryLog → Option system.Weights) (α : ℝ≥0∞)
    (extracts : ExtractsCommittedWeights system extractor α)
    (NewWeights NewPublicParameters : Type) (publicParameters : NewWeights → NewPublicParameters)
        (nextToken : NewWeights → List Token → Option Token)
    (map : system.Weights → NewWeights) (back : NewWeights → system.Weights)
        (hBack : ∀ weights, map (back weights) = weights) :
    ExtractsCommittedWeights
      (system.withWeights NewWeights NewPublicParameters publicParameters nextToken
          (fun weights => system.commit (back weights)) (fun weights => system.prove
          (back weights)))
      (fun commitment queryLog => (extractor commitment queryLog).map map) α := by
  intro weights
  refine le_trans ?_ (extracts (back weights))
  unfold Prob
  refine lintegral_mono fun hash => ?_
  show ZKCP.prob (((system.sampleCommitmentRandomness.bind fun randomness =>
      (system.commit (back weights) randomness).toRandomized).withQueryLog.bind fun c =>
        RandomizedAlgorithm.done ((extractor c.1 c.2).map map)).run hash) _
    ≤ ZKCP.prob (((system.sampleCommitmentRandomness.bind fun randomness =>
        (system.commit (back weights) randomness).toRandomized).withQueryLog.bind fun c =>
        RandomizedAlgorithm.done (extractor c.1 c.2)).run hash) _
  rw [run_bind, run_bind, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun c => ?_
  rw [run_done, run_done, ZKCP.prob_pure, ZKCP.prob_pure]
  refine ind_le fun hb he => hb ?_
  show (extractor c.1 c.2).map map = some weights
  rw [he]
  exact congrArg some (hBack weights)

end VerifiableInference

#print axioms VerifiableInference.SoundForWith.mapWeights
#print axioms VerifiableInference.SoundFor.mapWeights
#print axioms VerifiableInference.Sound.mapWeights
#print axioms VerifiableInference.CompleteOn.mapWeights
#print axioms VerifiableInference.ExtractsCommittedWeights.mapWeights
