-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/MapWeightsBinding.lean

For every argument system: binding carries over to a system with another type of weights
(`ArgumentSystem.withWeights`, MapWeights.lean).
`BindsWith.mapWeights`: for a map from the old weights to the new ones and a map `back`, if the new
honest committer is the old one at `back weights` and `map (back weights) = weights`.
`SoundAndBinding.mapWeights`: the same for `SoundAndBinding` (Statements.lean), if the map also
preserves "the output tokens are the model's".
Nothing here is about a particular proof system.
-/
import VerifiableInference.MapWeights
import VerifiableInference.Binds

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

namespace VerifiableInference

open RandomizedAlgorithm

/-- Binding for a given extractor carries over. The new extractor is the old one followed by the
map. An opener of the new system, followed by `back`, is an opener of the old one with the same
queries and the same commitment; if the old extractor gives `back weights`, the new one gives
`weights`. -/
theorem BindsWith.mapWeights (system : ArgumentSystem)
    (extractor : Commitment → QueryLog → Option system.Weights) (ε : ℕ → ℝ≥0∞)
    (binds : BindsWith system extractor ε)
    (NewWeights NewPublicParameters : Type) (publicParameters : NewWeights → NewPublicParameters)
    (nextToken : NewWeights → List Token → Option Token)
    (map : system.Weights → NewWeights) (back : NewWeights → system.Weights)
    (hBack : ∀ weights, map (back weights) = weights) :
    BindsWith
      (system.withWeights NewWeights NewPublicParameters publicParameters nextToken
        (fun weights => system.commit (back weights)) (fun weights => system.prove (back weights)))
      (fun commitment queryLog => (extractor commitment queryLog).map map) ε := by
  intro committerQueries proverQueries State committer committerBound opener openerBound
  refine le_trans ?_ (binds committerQueries proverQueries State committer committerBound
    (fun state => (opener state).bind fun y => RandomizedAlgorithm.done (back y.1, y.2))
    (fun state => queryBound_map (fun y : NewWeights × system.CommitmentRandomness =>
      (back y.1, y.2)) (opener state) proverQueries (openerBound state)))
  unfold Prob
  refine lintegral_mono fun hash => ?_
  show ZKCP.prob ((committer.withQueryLog.bind fun c => (opener c.1.2).bind fun y =>
        (system.commit (back y.1) y.2).toRandomized.bind fun recomputed =>
          RandomizedAlgorithm.done
            ((extractor c.1.1 c.2).map map, c.1.1, y.1, recomputed)).run hash) _
    ≤ ZKCP.prob ((committer.withQueryLog.bind fun c =>
        ((opener c.1.2).bind fun y => RandomizedAlgorithm.done (back y.1, y.2)).bind fun z =>
          (system.commit z.1 z.2).toRandomized.bind fun recomputed =>
            RandomizedAlgorithm.done (extractor c.1.1 c.2, c.1.1, z.1, recomputed)).run hash) _
  rw [run_bind, run_bind, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun c => ?_
  rw [run_bind, run_bind, run_bind, PMF.bind_bind, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun y => ?_
  rw [run_done, PMF.pure_bind]
  show ZKCP.prob (((system.commit (back y.1) y.2).toRandomized.bind fun recomputed =>
        RandomizedAlgorithm.done
          ((extractor c.1.1 c.2).map map, c.1.1, y.1, recomputed)).run hash) _
    ≤ ZKCP.prob (((system.commit (back y.1) y.2).toRandomized.bind fun recomputed =>
        RandomizedAlgorithm.done (extractor c.1.1 c.2, c.1.1, back y.1, recomputed)).run hash) _
  rw [run_bind, run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, PMF.pure_bind,
    run_done, run_done, ZKCP.prob_pure, ZKCP.prob_pure]
  refine ind_le fun hb => ?_
  obtain ⟨h1, h2⟩ := hb
  refine ⟨h1, fun he => h2 ?_⟩
  show (extractor c.1.1 c.2).map map = some y.1
  rw [he]
  exact congrArg some (hBack y.1)

/-- `SoundAndBinding` carries over, if the map preserves "the output tokens are the model's", the
new honest committer and prover are the old ones at `back weights`, and
`map (back weights) = weights` for all new weights. -/
theorem SoundAndBinding.mapWeights (system : ArgumentSystem) (ε : ℕ → ℝ≥0∞)
    (sound : SoundAndBinding system ε)
    (NewWeights NewPublicParameters : Type) (publicParameters : NewWeights → NewPublicParameters)
    (nextToken : NewWeights → List Token → Option Token)
    (map : system.Weights → NewWeights) (back : NewWeights → system.Weights)
    (hBack : ∀ weights, map (back weights) = weights)
    (carries : ∀ (weights : system.Weights) (prompt output : List Token),
      system.IsModelOutput weights prompt output →
      (system.withWeights NewWeights NewPublicParameters publicParameters nextToken
        (fun weights => system.commit (back weights))
        (fun weights => system.prove (back weights))).IsModelOutput (map weights) prompt output) :
    SoundAndBinding
      (system.withWeights NewWeights NewPublicParameters publicParameters nextToken
        (fun weights => system.commit (back weights)) (fun weights => system.prove (back weights)))
      ε := by
  obtain ⟨extractor, soundWith, binds⟩ := (soundAndBinding_iff system ε).1 sound
  exact (soundAndBinding_iff _ ε).2 ⟨_,
    SoundForWith.mapWeights system extractor system.IsModelOutput ε soundWith NewWeights
      NewPublicParameters publicParameters nextToken (fun weights => system.commit (back weights))
      (fun weights => system.prove (back weights)) map _ carries,
    BindsWith.mapWeights system extractor ε binds NewWeights NewPublicParameters publicParameters
      nextToken map back hBack⟩

end VerifiableInference

#print axioms VerifiableInference.BindsWith.mapWeights
#print axioms VerifiableInference.SoundAndBinding.mapWeights
