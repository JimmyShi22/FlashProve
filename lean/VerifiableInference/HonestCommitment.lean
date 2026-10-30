-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/HonestCommitment.lean

Soundness after an honest commitment, for every argument system.
`SoundForWith.afterHonestCommitment`: if soundness for a claim holds with the bound ε, with an
extractor that gives back the honest committer's weights but for probability α (`SoundForWith`,
VerifiableInference/MoreStatements.lean; `ExtractsCommittedWeights`,
VerifiableInference/MoreStatements.lean), then after an honest commitment to given weights, the
probability that the verifier accepts an output that does not meet the claim for these weights is at
most ε (committerQueries + proverQueries) + α, for every prover with at most `proverQueries`
queries, if the honest committer makes at most `committerQueries`. No extractor is in the
conclusion. The prover is given the commitment and the committer's randomness. One commitment, one
proof.
-/
import VerifiableInference.MoreStatements
import VerifiableInference.Bridge

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

namespace VerifiableInference

open RandomizedAlgorithm

variable {ρ γ δ : Type}

/-- Keeping the first result beside the second keeps every bound on the number of queries. -/
theorem queryBound_bind_map (g : ρ → γ → δ) (next : ρ → RandomizedAlgorithm γ) :
    ∀ (first : RandomizedAlgorithm ρ) (queries : ℕ), (first.bind next).QueryBound queries →
      (first.bind fun r => (next r).bind fun c => .done (g r c)).QueryBound queries
  | .done r, queries, h => queryBound_map (g r) (next r) queries h
  | .query _ _, 0, h => h.elim
  | .query _ k, queries + 1, h
      => fun answer => queryBound_bind_map g next (k answer) queries (h answer)
  | .sample _ k, queries, h => fun draw => queryBound_bind_map g next (k draw) queries (h draw)

/-- Under every hash function, keeping the first result beside the second gives the same
distribution of the second result, read back by `f` (`hf`), with the query log. -/
theorem run_withQueryLog_bind_map (g : ρ → γ → δ) (f : δ → γ) (hf : ∀ r c, f (g r c) = c)
    (next : ρ → RandomizedAlgorithm γ) (hash : Hash) :
    ∀ first : RandomizedAlgorithm ρ,
      (first.bind next).withQueryLog.run hash
        = ((first.bind fun r => (next r).bind fun c => .done (g r c)).withQueryLog.run hash).bind
            fun out => PMF.pure (f out.1, out.2)
  | .done r => by
      show (next r).withQueryLog.run hash = (((next r).bind fun c => RandomizedAlgorithm.done
          (g r c)).withQueryLog.run hash).bind _
      rw [run_withQueryLog_map (g r) hash (next r), PMF.bind_bind]
      simp only [PMF.pure_bind, hf]
      exact (PMF.bind_pure _).symm
  | .query input k => by
      show ((((k (hash input)).bind next).withQueryLog).bind fun rest =>
          RandomizedAlgorithm.done (rest.1, (input, hash input) :: rest.2)).run hash
        = (((((k (hash input)).bind fun r => (next r).bind fun c => RandomizedAlgorithm.done
            (g r c)).withQueryLog).bind fun rest =>
          RandomizedAlgorithm.done (rest.1, (input, hash input) :: rest.2)).run hash).bind _
      rw [run_bind, run_bind, run_withQueryLog_bind_map g f hf next hash (k (hash input)),
          PMF.bind_bind, PMF.bind_bind]
      refine congrArg _ (funext fun out => ?_)
      rw [PMF.pure_bind, run_done, run_done, PMF.pure_bind]
  | .sample bound k => by
      show (PMF.uniformOfFintype (Fin (bound + 1))).bind
          (fun draw => ((k draw).bind next).withQueryLog.run hash)
        = ((PMF.uniformOfFintype (Fin (bound + 1))).bind fun draw =>
            ((k draw).bind fun r => (next r).bind fun c => RandomizedAlgorithm.done
                (g r c)).withQueryLog.run hash).bind _
      rw [PMF.bind_bind]
      exact congrArg _ (funext fun draw => run_withQueryLog_bind_map g f hf next hash (k draw))

/-- The honest committer, returning the commitment and, as its state, the commitment and its
randomness. -/
def honestCommitterWithState (system : ArgumentSystem) (weights : system.Weights) :
    RandomizedAlgorithm (Commitment × (Commitment × system.CommitmentRandomness)) :=
  system.sampleCommitmentRandomness.bind fun randomness =>
    (system.commit weights randomness).toRandomized.bind fun commitment => .done
        (commitment, (commitment, randomness))

/-- Soundness after an honest commitment. Let soundness for `claim` hold with the bound ε for an
extractor that gives back the honest committer's weights except with probability at most α. Fix
weights. Let the honest committer make at most `committerQueries` queries, and let the prover, which
is given the commitment and the committer's randomness, make at most `proverQueries` queries.
The probability that the verifier accepts while the claim does not hold for these weights, the
prompt and the output tokens is at most ε (committerQueries + proverQueries) + α. It is a joint
probability, not a conditional one. -/
theorem SoundForWith.afterHonestCommitment (system : ArgumentSystem)
    (extractor : Commitment → QueryLog → Option system.Weights)
    (claim : system.Weights → List Token → List Token → Prop) (ε : ℕ → ℝ≥0∞) (α : ℝ≥0∞)
    (sound : SoundForWith system extractor claim ε)
        (extracts : ExtractsCommittedWeights system extractor α)
    (weights : system.Weights) (committerQueries proverQueries : ℕ)
    (committerBound : (system.sampleCommitmentRandomness.bind fun randomness =>
      (system.commit weights randomness).toRandomized).QueryBound committerQueries)
    (prover : Commitment → system.CommitmentRandomness → RandomizedAlgorithm
        (List Token × List Token × system.Proof))
    (proverBound : ∀ commitment randomness, (prover commitment randomness).QueryBound proverQueries)
        :
    Prob (do
        let randomness ← system.sampleCommitmentRandomness
        let commitment ← (system.commit weights randomness).toRandomized
        let (prompt, output, proof) ← prover commitment randomness
        let accepted ← (system.verify commitment prompt output proof).toRandomized
        pure (prompt, output, accepted))
      {(prompt, output, accepted) | accepted = true ∧ ¬ claim weights prompt output}
      ≤ ε (committerQueries + proverQueries) + α := by
  have hA : (honestCommitterWithState system weights).QueryBound committerQueries :=
    queryBound_bind_map (fun randomness commitment => (commitment, (commitment, randomness))) _ _ _
        committerBound
  have hS := sound committerQueries proverQueries _ (honestCommitterWithState system weights) hA
    (fun state => prover state.1 state.2) (fun state => proverBound state.1 state.2)
  refine le_trans ?_ (add_le_add hS (extracts weights))
  unfold Prob
  refine le_trans ?_ (le_of_eq (lintegral_add_left (measurable_eventProbability_run _ _) _))
  refine lintegral_mono fun hash => ?_
  show ZKCP.prob ((system.sampleCommitmentRandomness.bind fun randomness =>
      (system.commit weights randomness).toRandomized.bind fun commitment =>
        (prover commitment randomness).bind fun y =>
            (system.verify commitment y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (y.1, y.2.1, accepted)).run hash)
        {o : List Token × List Token × Bool | o.2.2 = true ∧ ¬ claim weights o.1 o.2.1}
    ≤ ZKCP.prob (((honestCommitterWithState system weights).withQueryLog.bind fun c =>
        (prover c.1.2.1 c.1.2.2).bind fun y =>
        (system.verify c.1.1 y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (extractor c.1.1 c.2, y.1, y.2.1, accepted)).run hash)
        {o : Option system.Weights × List Token × List Token × Bool | o.2.2.2 = true ∧ ¬ ∃ w, o.1 =
            some w ∧ claim w o.2.1 o.2.2.1}
      + ZKCP.prob (((system.sampleCommitmentRandomness.bind fun randomness =>
          (system.commit weights randomness).toRandomized).withQueryLog.bind fun c =>
        RandomizedAlgorithm.done (extractor c.1 c.2)).run hash)
            {extracted | extracted ≠ some weights}
  have eL : (system.sampleCommitmentRandomness.bind fun randomness =>
      (system.commit weights randomness).toRandomized.bind fun commitment =>
        (prover commitment randomness).bind fun y =>
            (system.verify commitment y.1 y.2.1 y.2.2).toRandomized.bind fun accepted =>
          RandomizedAlgorithm.done (y.1, y.2.1, accepted)).run hash
      = ((honestCommitterWithState system weights).withQueryLog.run hash).bind fun out =>
          ((prover out.1.2.1 out.1.2.2).run hash).bind fun y =>
            PMF.pure (y.1, y.2.1, (system.verify out.1.1 y.1 y.2.1 y.2.2).evaluate hash) := by
    refine Eq.trans ?_ (run_withQueryLog_bind_fst hash (honestCommitterWithState system weights)
      (fun s : Commitment × (Commitment × system.CommitmentRandomness) =>
          ((prover s.2.1 s.2.2).run hash).bind fun y =>
        PMF.pure (y.1, y.2.1, (system.verify s.1 y.1 y.2.1 y.2.2).evaluate hash))).symm
    unfold honestCommitterWithState
    simp only [run_bind, run_done, PMF.bind_bind, PMF.pure_bind,
        DeterministicAlgorithm.run_toRandomized]
  have e2 := run_withQueryLog_bind_map (fun (randomness : system.CommitmentRandomness)
      (commitment : Commitment) => (commitment, (commitment, randomness)))
    Prod.fst (fun _ _ => rfl) (fun randomness => (system.commit weights randomness).toRandomized)
        hash system.sampleCommitmentRandomness
  have e2' : (system.sampleCommitmentRandomness.bind fun randomness =>
      (system.commit weights randomness).toRandomized).withQueryLog.run hash
      = ((honestCommitterWithState system weights).withQueryLog.run hash).bind fun out => PMF.pure
          (out.1.1, out.2) := e2
  rw [eL, run_bind, run_bind, e2', PMF.bind_bind, ZKCP.prob_bind, ZKCP.prob_bind, ZKCP.prob_bind, ←
      ZKCP.expect_add]
  refine ZKCP.expect_mono _ fun c => ?_
  beta_reduce
  rw [PMF.pure_bind, run_done, run_bind, ZKCP.prob_bind, ZKCP.prob_bind,
    ← ZKCP.expect_const ((prover c.1.2.1 c.1.2.2).run hash)
        (ZKCP.prob (PMF.pure (extractor c.1.1 c.2)) {extracted | extracted ≠ some weights}),
    ← ZKCP.expect_add]
  refine ZKCP.expect_mono _ fun y => ?_
  beta_reduce
  rw [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_done, ZKCP.prob_pure,
      ZKCP.prob_pure, ZKCP.prob_pure]
  refine ind_le_add fun hb => ?_
  obtain ⟨h1, h2⟩ := hb
  by_cases he : extractor c.1.1 c.2 = some weights
  · refine Or.inl ⟨h1, fun hw => h2 ?_⟩
    obtain ⟨w, e, hc⟩ := hw
    have ew : w = weights := Option.some.inj ((show extractor c.1.1 c.2 = some w from e).symm.trans
        he)
    rw [← ew]
    exact hc
  · exact Or.inr he

end VerifiableInference

#print axioms VerifiableInference.queryBound_bind_map
#print axioms VerifiableInference.run_withQueryLog_bind_map
#print axioms VerifiableInference.SoundForWith.afterHonestCommitment
