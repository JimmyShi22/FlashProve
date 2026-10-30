-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/BindsAtRandomness.lean: binding (`BindsWith`,
VerifiableInference/MoreStatements.lean) is not an empty statement.

`BindsWith.atRandomness`: in every argument system whose commitment binds to the extractor's weights
with the bound ε, the extractor gives back the honest committer's weights at every given randomness,
except with probability ε at that committer's number of queries.
Run the honest committer at given weights and given randomness, and give the extractor the
commitment and the queries of that run. The probability that it does not return these weights is at
most ε at the number of these queries. The probability is over the hash function alone.
Why: that committer, with the opener that hands back the weights and the randomness, is one of the
adversaries of `BindsWith`, and its opening always fits.
So an extractor that never answers does not meet `BindsWith` with a bound that is below 1 at the
honest committer's number of queries.
`ExtractsCommittedWeights` (VerifiableInference/MoreStatements.lean) is the like statement on
average over
the randomness.
-/
import VerifiableInference.Binds
import VerifiableInference.Bridge
import ZKCP.HonestKey

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

namespace VerifiableInference

open RandomizedAlgorithm

/-- A bound on the queries of an algorithm that samples one number and goes on with it holds for
what it does at each number. -/
theorem queryBound_at_sample {β : Type} (n : ℕ) (rest : Fin (n + 1) → RandomizedAlgorithm β)
    (queries : ℕ)
    (h : ((RandomizedAlgorithm.sample n fun number => .done number).bind rest).QueryBound queries)
    (number : Fin (n + 1)) : (rest number).QueryBound queries :=
  h number

/-- From an honest commitment at given weights and given randomness, and the queries of that run,
the extractor returns the weights, except with probability ε at a bound on these queries. -/
theorem BindsWith.atRandomness {system : ArgumentSystem}
    {extractor : Commitment → QueryLog → Option system.Weights} {ε : ℕ → ℝ≥0∞}
    (binds : BindsWith system extractor ε) (weights : system.Weights)
    (randomness : system.CommitmentRandomness) (queries : ℕ)
    (bound : (system.commit weights randomness).toRandomized.QueryBound queries) :
    Prob (system.commit weights randomness).toRandomized.withQueryLog
        {o | extractor o.1 o.2 ≠ some weights}
      ≤ ε queries := by
  classical
  have key := binds queries 0 Unit
    ((system.commit weights randomness).toRandomized.bind fun c => .done (c, ()))
    (queryBound_map _ _ _ bound) (fun _ => .done (weights, randomness)) (fun _ => trivial)
  refine le_trans ?_ key
  unfold Prob
  refine lintegral_mono fun hash => ?_
  show ZKCP.prob ((system.commit weights randomness).toRandomized.withQueryLog.run hash) _
    ≤ ZKCP.prob ((((system.commit weights randomness).toRandomized.bind fun c =>
        RandomizedAlgorithm.done (c, ())).withQueryLog.bind fun c =>
        (system.commit weights randomness).toRandomized.bind fun recomputed =>
          RandomizedAlgorithm.done (extractor c.1.1 c.2, c.1.1, weights, recomputed)).run hash) _
  rw [run_bind, run_withQueryLog_map, PMF.bind_bind, ZKCP.prob_bind, ZKCP.prob_eq_expect]
  refine ZKCP.expect_le_on_support _ fun o ho => ?_
  have h1 : o.1 = (system.commit weights randomness).evaluate hash := by
    have hs : o.1 ∈ (((system.commit weights randomness).toRandomized.withQueryLog.run hash).bind
        fun out => PMF.pure out.1).support :=
      (PMF.mem_support_bind_iff _ _ _).2 ⟨o, ho, (PMF.mem_support_pure_iff _ _).2 rfl⟩
    rw [run_withQueryLog_fst, DeterministicAlgorithm.run_toRandomized] at hs
    exact (PMF.mem_support_pure_iff _ _).1 hs
  rw [PMF.pure_bind, run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind]
  show _ ≤ ZKCP.prob (PMF.pure _) _
  rw [ZKCP.prob_pure]
  exact ind_le fun hb => ⟨h1.symm, hb⟩

end VerifiableInference

#print axioms VerifiableInference.queryBound_at_sample
#print axioms VerifiableInference.BindsWith.atRandomness
