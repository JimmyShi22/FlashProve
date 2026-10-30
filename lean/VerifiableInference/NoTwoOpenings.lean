-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/NoTwoOpenings.lean: nobody opens one commitment to two different weights.

To open a commitment is to name weights and randomness from which the argument system's committer,
run again, computes that commitment.
  `NoTwoOpenings system ε`     for every adversary with at most `queries` queries that outputs a
                               commitment and two openings: the probability that both fit the
                               commitment and name different weights is at most ε queries
  `BindsWith.noTwoOpenings` it follows from `BindsWith` (VerifiableInference/MoreStatements.lean),
  for any
                               extractor, at twice the bound
Why: what the extractor gives is fixed by the commitment and the adversary's queries. It differs
from the weights of at least one of two openings that name different weights, and `BindsWith` bounds
each of the two cases.
The committer's two runs are not among the adversary's queries: a bound ε has to cover them.
Nothing is said of two openings with the same weights and different randomness.
This statement is not among those of VerifiableInference/Statements.lean; it is defined in
VerifiableInference/MoreStatements.lean.
-/
import VerifiableInference.MoreStatements
import VerifiableInference.Binds
import VerifiableInference.Bridge

set_option autoImplicit false

open scoped ENNReal

namespace VerifiableInference

open MeasureTheory RandomizedAlgorithm

/-- If the commitment binds to the weights that some extractor gives, with the bound ε, then nobody
opens one commitment to two different weights, with the bound 2 ε. -/
theorem BindsWith.noTwoOpenings {system : ArgumentSystem}
    {extractor : Commitment → QueryLog → Option system.Weights} {ε : ℕ → ℝ≥0∞}
    (binds : BindsWith system extractor ε) :
    NoTwoOpenings system fun queries => 2 * ε queries := by
  classical
  intro queries adversary hq
  -- the committer runs the adversary and keeps its whole result as the state; each of two openers
  -- reads one opening from it
  have b1 := binds queries 0 _ (adversary.bind fun o => .done (o.1, o))
    (queryBound_map _ adversary queries hq) (fun state => .done state.2.1) (fun _ => trivial)
  have b2 := binds queries 0 _ (adversary.bind fun o => .done (o.1, o))
    (queryBound_map _ adversary queries hq) (fun state => .done state.2.2) (fun _ => trivial)
  show Prob _ _ ≤ 2 * ε queries
  rw [two_mul]
  refine le_trans ?_ (add_le_add b1 b2)
  unfold Prob
  rw [← lintegral_add_right _ (measurable_eventProbability_run _ _)]
  refine lintegral_mono fun H => ?_
  have e0 : (adversary.bind fun o => (system.commit o.2.1.1 o.2.1.2).toRandomized.bind fun r₁ =>
        (system.commit o.2.2.1 o.2.2.2).toRandomized.bind fun r₂ =>
          RandomizedAlgorithm.done (o.1, o.2.1.1, o.2.2.1, r₁, r₂)).run H
      = (adversary.withQueryLog.run H).bind fun ol => PMF.pure
          (ol.1.1, ol.1.2.1.1, ol.1.2.2.1, (system.commit ol.1.2.1.1 ol.1.2.1.2).evaluate H,
          (system.commit ol.1.2.2.1 ol.1.2.2.2).evaluate H) := by
    simp only [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_done]
    conv_lhs => rw [← run_withQueryLog_fst H adversary]
    rw [PMF.bind_bind]
    simp only [PMF.pure_bind]
  have e1 : ((adversary.bind fun o => RandomizedAlgorithm.done (o.1, o)).withQueryLog.bind fun x =>
        (system.commit x.1.2.2.1.1 x.1.2.2.1.2).toRandomized.bind fun recomputed =>
          RandomizedAlgorithm.done (extractor x.1.1 x.2, x.1.1, x.1.2.2.1.1, recomputed)).run H
      = (adversary.withQueryLog.run H).bind fun ol => PMF.pure
          (extractor ol.1.1 ol.2, ol.1.1, ol.1.2.1.1,
          (system.commit ol.1.2.1.1 ol.1.2.1.2).evaluate H) := by
    simp only [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_done,
      run_withQueryLog_map, PMF.bind_bind]
  have e2 : ((adversary.bind fun o => RandomizedAlgorithm.done (o.1, o)).withQueryLog.bind fun x =>
        (system.commit x.1.2.2.2.1 x.1.2.2.2.2).toRandomized.bind fun recomputed =>
          RandomizedAlgorithm.done (extractor x.1.1 x.2, x.1.1, x.1.2.2.2.1, recomputed)).run H
      = (adversary.withQueryLog.run H).bind fun ol => PMF.pure
          (extractor ol.1.1 ol.2, ol.1.1, ol.1.2.2.1,
          (system.commit ol.1.2.2.1 ol.1.2.2.2).evaluate H) := by
    simp only [run_bind, DeterministicAlgorithm.run_toRandomized, PMF.pure_bind, run_done,
      run_withQueryLog_map, PMF.bind_bind]
  show ZKCP.prob ((adversary.bind fun o =>
        (system.commit o.2.1.1 o.2.1.2).toRandomized.bind fun r₁ =>
        (system.commit o.2.2.1 o.2.2.2).toRandomized.bind fun r₂ =>
          RandomizedAlgorithm.done (o.1, o.2.1.1, o.2.2.1, r₁, r₂)).run H) _
    ≤ ZKCP.prob (((adversary.bind fun o =>
        RandomizedAlgorithm.done (o.1, o)).withQueryLog.bind fun x =>
        (system.commit x.1.2.2.1.1 x.1.2.2.1.2).toRandomized.bind fun recomputed =>
          RandomizedAlgorithm.done (extractor x.1.1 x.2, x.1.1, x.1.2.2.1.1, recomputed)).run H) _
      + ZKCP.prob (((adversary.bind fun o =>
        RandomizedAlgorithm.done (o.1, o)).withQueryLog.bind fun x =>
        (system.commit x.1.2.2.2.1 x.1.2.2.2.2).toRandomized.bind fun recomputed =>
          RandomizedAlgorithm.done (extractor x.1.1 x.2, x.1.1, x.1.2.2.2.1, recomputed)).run H) _
  rw [e0, e1, e2, ZKCP.prob_bind, ZKCP.prob_bind, ZKCP.prob_bind, ← ZKCP.expect_add]
  refine ZKCP.expect_mono _ fun ol => ?_
  rw [ZKCP.prob_pure, ZKCP.prob_pure, ZKCP.prob_pure]
  -- for one run: the extractor's answer differs from the weights of the first or of the second
  refine ind_le_add ?_
  rintro ⟨hFirst, hSecond, hDiffer⟩
  by_cases hExtracted : extractor ol.1.1 ol.2 = some ol.1.2.1.1
  · right
    show (system.commit ol.1.2.2.1 ol.1.2.2.2).evaluate H = ol.1.1
      ∧ extractor ol.1.1 ol.2 ≠ some ol.1.2.2.1
    exact ⟨hSecond, fun h => hDiffer (Option.some.inj (hExtracted.symm.trans h))⟩
  · left
    show (system.commit ol.1.2.1.1 ol.1.2.1.2).evaluate H = ol.1.1
      ∧ extractor ol.1.1 ol.2 ≠ some ol.1.2.1.1
    exact ⟨hFirst, hExtracted⟩

end VerifiableInference

#print axioms VerifiableInference.BindsWith.noTwoOpenings
