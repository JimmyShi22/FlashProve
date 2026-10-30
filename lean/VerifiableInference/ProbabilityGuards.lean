-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/ProbabilityGuards.lean

Guards on `Prob`: the sure event has probability 1, and an event and its complement add up to 1.

`Sound`, `SoundAndBinding`, `SoundOpened` and `Complete` (VerifiableInference/Statements.lean) each
bound `Prob experiment event`, and so do further statements in
VerifiableInference/MoreStatements.lean, and `CompleteOn` (VerifiableInference/Steps.lean). `Prob`
(VerifiableInference/RandomOracleModel.lean) is an integral over the hash function. If the measure
on hash functions had mass 0, every such bound would hold and say nothing. It has mass 1
(`uniformHash_univ`); the sure event has probability 1 in every experiment (`Prob_univ`); no event
has a probability above 1 (`Prob_le_one`); an event and its complement have probabilities that add
up to 1 (`Prob_add_compl`). That also rules out a loss in the integral: `Prob` is written as a lower
integral, and the sum is 1 because the integrand is measurable (`measurable_eventProbability_run`,
VerifiableInference/Bridge.lean). So a bound ε on a bad event says that the complement has
probability at least 1 - ε (`one_sub_le_Prob_compl`; for ε ≥ 1 that says nothing). `ZeroKnowledge`
and `ZeroKnowledgeOn` compare `Prob` of the real experiment with `eventProbability` of the simulated
one: both have mass 1 (`Prob_univ`, `eventProbability_univ`).

`Pr_univ` says what `Prob_univ` says, of the library's own `ZKCP.Pr`; `Prob` is `ZKCP.Pr` of the
corresponding algorithm, at 256 bits, for events that do not mention the hash function
(`Prob_eq_Pr`, VerifiableInference/Bridge.lean). For `ZKCP.Pr`, `Prob_le_one` is `ZKCP.Pr_le_one`
(ZKCP/Lemmas.lean), and `Prob_add_compl` is `ZKCP.Pr_add_compl` (ZKCP/Basic.lean), that one too for
events that do not mention the hash function.

The file is general: it speaks of no protocol and says nothing on how large any bound is. Mass 1
does not show that the measure is the uniform one: for that see `ZKCP.U_cylinder`
(ZKCP/Lemmas.lean), through `uniformHash_eq`. Nothing here says that a real hash function behaves
like a random one.
-/
import VerifiableInference.Bridge

set_option autoImplicit false

open scoped ENNReal

namespace VerifiableInference

/-- The uniform distribution on hash functions has mass 1. -/
theorem uniformHash_univ : uniformHash Set.univ = 1 := by
  rw [uniformHash_eq]
  exact MeasureTheory.measure_univ

/-- Under a distribution the sure event has probability 1. -/
theorem eventProbability_univ {α : Type} (distribution : PMF α) :
    eventProbability distribution Set.univ = 1 :=
  (PMF.toOuterMeasure_apply_eq_one_iff distribution Set.univ).2 (Set.subset_univ _)

/-- Under a distribution the probabilities of an event and of its complement add up to 1. -/
theorem eventProbability_add_compl {α : Type} (distribution : PMF α) (event : Set α) :
    eventProbability distribution event + eventProbability distribution eventᶜ = 1 := by
  unfold eventProbability
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
  refine (tsum_congr fun x => ?_).trans distribution.tsum_coe
  exact congrFun (Set.indicator_self_add_compl event distribution) x

/-- In every experiment the sure event has probability 1. -/
theorem Prob_univ {α : Type} (experiment : RandomizedAlgorithm α) :
    Prob experiment Set.univ = 1 := by
  unfold Prob
  simp only [eventProbability_univ]
  rw [MeasureTheory.lintegral_one]
  exact uniformHash_univ

/-- No event has a probability above 1. -/
theorem Prob_le_one {α : Type} (experiment : RandomizedAlgorithm α) (event : Set α) :
    Prob experiment event ≤ 1 := by
  rw [Prob_eq_Pr]
  exact ZKCP.Pr_le_one _ _

/-- In every experiment the probabilities of an event and of its complement add up to 1. -/
theorem Prob_add_compl {α : Type} (experiment : RandomizedAlgorithm α) (event : Set α) :
    Prob experiment event + Prob experiment eventᶜ = 1 := by
  unfold Prob
  rw [← MeasureTheory.lintegral_add_left (measurable_eventProbability_run experiment event)]
  simp only [eventProbability_add_compl]
  rw [MeasureTheory.lintegral_one]
  exact uniformHash_univ

/-- If an event has probability at most ε, its complement has probability at least 1 - ε. For ε ≥ 1
that says nothing. -/
theorem one_sub_le_Prob_compl {α : Type} (experiment : RandomizedAlgorithm α) (event : Set α)
    {ε : ℝ≥0∞} (h : Prob experiment event ≤ ε) : 1 - ε ≤ Prob experiment eventᶜ :=
  tsub_le_iff_left.2 ((Prob_add_compl experiment event).ge.trans (add_le_add h le_rfl))

/-- The same as `Prob_univ` for the library's own probability `ZKCP.Pr` (ZKCP/Defs.lean), at every
length of the hash function's values. -/
theorem Pr_univ {lam : ℕ} {α : Type} (computation : ZKCP.OComp lam α) :
    ZKCP.Pr computation (fun _ => Set.univ) = 1 := by
  have h : ∀ f, ZKCP.PrCoins f computation Set.univ = 1 := fun f =>
    (PMF.toOuterMeasure_apply_eq_one_iff (computation.run f) Set.univ).2 (Set.subset_univ _)
  unfold ZKCP.Pr
  simp only [h]
  rw [MeasureTheory.lintegral_one]
  exact MeasureTheory.measure_univ

end VerifiableInference

#print axioms VerifiableInference.uniformHash_univ
#print axioms VerifiableInference.eventProbability_univ
#print axioms VerifiableInference.eventProbability_add_compl
#print axioms VerifiableInference.Prob_univ
#print axioms VerifiableInference.Prob_le_one
#print axioms VerifiableInference.Prob_add_compl
#print axioms VerifiableInference.one_sub_le_Prob_compl
#print axioms VerifiableInference.Pr_univ
