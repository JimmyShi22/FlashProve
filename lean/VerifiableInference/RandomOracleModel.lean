-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/RandomOracleModel.lean

The model of hashes (the random oracle model). A hash function is one function from bit strings to
256 bits.
In every `Prob` of VerifiableInference/Statements.lean it is sampled uniformly at random, and an
algorithm reaches it by queries alone. In the simulated experiment the simulator is in the place of
the hash function.

Definitions only, over Mathlib. Nothing is proved here, and no other file of this library is
imported.
-/
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
noncomputable section -- markers lifted: Lean tags what it cannot compile

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace VerifiableInference

/-! ## 1. Hash functions -/

/-- A bit string, of any finite length. -/
abbrev BitString : Type := List Bool

/-- A value of the hash function: 256 bits. -/
abbrev Digest : Type := Fin 256 → Bool

/-- A hash function: one function from bit strings to 256 bits. -/
abbrev Hash : Type := BitString → Digest

/-- The uniform distribution on hash functions: the value at each bit string is uniform on the
256-bit values, and the values at different bit strings are independent. -/
def uniformHash : Measure Hash :=
  Measure.infinitePi fun _ : BitString => (PMF.uniformOfFintype Digest).toMeasure

/-! ## 2. Randomized algorithms that query the hash function -/

/-- A randomized algorithm with query access to the hash function, with a result in α. It is a tree.
At each step it
* stops with a result, or
* queries the hash function at a bit string and continues with the answer, or
* samples a number uniformly from 0, …, `bound` and continues with it.
Its running time is not bounded: the next step is any function of what it has seen. -/
inductive RandomizedAlgorithm (α : Type) : Type
  | done (result : α) : RandomizedAlgorithm α
  | query (input : BitString) (next : Digest → RandomizedAlgorithm α) : RandomizedAlgorithm α
  | sample (bound : ℕ) (next : Fin (bound + 1) → RandomizedAlgorithm α) : RandomizedAlgorithm α

/-- Run the first algorithm, then `rest` on its result. -/
def RandomizedAlgorithm.bind {α β : Type} : RandomizedAlgorithm α → (α → RandomizedAlgorithm β) →
    RandomizedAlgorithm β
  | .done result, rest => rest result
  | .query input next, rest => .query input fun answer => (next answer).bind rest
  | .sample bound next, rest => .sample bound fun draw => (next draw).bind rest

/-- This instance only provides the do-notation of the experiments. -/
instance : Monad RandomizedAlgorithm where
  pure := RandomizedAlgorithm.done
  bind := RandomizedAlgorithm.bind

/-- The distribution of the result under one fixed hash function: the probability is over the
algorithm's own random choices. -/
def RandomizedAlgorithm.run {α : Type} (hash : Hash) : RandomizedAlgorithm α → PMF α
  | .done result => PMF.pure result
  | .query input next => (next (hash input)).run hash
  | .sample bound next => (PMF.uniformOfFintype (Fin (bound + 1))).bind fun draw => (next draw).run
      hash

/-- The algorithm makes at most `queries` queries to the hash function, on every path. A repeated
query counts each time. -/
def RandomizedAlgorithm.QueryBound {α : Type} : RandomizedAlgorithm α → ℕ → Prop
  | .done _, _ => True
  | .query _ _, 0 => False
  | .query _ next, queries + 1 => ∀ answer, (next answer).QueryBound queries
  | .sample _ next, queries => ∀ draw, (next draw).QueryBound queries

/-- A query log: the queries that an algorithm made to the hash function, each with its answer, in
order. -/
abbrev QueryLog : Type := List (BitString × Digest)

/-- The same algorithm, returning its query log beside its result. -/
def RandomizedAlgorithm.withQueryLog {α : Type} : RandomizedAlgorithm α → RandomizedAlgorithm
    (α × QueryLog)
  | .done result => .done (result, [])
  | .query input next => .query input fun answer =>
      (next answer).withQueryLog.bind fun rest => .done (rest.1, (input, answer) :: rest.2)
  | .sample bound next => .sample bound fun draw => (next draw).withQueryLog

/-! ## 3. Probability -/

/-- The probability of an event under a distribution. -/
def eventProbability {α : Type} (distribution : PMF α) (event : Set α) : ℝ≥0∞ :=
  distribution.toOuterMeasure event

/-- The probability that the result of an experiment is in `event`, over a hash function sampled
uniformly at random and the random choices of the experiment.
Written as a lower integral. The integrand is measurable (`measurable_eventProbability_run`,
VerifiableInference/Bridge.lean). -/
def Prob {α : Type} (experiment : RandomizedAlgorithm α) (event : Set α) : ℝ≥0∞ :=
  ∫⁻ hash, eventProbability (experiment.run hash) event ∂uniformHash

/-- The statistical distance of two distributions, each given by its probabilities of events:
the least upper bound of the differences between the two probabilities of one event. -/
def statisticalDistance {α : Type} (first second : Set α → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ event : Set α, max (first event - second event) (second event - first event)

/-! ## 4. Deterministic algorithms that query the hash function -/

/-- A deterministic algorithm with query access to the hash function:
it stops with a result, or it queries the hash function and continues with the answer. It uses no
randomness. -/
inductive DeterministicAlgorithm (α : Type) : Type
  | done (result : α) : DeterministicAlgorithm α
  | query (input : BitString) (next : Digest → DeterministicAlgorithm α) : DeterministicAlgorithm α

/-- The result under the hash function `hash`. -/
def DeterministicAlgorithm.evaluate {α : Type} (hash : Hash) : DeterministicAlgorithm α → α
  | .done result => result
  | .query input next => (next (hash input)).evaluate hash

/-- The same algorithm as a step of an experiment. -/
def DeterministicAlgorithm.toRandomized {α : Type} : DeterministicAlgorithm α → RandomizedAlgorithm
    α
  | .done result => .done result
  | .query input next => .query input fun answer => (next answer).toRandomized

end VerifiableInference
