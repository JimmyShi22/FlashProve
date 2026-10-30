-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Prob/Basic.lean: the five definitions of discrete probability that the library shares.

It fixes what Pr[·], E[·], "x uniform in S" and "statistical distance" mean in this library
(ZKCP/Defs.lean and ZKCP/Lemmas.lean declare their own `prob`, `SD`, `expect`, with the same
right-hand sides; ZKCP/Special.lean passes from `SD` to `sd` by unfolding), on Mathlib's type `PMF`
of discrete probability distributions. Definitions only.
The lemmas are in Prob/Count.lean (probabilities, averages, counts) and Prob/Tv.lean (statistical
distance).
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Prob.Cnt
noncomputable section -- Lean tags what it cannot compile

open scoped ENNReal

namespace Prob

universe u
variable {α : Type u}

/-- Pr[ a ∈ E | a ← p ] for a discrete distribution p; it equals the sum of p(a) over a ∈ E. -/
def pr (p : PMF α) (E : Set α) : ℝ≥0∞ := p.toOuterMeasure E

/-- E[ F(a) | a ← p ], the average of a non-negative (possibly infinite) quantity. -/
def expect (p : PMF α) (F : α → ℝ≥0∞) : ℝ≥0∞ := ∑' a, p a * F a

/-- The uniform distribution on a finite non-empty type. -/
abbrev unif (C : Type u) [Fintype C] [Nonempty C] : PMF C := PMF.uniformOfFintype C

/-- Statistical distance of two "distributions given by their event probabilities":
the supremum over all events E of |X(E) - Y(E)|.  Subtraction in ℝ≥0∞ is truncated at 0, hence the
maximum of both orders. -/
def sd (X Y : Set α → ℝ≥0∞) : ℝ≥0∞ := ⨆ E : Set α, max (X E - Y E) (Y E - X E)

/-- Statistical (total variation) distance of two discrete distributions. -/
def tv (p q : PMF α) : ℝ≥0∞ := sd (pr p) (pr q)

end Prob
