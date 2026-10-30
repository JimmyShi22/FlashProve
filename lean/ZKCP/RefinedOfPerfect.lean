-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/RefinedOfPerfect.lean: for countable X and W, perfect completeness gives refined completeness.

`HasCompletenessError` asks, for each (i, x, w) in R, that V reject an honest proof with probability
at most α. Refined completeness lets (x, w) depend on the key: a key is bad if a valid (x, w)
is rejected with probability above α_P, taken over the prover's coins, and bad keys have probability
at most α_C. (In α_P, V's coins count too.) In general the first does not give the second.
At α = 0 it does, if there are only countably many pairs (x, w): for each valid pair, almost every
oracle f is such that no key that C^f(i) can output rejects the pair with positive probability; a
countable union of null sets of oracles is null.
  `refined_of_perfect`: the theorem, with (α_C, α_P) = (0, 0)
Nothing here is part of the definitions of ZKCP/Defs.lean.
-/
import ZKCP.Basic

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ZKCP

namespace RefinedOfPerfect

variable {α : Type}

/-- If the average of F is 0, F has value 0 at every point of positive probability. -/
theorem eq_zero_of_expect_eq_zero
    {p : PMF α} {F : α → ℝ≥0∞} (h : expect p F = 0) {a : α} (ha : p a ≠ 0) : F a = 0 := by
  have h1 := (ENNReal.tsum_eq_zero.1 h) a
  exact (mul_eq_zero.1 h1).resolve_left ha

/-- An event that no point of positive probability meets has probability 0. -/
theorem prob_eq_zero {p : PMF α} {E : Set α} (h : ∀ a, p a ≠ 0 → a ∉ E) : prob p E = 0 := by
  classical
  rw [prob_eq_expect]
  refine ENNReal.tsum_eq_zero.2 fun a => ?_
  by_cases ha : p a = 0
  · rw [ha, zero_mul]
  · simp only [if_neg (h a ha), mul_zero]

end RefinedOfPerfect

variable {lam : ℕ} {I X W PP IVK ISK Pf : Type}
variable (R : IndexedRelation I X W PP) (A : Arg lam I X W IVK ISK Pf)

open RefinedOfPerfect in
/-- Perfect completeness (`HasCompletenessError` with α = 0) gives refined completeness
with (α_C, α_P) = (0, 0), for countably many instances and witnesses. -/
theorem refined_of_perfect [Countable X] [Countable W] (h : HasCompletenessError R A 0) :
    HasRefinedCompletenessError R A 0 0 := by
  intro i
  have e : ∀ (f : Oracle lam) (x : X) (w : W), PrCoins f (completenessExp A i x w) {b | b = false} =
      expect ((A.C i).run f) fun key =>
        PrCoins f (sessionExp A key.1 key.2 x w) {b | b = false} := fun f x w => by
    simp only [PrCoins, completenessExp, bind_eq, run_bind, prob_bind]
  -- for each valid pair, almost every oracle makes the experiment of `HasCompletenessError`
  -- fail with probability 0
  have h1 : ∀ xw : X × W, ∀ᵐ f ∂(U lam), R.rel i xw.1 xw.2 → PrCoins f (completenessExp A i xw.1 xw.2) {b | b = false} = 0 := by
    intro xw
    by_cases hR : R.rel i xw.1 xw.2
    · have h0 : ∫⁻ f, PrCoins f (completenessExp A i xw.1 xw.2) {b | b = false} ∂(U lam) = 0 :=
        le_antisymm (h i xw.1 xw.2 hR) (zero_le _)
      have h2 := (lintegral_eq_zero_iff
        (measurable_prob_run (completenessExp A i xw.1 xw.2) {b | b = false})).1 h0
      exact h2.mono fun f hf _ => hf
    · exact Filter.Eventually.of_forall fun f hr => absurd hr hR
  -- so almost every oracle does so for all valid pairs at once
  have h2 : ∀ᵐ f ∂(U lam), ∀ xw : X × W, R.rel i xw.1 xw.2 →
      PrCoins f (completenessExp A i xw.1 xw.2) {b | b = false} = 0 := ae_all_iff.2 h1
  -- and for such an oracle no key that C can output is bad
  have h3 : ∀ᵐ f ∂(U lam), PrCoins f (A.C i) (badKeys R A 0 i f) = 0 := h2.mono fun f hf => by
    refine prob_eq_zero fun key hkey hbad => ?_
    obtain ⟨x, w, hR, hpos⟩ := hbad
    have h4 := hf (x, w) hR
    rw [e] at h4
    exact absurd (eq_zero_of_expect_eq_zero h4 hkey) (ne_of_gt hpos)
  refine le_of_eq ?_
  unfold Pr
  rw [lintegral_congr_ae h3, lintegral_zero]

end ZKCP
