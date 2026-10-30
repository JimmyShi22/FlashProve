-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/Open.lean -- the event of `HasRefinedCompletenessError` is measurable for arbitrary types of
instances and witnesses. The event: `badKeys` (ZKCP/Defs.lean), the bad keys for a fixed f: the keys
for which some (x, w) with (i, x, w) ∈ R is rejected with probability more than α_P.

With f fixed, the probability that an oracle algorithm's output is in an event depends on finitely
many values of f only. So { f | that probability > a } is an open set of the product topology on
{0,1}^* → {0,1}^λ. For a fixed key, the set of oracles for which the key is bad (the bad-key event
of `badKeys`) is a union of such sets, over all (x, w) with (i, x, w) ∈ R. A union of any
number of open sets is open, and open sets are measurable here, because the index set {0,1}^* is
countable and {0,1}^λ is finite. No countability of X or W is needed.
-/
import ZKCP.Finite
import ZKCP.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ZKCP

variable {lam : ℕ} {α : Type}

/-- The set of oracles that agree with f₀ on the finite set S is open. -/
lemma isOpen_agree (S : Finset Str) (f₀ : Oracle lam) :
    IsOpen {f : Oracle lam | ∀ q ∈ S, f q = f₀ q} := by
  have h : {f : Oracle lam | ∀ q ∈ S, f q = f₀ q} = Set.pi (S : Set Str) fun q => {f₀ q} := by
    ext f; simp [Set.mem_pi]
  rw [h]
  exact isOpen_set_pi S.finite_toSet fun q _ => isOpen_discrete _

/-- A property of the oracle that depends only on its values on a finite set is open. -/
lemma isOpen_of_finite_dependence {P : Oracle lam → Prop} (S : Finset Str)
    (h : ∀ f g : Oracle lam, (∀ q ∈ S, f q = g q) → (P f ↔ P g)) : IsOpen {f | P f} := by
  rw [isOpen_iff_forall_mem_open]
  intro f₀ hf₀
  exact ⟨{f | ∀ q ∈ S, f q = f₀ q}, fun f hf => (h f f₀ hf).2 hf₀,
    isOpen_agree S f₀, fun _ _ => rfl⟩

/-- { f | Pr[ output ∈ E ] > a }, the probability over the coins alone, is open. -/
lemma isOpen_PrCoins_gt (c : OComp lam α) (E : Set α) (a : ℝ≥0∞) :
    IsOpen {f : Oracle lam | PrCoins f c E > a} := by
  obtain ⟨S, hS⟩ := c.exists_queriesIn
  exact isOpen_of_finite_dependence S fun f g h => by rw [PrCoins_congr h c hS]

/-- The integrand of Pr is measurable also for an event E(f) that mentions f, provided that for each
output a the set { f | a ∈ E(f) } is measurable. -/
lemma measurable_PrCoins_dep (c : OComp lam α) (E : Oracle lam → Set α)
    (hE : ∀ a, MeasurableSet {f | a ∈ E f}) : Measurable fun f => PrCoins f c (E f) := by
  classical
  unfold PrCoins
  induction c with
  | pure a =>
    simp only [OComp.run, prob_pure]
    exact Measurable.ite (hE a) measurable_const measurable_const
  | query q k ih =>
    have h : Measurable fun p : Oracle lam × Digest lam => prob ((k p.2).run p.1) (E p.1) :=
      measurable_from_prod_countable_left fun r => ih r
    exact h.comp (measurable_id.prodMk (measurable_pi_apply q))
  | sample n k ih =>
    simp only [OComp.run, prob_bind, expect_uniform]
    exact Finset.measurable_sum _ fun r _ => (ih r).const_mul _

section
variable {I X W PP IVK ISK Pf : Type}
variable (R : IndexedRelation I X W PP) (A : Arg lam I X W IVK ISK Pf)

/-- For a fixed key, the set of oracles for which the key is bad (`HasRefinedCompletenessError`) is
open. -/
theorem isOpen_badKeys (αP : ℝ≥0∞) (i : I) (key : IVK × ISK) :
    IsOpen {f : Oracle lam | key ∈ badKeys R A αP i f} := by
  have h : {f : Oracle lam | key ∈ badKeys R A αP i f}
      = ⋃ (x : X) (w : W) (_ : R.rel i x w),
          {f | PrCoins f (sessionExp A key.1 key.2 x w) {b | b = false} > αP} := by
    ext f; simp [badKeys]
  rw [h]
  exact isOpen_iUnion fun x => isOpen_iUnion fun w => isOpen_iUnion fun _ => isOpen_PrCoins_gt _ _ _

/-- The integrand of `HasRefinedCompletenessError` is measurable, for arbitrary types X and W. So
the integral in HasRefinedCompletenessError is the true probability of the event "bad key". -/
theorem measurable_refined_integrand (αP : ℝ≥0∞) (i : I) :
    Measurable fun f : Oracle lam => PrCoins f (A.C i) (badKeys R A αP i f) :=
  measurable_PrCoins_dep _ _ fun key => (isOpen_badKeys R A αP i key).measurableSet

end

end ZKCP
