-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/EagerAudited.lean: lemmas on the definitions of ZKCP/Defs.lean and ZKCP/Lemmas.lean; above all,
the integrands of the four probabilities of ZKCP/Defs.lean are measurable.

They are about ZKCP/Defs.lean's oracle model (the uniform distribution U(λ) on all functions, and
algorithms with access to the oracle f) and the file's four probabilities (`HasCompletenessError`,
`HasRefinedCompletenessError`, `HasIndexBinding`, `HasIndexPrivacy`).

  `expect_eq`, `prob_eq`          `ZKCP.expect` and `ZKCP.prob` are `Prob.expect` and `Prob.pr`, so
                                  that the lemmas of Prob/Count.lean apply to them.
  `OComp.exists_dependsOn_run`    A run reads finitely many values of the oracle.
  `mem_support_lazyAnswer`        If (r, T') is in the support of `lazyAnswer T q`, then
                                  `T' = Function.update T q (some r) ∧ CacheLE T T'`.
  `OComp.lazyRun_withTrace_map`   Recording the trace changes neither the output nor the table.
  `measurable_integrand_binding`  With its three companions: the integrands of the four
                                  probabilities are measurable, for arbitrary types.

These four restate `measurable_refined_integrand` (ZKCP/Open.lean) and three instances of
`measurable_prob_run` (ZKCP/Lemmas.lean), so that all four are together.

Notation: `PrCoins f c E : ℝ≥0∞` (ZKCP/Defs.lean): Pr[ a ∈ E | a ← c^f ] for a fixed f: the
probability is over c's coins only; `badKeys R A αP i f` (there): the event of
bad keys for a fixed f; `St : Type`, `Ct : OComp lam (IVK × St)`, `Pt : St → OComp lam (X × Pf)`:
binders of `HasIndexBindingWith` (there); `Vt : IVK → AdvVerifier lam X Pf`,
`Z : ViewEnv lam IVK X W Pf`, `N : ℕ`: binders of `PrivacyFor` (there); `Cache lam : Type`
(ZKCP/Lemmas.lean): a partial table of oracle values already fixed; `lazyAnswer c q` (there): one
lazily sampled oracle answer: from the table if present, else fresh, uniform and recorded;
`CacheLE c c' : Prop` (ZKCP/Basic.lean): table c' extends table c.
Terms: lean/GLOSSARY.md.
-/
import Rom.Eager
import ZKCP.Open
import ZKCP.Basic

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ZKCP

variable {lam : ℕ} {α β : Type}

theorem expect_eq (p : PMF α) (F : α → ℝ≥0∞) : expect p F = Prob.expect p F := rfl

theorem prob_eq (p : PMF α) (E : Set α) : prob p E = Prob.pr p E := rfl



/-- A run reads finitely many values of the oracle: the tree is finite. -/
theorem OComp.exists_dependsOn_run (c : OComp lam α) :
    ∃ s : Finset Str, DependsOn (fun f : Oracle lam => c.run f) s := by
  obtain ⟨s, hs⟩ := c.exists_queriesIn
  exact ⟨s, fun _ _ h => OComp.run_congr (fun q hq => h q (Finset.mem_coe.2 hq)) c hs⟩



/-! ### Lazy sampling and the trace -/


theorem mem_support_lazyAnswer {T T' : Cache lam} {q : Str} {r : Digest lam}
    (h : (r, T') ∈ (lazyAnswer T q).support) :
    T' = Function.update T q (some r) ∧ CacheLE T T' := by
  unfold lazyAnswer at h
  cases hq : T q with
  | some r₀ =>
    simp only [hq, PMF.mem_support_pure_iff, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by rw [← hq, Function.update_eq_self], fun _ _ e => e⟩
  | none =>
    simp only [hq, PMF.mem_support_map_iff, Prod.mk.injEq] at h
    obtain ⟨r₁, -, rfl, rfl⟩ := h
    refine ⟨rfl, fun q' r' e => ?_⟩
    have hne : q' ≠ q := fun e' => by rw [e', hq] at e; cases e
    rw [Function.update_of_ne hne]; exact e

/-- Recording the trace changes neither the output nor the table. -/
theorem OComp.lazyRun_withTrace_map (c : OComp lam α) (T : Cache lam) :
    (c.withTrace.lazyRun T).map (fun o => (o.1.1, o.2)) = c.lazyRun T := by
  induction c generalizing T with
  | pure a => simp [OComp.withTrace, OComp.lazyRun, PMF.pure_map]
  | query q k ih =>
    simp only [OComp.withTrace, OComp.lazyRun, OComp.lazyRun_bind, PMF.map_bind, PMF.pure_map]
    congr 1; funext o; rw [← ih o.1 o.2]; rfl
  | sample n k ih =>
    simp only [OComp.withTrace, OComp.lazyRun, PMF.map_bind, ih]

/-! ### Every integral of Defs.lean is the integral of a measurable function

Mathlib's ∫⁻ is defined for every function, but for a non-measurable one it is only a lower
integral. Defs.lean has one integral sign, in Pr, and uses it four times. In all four the integrand
is measurable, whatever the types of indices, instances, witnesses, keys and proofs are. -/

section Integrands

variable {I X W PP IVK ISK Pf : Type}
variable (R : IndexedRelation I X W PP) (A : Arg lam I X W IVK ISK Pf)

/-- The integrand of `HasCompletenessError` is measurable. -/
theorem measurable_integrand_completeness (i : I) (x : X) (w : W) :
    Measurable fun f : Oracle lam => PrCoins f (completenessExp A i x w) {b | b = false} :=
  measurable_prob_run _ _

/-- The integrand of `HasRefinedCompletenessError` is measurable. Its event depends on the whole
f and has a quantifier over (x, w) inside, whose types may have any size. (Restated from
ZKCP/Open.lean.) -/
theorem measurable_integrand_refinedCompleteness (αP : ℝ≥0∞) (i : I) :
    Measurable fun f : Oracle lam => PrCoins f (A.C i) (badKeys R A αP i f) :=
  measurable_refined_integrand R A αP i

/-- The integrand of `HasIndexBinding` is measurable. -/
theorem measurable_integrand_binding {St : Type} (E : Extractor lam I X W IVK Pf)
    (Ct : OComp lam (IVK × St)) (Pt : St → OComp lam (X × Pf)) :
    Measurable fun f : Oracle lam => PrCoins f (bindingExp A E Ct Pt) (bindingBad R) :=
  measurable_prob_run _ _

/-- The integrand of `HasIndexPrivacy` is measurable, for every event on the view. -/
theorem measurable_integrand_privacy (Vt : IVK → AdvVerifier lam X Pf) (Z : ViewEnv lam IVK X W Pf)
    (i : I) (N : ℕ) (T : Set (View lam IVK X Pf)) :
    Measurable fun f : Oracle lam => PrCoins f (realExp A Vt Z i N) T :=
  measurable_prob_run _ _

end Integrands

end ZKCP
