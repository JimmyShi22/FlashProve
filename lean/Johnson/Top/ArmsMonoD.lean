-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmsMonoD.lean: an arm's bound with a reading (`ArmBoundD`, Johnson/Top/ArmsD.lean)
passes to an arm that accepts no more often, and to a weaker promise.

Why. The arm of which a bound is proved and the term that is run need not be one term. Where the
term that is run says yes only where the arm says yes, at every function, it has the arm's bound.
`ArmBound.mono` (Johnson/Top/Arms.lean) says it for a bound without a reading.

Main names.
  `ArmBoundD.mono`: an arm v' that, at every function, key, instance and proof, accepts with at most
    the probability with which v accepts has v's bound.
  `ArmBoundD.mono_of_det`: the same for arms without coins: v' says yes only where v says yes.
  `ArmBoundD.weakenHolds`: a bound for a promise is a bound for every promise that it gives.

What is not claimed. Nothing on any written arm, reading or promise. The reading draws no coin. The
reading, the error and the two budgets do not turn. Nor do the family of oracles and the types of
keys, instances and proofs: a term that takes another kind of proof (a file, or a string at another
protocol) needs a step that carries the prover's output, which is not here. That v' ever says yes is
not asked: an arm that refuses everything meets the premise at every v, and the bound that it takes
over says nothing of it. At letters; over any family of oracles. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.ArmsD

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP.Gen

open Rom (OSpec Fam)
open Prob (pr expect)

variable {S : OSpec} {X IVK Pf D : Type}

/-- **An arm that accepts no more often has the bound.** -/
theorem ArmBoundD.mono {rd : IVK → Rom.OComp S D} (hrd : ∀ k, (rd k).NoCoin)
    {v v' : IVK → X → Pf → Rom.OComp S Bool}
    {Holds : D → IVK → Rom.Trace S → X → Pf → Rom.Trace S → Prop} {ε : ℕ → ℕ → ℝ≥0∞}
    (h : ArmBoundD rd v Holds ε)
    (le : ∀ f k x π,
      pr ((v' k x π).runEager f) {b | b = true} ≤ pr ((v k x π).runEager f) {b | b = true}) :
    ArmBoundD rd v' Holds ε := by
  classical
  intro tC tP St Ct Pt hC hP
  refine le_trans ?_ (h tC tP St Ct Pt hC hP)
  unfold Rom.Pr
  refine MeasureTheory.lintegral_mono fun f => ?_
  simp only [Rom.PrCoins]
  rw [runEager_armExpD hrd, runEager_armExpD hrd]
  rw [Prob.pr_bind, Prob.pr_bind]
  refine Prob.expect_mono _ fun o => ?_
  rw [Prob.pr_bind, Prob.pr_bind]
  refine Prob.expect_mono _ fun o' => ?_
  by_cases hh : Holds ((rd o.1.1).det f) o.1.1 o.2 o'.1.1 o'.1.2 o'.2
  · refine le_trans (le_of_eq ?_) (zero_le _)
    rw [Prob.pr_bind]
    refine le_antisymm
      (le_trans (Prob.expect_mono _ fun b => ?_) (le_of_eq (Prob.expect_const _ 0))) (zero_le _)
    rw [Prob.pr_pure, if_neg]
    rintro ⟨-, hn⟩
    exact hn hh
  · rw [pr_armD_of_not (Holds := Holds) _ _ _ _ _ _ _ hh,
      pr_armD_of_not (Holds := Holds) _ _ _ _ _ _ _ hh]
    exact le f _ _ _

/-- For arms without coins: an arm that says yes only where v says yes has v's bound. -/
theorem ArmBoundD.mono_of_det {rd : IVK → Rom.OComp S D} (hrd : ∀ k, (rd k).NoCoin)
    {v v' : IVK → X → Pf → Rom.OComp S Bool} (hv : ∀ k x π, (v k x π).NoCoin)
    (hv' : ∀ k x π, (v' k x π).NoCoin)
    {Holds : D → IVK → Rom.Trace S → X → Pf → Rom.Trace S → Prop} {ε : ℕ → ℕ → ℝ≥0∞}
    (h : ArmBoundD rd v Holds ε)
    (imp : ∀ (f : Fam S) k x π, (v' k x π).det f = true → (v k x π).det f = true) :
    ArmBoundD rd v' Holds ε := by
  classical
  refine h.mono hrd fun f k x π => ?_
  rw [(hv' k x π).runEager f, (hv k x π).runEager f, Prob.pr_pure, Prob.pr_pure]
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (imp f k x π h1) h2
  · exact zero_le _
  · exact le_rfl

/-- A bound for a promise is a bound for every promise that it gives. -/
theorem ArmBoundD.weakenHolds {rd : IVK → Rom.OComp S D} {v : IVK → X → Pf → Rom.OComp S Bool}
    {Holds Holds' : D → IVK → Rom.Trace S → X → Pf → Rom.Trace S → Prop} {ε : ℕ → ℕ → ℝ≥0∞}
    (h : ArmBoundD rd v Holds ε)
    (imp : ∀ d k trC x π trP, Holds d k trC x π trP → Holds' d k trC x π trP) :
    ArmBoundD rd v Holds' ε := by
  intro tC tP St Ct Pt hC hP
  refine le_trans ?_ (h tC tP St Ct Pt hC hP)
  unfold Rom.Pr
  refine MeasureTheory.lintegral_mono fun f => ?_
  simp only [Rom.PrCoins]
  refine Prob.pr_mono _ fun o ho => ?_
  exact ⟨ho.1, fun hh => ho.2 (imp _ _ _ _ _ _ hh)⟩

end ZKCP.Gen
