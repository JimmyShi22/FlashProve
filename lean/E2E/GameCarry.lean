-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/GameCarry.lean: index privacy carries every event on views from the ideal experiment to the real
one, at the cost of its error.

Summary. "Some session's proof in the view is not produced" is a set of views. In the ideal
experiment the answers to a simulated run's Fiat-Shamir queries are the simulator's own samples; in
the real one they depend on what the adversary has asked. So the event is bounded in the ideal
experiment (E2E/IdealStrings.lean) and carried over by this lemma (E2E/SessionsInGame.lean). It
holds for any scheme.

Main results.
  `real_le_ideal`: under `ZKCP.Gen.PrivacyFor R A Sim ζ i Z`, for every adversary with at most tV
    queries, every number N of batches and every set T of views, the real experiment ends in T with
    probability at most that of the ideal experiment plus ζ tV N.

Terms: E2E/HidingTerms.lean.

Limits. It inherits every premise and limit of the statement of index privacy that it is applied to.
By itself it says nothing about either experiment.


-/
import ZKCP.Gen

set_option autoImplicit false

open scoped ENNReal

namespace AtPublicFiles.Shown
open Rom Prob
open ZKCP.Gen

theorem real_le_ideal {S : OSpec} {I X W PP IVK ISK Pf : Type} {R : RelPair I X W PP}
    {A : Arg S I X W IVK ISK Pf} {Sim : Simulator S PP IVK X Pf} {ζ : ℕ → ℕ → ℝ≥0∞} {i : I}
    {Z : ViewEnv S IVK X W Pf} (h : PrivacyFor R A Sim ζ i Z) (tV : ℕ)
    (Vt : IVK → AdvVerifier S X Pf) (N : ℕ) (hq : ∀ ivk, (Vt ivk).QueryBound tV)
    (T : Set (View S IVK X Pf)) :
    Rom.Pr (realExp A Vt Z i N) (fun _ => T) ≤ pr (idealExp R Sim Vt Z i N) T + ζ tV N :=
  le_add_of_sd_le (h tV Vt N hq).1 T

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.real_le_ideal
