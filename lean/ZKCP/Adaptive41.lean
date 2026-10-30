-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  ZKCP/Adaptive41.lean -- beside `sessions_of_refined` (ZKCP/Basic.lean): with completeness
  (`HasCompletenessError`) alone, a bound of N·α for N sessions does not hold for adaptive
  choices of instances. The last sentence of a proposition of the work that this protocol builds
  on (lean/CREDITS.md, "Further work") states that bound.
  Completeness fixes (x, w) before f is sampled. In the scheme below every proof carries y = f(ε),
  and V rejects exactly the instance x = y.
  * adaptive_complete : completeness error 2^-λ in the sense of `HasCompletenessError`;
  * adaptive_rejected : the chooser that takes x_2 := π_1 has a rejected session among N = 2 with
    probability 1 (with α = 2^-λ, 2·α < 1 needs λ ≥ 2);
  * adaptive_fails : so the scheme has no adaptive completeness (Adaptive.lean) better than
    α(0, 2) = 1.
  Notation: α(t, N): a function ℕ → ℕ → ℝ≥0∞, the `α` of `HasAdaptiveCompletenessError`
  (ZKCP/Adaptive.lean): there t stands in `(E ivk).QueryBound t`, N in `adaptiveExp A E i N`.
-/
import ZKCP.HashToy
import ZKCP.Adaptive

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ZKCP

section Adaptive41
variable (lam : ℕ)

/-- Every λ-bit string is an instance of the one index. -/
def digR : IndexedRelation Unit (Digest lam) Unit Unit where
  rel := fun _ _ _ => True
  pp := fun _ => ()

/-- P sends y = f(ε); V rejects the instance y. -/
def adaArg : Arg lam Unit (Digest lam) Unit Unit Unit (Digest lam) where
  C := fun _ => .pure ((), ())
  P := fun _ _ _ => .query [] fun y => .pure y
  V := fun _ x _ => .query [] fun y => .pure (decide (x ≠ y))

/-- Completeness (ZKCP/Defs.lean, `HasCompletenessError`) holds with α = 2^-λ. -/
theorem adaptive_complete : HasCompletenessError (digR lam) (adaArg lam) (u lam) := by
  classical
  intro i x w _
  rw [Pr_eq_PrFrom]
  simp only [completenessExp, sessionExp, adaArg, bind_eq, OComp.bind]
  rw [PrFrom_query_miss rfl]
  refine le_trans
    (expect_uniform_le {x} _ 0 (fun r => PrFrom_le_one _ _ _) fun r hr => ?_) (by simp)
  rw [PrFrom_query_hit (Function.update_self _ _ _), PrFrom_pure, if_neg]
  have : x ≠ r := fun e => hr (by simp [e])
  simp [this]

/-- The adaptive chooser: first the all-zero string, then the string that the first proof showed. -/
def adaChooser :
    List (Digest lam × Digest lam × Bool) → {xw : Digest lam × Unit // (digR lam).rel () xw.1 xw.2}
  | [] => ⟨(fun _ => false, ()), trivial⟩
  | (_, π, _) :: _ => ⟨(π, ()), trivial⟩

/-- Among two honest sessions with x_2 := π_1 one is rejected, for every oracle. So the probability
is 1, not 2·α. (2·α < 1 needs λ ≥ 2.) -/
theorem adaptive_rejected (f : Oracle lam) :
    PrCoins f (sessionsLoop (digR lam) (adaArg lam) (adaChooser lam) () () 2 []) {b | b = false} =
      1 := by
  simp [PrCoins, sessionsLoop, adaArg, adaChooser, OComp.bind, OComp.run, prob_pure]

/-- In the terms of Adaptive.lean: an environment without any query forces α(0, 2) ≥ 1, while
completeness (ZKCP/Defs.lean, `HasCompletenessError`) holds with 2^-λ. -/
theorem adaptive_fails (α : ℕ → ℕ → ℝ≥0∞)
    (h : HasAdaptiveCompletenessError (digR lam) (adaArg lam) α) : 1 ≤ α 0 2 := by
  refine le_trans (le_of_eq ?_)
    (h () 0 2 (fun _ => .session (fun _ => false) () fun π _ => .session π () fun _ _ => .halt)
      (fun _ _ _ _ _ => trivial) (fun _ => ⟨trivial, fun _ _ => ⟨trivial, fun _ _ => trivial⟩⟩))
  have h1 : ∀ f : Oracle lam,
      PrCoins f (adaptiveExp (adaArg lam)
            (fun _ => .session (fun _ => false) () fun π _ => .session π () fun _ _ => .halt) () 2)
          {b | b = false} = 1 := by
    intro f
    simp [PrCoins, adaptiveExp, adaptiveLoop, adaArg, OComp.bind, OComp.run, prob_pure]
  rw [Pr, lintegral_congr h1]; simp

end Adaptive41
end ZKCP
