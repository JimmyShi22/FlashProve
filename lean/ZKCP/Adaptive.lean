-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  ZKCP/Adaptive.lean -- completeness against an adaptive environment. Not part of the definitions of
  ZKCP/Defs.lean.

  The claim of `sessions_of_refined` (ZKCP/Basic.lean), for N pairs (x_j, w_j) chosen adaptively,
  is Pr[ some honest π_j is rejected ] ≤ α_C + N·α_P; the work that this protocol builds on
  (lean/CREDITS.md, "Further work") derives it from refined completeness
  (`HasRefinedCompletenessError`). Two facts make a notion of its own useful: the refined form is
  out of reach for a scheme whose failures depend on the oracle, over a large set of instances
  (ZKCP/Sep41.lean: one scheme, over an infinite set of instances), and completeness alone does
  not give the claim (ZKCP/Adaptive41.lean). This file states the conclusion of that claim as a
  property:
    CEnv                           the environment: a tree that queries f, draws coins, and names
                                   the next pair (x, w); it is given ivk, every honest proof and V's
                                   bit on it; it is not given isk
    HasAdaptiveCompletenessError   for every index i, every t-query environment that names valid
                                   pairs only, and every N:
                                   Pr[ some honest proof is rejected ] ≤ α(t, N)
  and relates it to `HasCompletenessError` and `HasRefinedCompletenessError`:
    completeness_of_adaptive       it implies `HasCompletenessError`, with α(0, 1)
    adaptive_of_refined            `HasRefinedCompletenessError` implies it, with α_C + N·α_P:
                                   `sessions_of_refined`, for these environments
  Definitions are cited by their names in ZKCP/Defs.lean.
-/
import ZKCP.Basic

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ZKCP

/-- The environment. It halts, queries the oracle, draws coins, or names the next pair (x, w); it
then receives the honest proof and V's bit on it. So each choice may depend on ivk, on all earlier
proofs and bits, on its queries and on its coins. It never sees isk. -/
inductive CEnv (lam : ℕ) (X W Pf : Type) : Type
  | halt : CEnv lam X W Pf
  | query (q : Str) (k : Digest lam → CEnv lam X W Pf) : CEnv lam X W Pf
  | sample (n : ℕ) (k : Fin (n + 1) → CEnv lam X W Pf) : CEnv lam X W Pf
  | session (x : X) (w : W) (k : Pf → Bool → CEnv lam X W Pf) : CEnv lam X W Pf

section Defs
variable {lam : ℕ} {I X W PP IVK ISK Pf : Type}

/-- at most t queries, on every path -/
def CEnv.QueryBound : CEnv lam X W Pf → ℕ → Prop
  | .halt, _ => True
  | .query _ _, 0 => False
  | .query _ k, t + 1 => ∀ r, (k r).QueryBound t
  | .sample _ k, t => ∀ r, (k r).QueryBound t
  | .session _ _ k, t => ∀ π b, (k π b).QueryBound t

/-- every pair that the environment names is allowed, whatever it has received -/
def CEnv.Valid (ok : X → W → Prop) : CEnv lam X W Pf → Prop
  | .halt => True
  | .query _ k => ∀ r, (k r).Valid ok
  | .sample _ k => ∀ r, (k r).Valid ok
  | .session x w k => ok x w ∧ ∀ π b, (k π b).Valid ok

variable (R : IndexedRelation I X W PP) (A : Arg lam I X W IVK ISK Pf)

/-- The sessions on one key; n is the number of sessions still allowed. The result is true if V has
accepted every proof. -/
def adaptiveLoop (ivk : IVK) (isk : ISK) : CEnv lam X W Pf → ℕ → OComp lam Bool
  | .halt, _ => .pure true
  | .query q k, n => .query q fun r => adaptiveLoop ivk isk (k r) n
  | .sample m k, n => .sample m fun r => adaptiveLoop ivk isk (k r) n
  | .session _ _ _, 0 => .pure true
  | .session x w k, n + 1 =>
      (A.P isk x w).bind fun π => (A.V ivk x π).bind fun b =>
        (adaptiveLoop ivk isk (k π b) n).bind fun rest => .pure (b && rest)

/-- The experiment: an honest key for i, then at most N honest sessions on pairs that the
environment chooses. -/
def adaptiveExp (E : IVK → CEnv lam X W Pf) (i : I) (N : ℕ) : OComp lam Bool :=
  (A.C i).bind fun key => adaptiveLoop A key.1 key.2 (E key.1) N

/-- Completeness against an adaptive environment (our notion for the claim of `sessions_of_refined`,
ZKCP/Basic.lean): for each index i, all t and N, and each environment E (it may depend on i,
and
is handed ivk) that makes at most t queries and chooses only pairs valid for i: the probability that
V rejects at least one of the first N honest proofs is at most α(t, N). -/
def HasAdaptiveCompletenessError (α : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (i : I) (t N : ℕ) (E : IVK → CEnv lam X W Pf), (∀ ivk, (E ivk).QueryBound t) →
    (∀ ivk, (E ivk).Valid (R.rel i)) → Pr (adaptiveExp A E i N) (fun _ => {b | b = false}) ≤ α t N

end Defs

section Facts
variable {lam : ℕ} {I X W PP IVK ISK Pf : Type}
variable {R : IndexedRelation I X W PP} {A : Arg lam I X W IVK ISK Pf}

/-- It implies completeness (`HasCompletenessError`): one session on a pair that is fixed in
advance. -/
theorem completeness_of_adaptive {α : ℕ → ℕ → ℝ≥0∞} (h : HasAdaptiveCompletenessError R A α) :
    HasCompletenessError R A (α 0 1) := by
  intro i x w hR
  refine le_trans (le_of_eq ?_)
    (h i 0 1 (fun _ => .session x w fun _ _ => .halt)
      (fun _ _ _ => trivial) (fun _ => ⟨hR, fun _ _ => trivial⟩))
  unfold Pr PrCoins
  refine lintegral_congr fun f => ?_
  simp only [completenessExp, sessionExp, adaptiveExp, adaptiveLoop, bind_eq, OComp.bind,
    Bool.and_true, run_bind, prob_bind, OComp.run, expect_prob_pure]

/-- On a key that is not bad, for every valid environment, n sessions fail with probability at most
n·α_P; f is fixed. -/
theorem adaptiveLoop_good {αP : ℝ≥0∞} {i : I} (f : Oracle lam) (key : IVK × ISK)
    (hg : key ∉ badKeys R A αP i f) (E : CEnv lam X W Pf) :
    E.Valid (R.rel i) →
    ∀ n : ℕ, prob ((adaptiveLoop A key.1 key.2 E n).run f) {b | b = false} ≤ n * αP := by
  induction E with
  | halt => intro _ n; simp [adaptiveLoop, OComp.run, prob_pure]
  | query q k ih => intro hv n; simp only [adaptiveLoop, OComp.run]; exact ih _ (hv _) n
  | sample m k ih =>
    intro hv n
    simp only [adaptiveLoop, OComp.run, prob_bind]
    exact expect_le_of_le _ fun r => ih r (hv r) n
  | session x w k ih =>
    intro hv n
    cases n with
    | zero => simp [adaptiveLoop, OComp.run, prob_pure]
    | succ n =>
      have hs : PrCoins f (sessionExp A key.1 key.2 x w) {b | b = false} ≤ αP := by
        by_contra hc
        exact hg ⟨x, w, hv.1, not_le.1 hc⟩
      simp only [PrCoins, sessionExp, bind_eq, run_bind, prob_bind] at hs
      simp only [adaptiveLoop, run_bind, prob_bind, OComp.run]
      have step : ∀ (π : Pf) (b : Bool),
          (expect ((adaptiveLoop A key.1 key.2 (k π b) n).run f) fun rest =>
              prob (PMF.pure (b && rest)) {b | b = false}) ≤
            prob (PMF.pure b) {b | b = false} + n * αP := by
        intro π b
        cases b with
        | false => simp [prob_pure, expect_const]
        | true =>
          refine le_trans (le_of_eq ?_) (le_trans (ih π true (hv.2 π true) n) le_add_self)
          simp only [Bool.true_and, expect_prob_pure]
      refine le_trans (expect_mono _ fun π => expect_mono _ fun b => step π b) ?_
      simp only [expect_add, expect_const, expect_prob_pure]
      calc _ ≤ αP + n * αP := by gcongr
        _ = ((n + 1 : ℕ) : ℝ≥0∞) * αP := by push_cast; ring

/-- The claim of `sessions_of_refined` (ZKCP/Basic.lean): for every i and adaptively chosen pairs
(x_j, w_j), j ≤ N, with (i, x_j, w_j) ∈ R, the bound Pr[ some honest π_j is rejected ] ≤ α_C +
N·α_P, for environments of any query budget. The hypothesis is `HasRefinedCompletenessError` with
(α_C, α_P). -/
theorem adaptive_of_refined {αC αP : ℝ≥0∞} (h : HasRefinedCompletenessError R A αC αP) :
    HasAdaptiveCompletenessError R A fun _ N => αC + N * αP := by
  intro i t N E _ hv
  have key : ∀ f : Oracle lam, PrCoins f (adaptiveExp A E i N) {b | b = false} ≤
      PrCoins f (A.C i) (badKeys R A αP i f) + N * αP := by
    intro f
    simp only [PrCoins, adaptiveExp, run_bind, prob_bind]
    exact expect_le_prob_add _ _ _ _ (fun _ => prob_le_one _ _) fun key hb =>
      adaptiveLoop_good f key hb (E key.1) (hv key.1) N
  calc Pr (adaptiveExp A E i N) (fun _ => {b | b = false})
      ≤ ∫⁻ f, (PrCoins f (A.C i) (badKeys R A αP i f) + N * αP) ∂(U lam) := lintegral_mono key
    _ = Pr (A.C i) (fun f => badKeys R A αP i f) + N * αP := by
        rw [lintegral_add_right _ measurable_const]; simp [Pr]
    _ ≤ αC + N * αP := by gcongr; exact h i

/-- The property passes to larger bounds: if α ≤ α' at all (t, N), it holds with α'. -/
theorem HasAdaptiveCompletenessError.mono
    {α α' : ℕ → ℕ → ℝ≥0∞} (h : HasAdaptiveCompletenessError R A α) (hα : ∀ t N, α t N ≤ α' t N) :
    HasAdaptiveCompletenessError R A α' :=
  fun i t N E hq hv => (h i t N E hq hv).trans (hα t N)

end Facts
end ZKCP
