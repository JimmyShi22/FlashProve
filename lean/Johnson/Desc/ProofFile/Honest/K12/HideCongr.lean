-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/HideCongr.lean: `hideAt k c` (Coins.lean), the coefficients of a
hiding polynomial in k variables taken from a function c of a number, reads c below 2 k + 1 alone.

  `hideAt_congr`   if c and c' agree below 2 k + 1, then `hideAt k c = hideAt k c'`
  `byName_congr`   the same for `byName` (Coins.lean): it reads its function at variables 1 to k and
                 degrees 1 and 2

By what. Induction on k, along the definition of `byName`.

Limits. Two lemmas on which numbers a definition reads. Nothing on how a value is sampled. Nothing
on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Coins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes.Slice (GE)

theorem byName_congr : ∀ (k : ℕ) (u u' : ℕ → ℕ → GE) (u0 u0' : GE), u0 = u0' →
    (∀ l t, 1 ≤ l → l ≤ k → 1 ≤ t → t ≤ 2 → u l t = u' l t) → byName k u u0 = byName k u' u0'
  | 0, _, _, _, _, h0, _ => by
    funext _
    exact h0
  | k + 1, u, u', u0, u0', h0, h => by
    funext i
    cases i with
    | inl t =>
      have ht : t.val < 2 := t.isLt
      exact h 1 (t.val + 1) (le_refl _) (by omega) (by omega) (by omega)
    | inr i =>
      exact congrFun (byName_congr k (fun l t => u (l + 1) t) (fun l t => u' (l + 1) t) u0 u0' h0
        fun l t h1 h2 h3 h4 => h (l + 1) t (by omega) (by omega) h3 h4) i

theorem hideAt_congr (k : ℕ) (c c' : ℕ → GE) (h : ∀ i, i < 2 * k + 1 → c i = c' i) :
    hideAt k c = hideAt k c' := by
  unfold hideAt
  refine byName_congr k _ _ _ _ (h _ (by omega)) fun l t h1 h2 h3 h4 => ?_
  show c (if l < k then 2 * (l - 1) + (t - 1) else 2 * (k - 1) + t) =
    c' (if l < k then 2 * (l - 1) + (t - 1) else 2 * (k - 1) + t)
  split <;> exact h _ (by omega)

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.byName_congr
#print axioms ProofFile.Honest.K12.Light.hideAt_congr
