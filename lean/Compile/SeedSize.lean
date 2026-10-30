-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/SeedSize.lean: three lemmas for counting uniform samples.

  `length_filter_lt`             Of the numbers below N, min n N are below n.
  `muStd_le_one`, `muStd_salt`   The weight `muStd` (Compile/SeedStd.lean) of a uniform sample is at
                                 most 1; it is 0 for a sample with exactly 2^λ outcomes.

Limits: this file does not give the size of a key or the number of uniform samples of a committer.
-/
import Compile.SeedStd
import Iop.Ser

open Rom Iop

namespace Compile
namespace Seed

variable {I X : Type} {lam : ℕ}

/-! ## The three lemmas -/

theorem length_filter_lt (N n : ℕ) :
    ((List.range N).filter fun j => decide (j < n)).length = min n N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases h : N < n
    · simp only [List.filter_cons, List.filter_nil, decide_eq_true h,
        if_true, List.length_singleton]
      omega
    · simp only [List.filter_cons, List.filter_nil, decide_eq_false h, Bool.false_eq_true,
        if_false, List.length_nil]
      omega

variable (p : Params)




theorem muStd_le_one (k : ℕ) : muStd lam k ≤ 1 := by
  unfold muStd
  split_ifs <;> omega

theorem muStd_salt : muStd lam (2 ^ lam - 1) = 0 := if_pos (two_pow_sub_add lam)

end Seed
end Compile
