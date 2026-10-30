-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Tie/Sums.lean: a sum over the indices of a table of at most 2 ^ c rows, in which
entry j of row r has the index r + j * 2 ^ c, rewritten as a sum over rows and their entries.
Terms: the file uses none of the folder's terms. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file proves, over any commutative semiring.
  sum_range_mul   A sum over the numbers below a * b is the sum over j < b of the sums over r < a of
                  the summands at r + j * a.
  table_sum       Let rows ≤ 2 ^ c. Let the summand at index i be a weight W i times entry i / 2 ^ c
                  of row i % 2 ^ c, and 0 at the rows from "rows" on. Then the sum over the indices
                  below 2 ^ c * L is the sum over r < rows and j < L of W (r + j * 2 ^ c) * y r j.

How it fits. form_rows (Johnson/SendSim/At/Answers.lean) applies table_sum, to write the honest
sender's answers as the linear forms of the instance of the general model. That serves rowsExact and
rowsFresh through shownTie (Johnson/SendSim/At/Shown.lean).
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace OnBytes.SendSim

variable {K : Type} [CommSemiring K]

/-- A sum over the numbers below a * b is the sum over j < b of the sums over r < a of the summands
at r + j * a. -/
theorem sum_range_mul (a : ℕ) (f : ℕ → K) : ∀ b : ℕ,
    ∑ i ∈ Finset.range (a * b), f i = ∑ j ∈ Finset.range b, ∑ r ∈ Finset.range a, f (r + j * a)
  | 0 => by simp
  | b + 1 => by
    rw [Nat.mul_succ, Finset.sum_range_add, sum_range_mul a f b, Finset.sum_range_succ]
    refine congrArg _ (Finset.sum_congr rfl fun r _ => ?_)
    rw [Nat.add_comm, Nat.mul_comm]

/-- If rows ≤ 2 ^ c, the sum over the indices i below 2 ^ c * L of W i times entry i / 2 ^ c of row
i % 2 ^ c of y, with 0 at the rows from "rows" on, is the sum over r < rows and j < L of W (r + j *
2 ^ c) * y r j. -/
theorem table_sum (rows c L : ℕ) (hr : rows ≤ 2 ^ c) (W : ℕ → K) (y : ℕ → ℕ → K) :
    ∑ i ∈ Finset.range (2 ^ c * L),
        W i * (if i % 2 ^ c < rows then y (i % 2 ^ c) (i / 2 ^ c) else 0) =
      ∑ r ∈ Finset.range rows, ∑ j ∈ Finset.range L, W (r + j * 2 ^ c) * y r j := by
  have hp : 0 < 2 ^ c := Nat.two_pow_pos c
  rw [sum_range_mul, Finset.sum_comm]
  rw [← Finset.sum_subset (Finset.range_subset_range.2 hr)]
  · refine Finset.sum_congr rfl fun r hr' => Finset.sum_congr rfl fun j _ => ?_
    have h1 : r < rows := Finset.mem_range.1 hr'
    have h2 : r < 2 ^ c := lt_of_lt_of_le h1 hr
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2, Nat.add_mul_div_right _ _ hp,
      Nat.div_eq_of_lt h2, Nat.zero_add, if_pos h1]
  · intro r hr1 hr2
    refine Finset.sum_eq_zero fun j _ => ?_
    have h2 : r < 2 ^ c := Finset.mem_range.1 hr1
    have h1 : ¬ r < rows := fun h => hr2 (Finset.mem_range.2 h)
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2, if_neg h1, mul_zero]

end OnBytes.SendSim

#print axioms OnBytes.SendSim.sum_range_mul
#print axioms OnBytes.SendSim.table_sum
