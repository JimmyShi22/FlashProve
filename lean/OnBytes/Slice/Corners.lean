-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/Corners.lean: different indices have different bits.

An entry of a table is named by a number, and the number's bits are a corner of a cube. Three plain
facts on natural numbers say that this naming loses nothing.

Main theorems.
 `testBit_inj`       two numbers below 2^c with the same c lowest bits are equal.
 `idx_inj`           a row below 2^aR and a place are determined by row + 2^aR * place.
 `le_two_pow_clog`   a block of 2^(clog n) rows has room for n rows (Fmt/M2Types.lean: `clog`).

Not claimed. That `clog n` is the least such exponent.
-/
import Fmt.M2Types

set_option autoImplicit false

namespace OnBytes.Slice

/-- Two numbers below 2^c with the same c lowest bits are equal. -/
theorem testBit_inj (c : Nat) {x y : Nat} (hx : x < 2 ^ c) (hy : y < 2 ^ c)
    (h : ∀ t : Fin c, x.testBit t.val = y.testBit t.val) : x = y := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < c
  · exact h ⟨i, hi⟩
  · have hc : 2 ^ c ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hi)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx hc),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy hc)]

/-- The map from (row, place) to row + 2^aR * place is injective on rows below 2^aR. -/
theorem idx_inj (aR : Nat) {r r' p p' : Nat} (hr : r < 2 ^ aR) (hr' : r' < 2 ^ aR)
    (h : r + 2 ^ aR * p = r' + 2 ^ aR * p') : r = r' ∧ p = p' := by
  have hrow : r = r' :=
    calc r = (r + 2 ^ aR * p) % 2 ^ aR := by
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
      _ = (r' + 2 ^ aR * p') % 2 ^ aR := by rw [h]
      _ = r' := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr']
  subst hrow
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos aR) (Nat.add_left_cancel h)⟩

/-- A block of 2^(clog n) rows has room for n rows. -/
theorem le_two_pow_clog (n : Nat) : n ≤ 2 ^ Fmt.M2.clog n := by
  unfold Fmt.M2.clog
  by_cases h : n ≤ 1
  · rw [if_pos h]
    exact h
  · rw [if_neg h]
    have h1 : n - 1 < 2 ^ (Nat.log2 (n - 1) + 1) := Nat.lt_log2_self
    exact Nat.le_of_pred_lt h1

end OnBytes.Slice

#print axioms OnBytes.Slice.testBit_inj
#print axioms OnBytes.Slice.idx_inj
#print axioms OnBytes.Slice.le_two_pow_clog
