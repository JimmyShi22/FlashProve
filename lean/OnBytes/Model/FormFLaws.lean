-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/FormFLaws.lean: a symbol has at most one reading as three small cells.

A symbol packs three cells of a matrix into one element of the base field: cell 0 + B * cell 1 +
B^2 * cell 2 modulo the prime p, with the radix B = radb (OnBytes/Model/FormF.lean). The smallness
test is meant to show that every cell lies strictly between -2 beta and 2 beta, where beta = 2^lbz.
This file proves that two triples of such cells with the same symbol are equal. The proof works on
the numbers themselves (lbz = 17, B = 2^20, p = 2^64 - 2^32 + 1). It does not cite the two
inequalities of FormF.lean, B >= 4 beta - 1 and (4 beta - 2) (1 + B + B^2) < p, which say why these
numbers suffice.

Main theorem: symbol_has_one_reading.

What this file does not claim. It says nothing about the verifier: not that the smallness test shows
the bound on the cells, and not that a committed symbol is read in this way. It is a statement about
integers. The file is not imported by the program.
-/
import OnBytes.Model.FormF

namespace OnBytes.Model

/-- The prime as an integer. -/
theorem prime_value : (pW.toNat : Int) = 18446744069414584321 := by decide

/-- A multiple of the prime that is smaller than the prime in absolute value is 0. -/
theorem small_multiple_of_prime (S : Int) (h : S % 18446744069414584321 = 0)
    (lo : -18446744069414584321 < S) (hi : S < 18446744069414584321) : S = 0 := by omega

/-- If d + B T = 0 and d is smaller than the radix B in absolute value, then d and T are 0. -/
theorem small_multiple_of_radix (d T : Int) (h : d + 1048576 * T = 0) (lo : -1048576 < d)
    (hi : d < 1048576) : d = 0 ∧ T = 0 := by omega

/-- Let a0, a1, a2 and b0, b1, b2 be integers strictly between -2 beta and 2 beta. If
a0 + B a1 + B^2 a2 and b0 + B b1 + B^2 b2 are congruent modulo the prime, the two triples are
equal. -/
theorem symbol_has_one_reading (a0 a1 a2 b0 b1 b2 : Int)
    (ha0 : -(2 * 2 ^ lbz : Int) < a0 ∧ a0 < 2 * 2 ^ lbz)
    (ha1 : -(2 * 2 ^ lbz : Int) < a1 ∧ a1 < 2 * 2 ^ lbz)
    (ha2 : -(2 * 2 ^ lbz : Int) < a2 ∧ a2 < 2 * 2 ^ lbz)
    (hb0 : -(2 * 2 ^ lbz : Int) < b0 ∧ b0 < 2 * 2 ^ lbz)
    (hb1 : -(2 * 2 ^ lbz : Int) < b1 ∧ b1 < 2 * 2 ^ lbz)
    (hb2 : -(2 * 2 ^ lbz : Int) < b2 ∧ b2 < 2 * 2 ^ lbz)
    (h : ((a0 + radb * a1 + radb * radb * a2) - (b0 + radb * b1 + radb * radb * b2)) %
      (pW.toNat : Int) = 0) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 := by
  rw [prime_value] at h
  simp only [lbz, radb, lrad] at *
  have zero := small_multiple_of_prime _ h (by omega) (by omega)
  have low := small_multiple_of_radix (a0 - b0) ((a1 - b1) + 1048576 * (a2 - b2)) (by omega)
    (by omega) (by omega)
  have mid := small_multiple_of_radix (a1 - b1) (a2 - b2) (by omega) (by omega) (by omega)
  omega

end OnBytes.Model
