-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/NoWorkRatesNum.lean: the comparisons of natural numbers behind the exponent 128.






OnBytes/Slice/RatesNum.lean brings "the share of bad challenge values (there: written verifier
messages) of a round is at most 2^-k" to one inequality between natural numbers. This file proves it
at k = 128 for a round that draws one element.


Main theorem.
 `nw_elem_num`    a round that draws one element, with a count of at most 2^32.








The size of the field is a variable q with 2^191 ≤ q. Every comparison that is left to
evaluation is a theorem of its own between numerals (`nw_lit_elem`), with no variable
and no field in it.




What this file does not claim: that these are the sizes, counts or numbers of hash blocks of any
protocol, or that the radii are right for any code. It holds arithmetic alone.
-/
import OnBytes.Slice.RatesMix

set_option autoImplicit false

namespace OnBytes.Slice

/-! ### Comparisons between numerals -/

/-- One element, five hash blocks, a count of 2^32. -/
theorem nw_lit_elem : (2 ^ 128 + 1) ^ 5 * 2 ^ 32 * 2 ^ 128 ≤ (2 ^ 128) ^ 5 * 2 ^ 191 * 2 ^ 0 := by
  decide +kernel

/-! ### In variables -/

/-- A larger radius leaves fewer positions: n - r - 1 to a power falls as r grows. -/
theorem far_pow_le (n r0 r t : ℕ) (hr : r0 ≤ r) : (n - r - 1) ^ t ≤ (n - r0 - 1) ^ t :=
  Nat.pow_le_pow_left (Nat.sub_le_sub_right (Nat.sub_le_sub_left hr n) 1) t

/-- The left side of `mix_num` grows with the factor X of q. -/
theorem mix_mono (A X X0 Y Z T q : ℕ) (hX : X ≤ X0) :
    A * (X * q + Y * Z) * T ≤ A * (X0 * q + Y * Z) * T :=
  Nat.mul_le_mul_right T
    (Nat.mul_le_mul_left A (Nat.add_le_add_right (Nat.mul_le_mul_right q hX) (Y * Z)))

/-- The larger of two numbers of which the second is the larger, times D. -/
theorem max_mul_le (A B D R : ℕ) (h1 : A ≤ B) (h2 : B * D ≤ R) : max A B * D ≤ R :=
  (Nat.mul_le_mul_right D (max_le h1 le_rfl)).trans h2

/-- One element, five hash blocks, no test bit, a count of at most 2^32. -/
theorem nw_elem_num (e q : ℕ) (he : e ≤ 2 ^ 32) (hq : 2 ^ 191 ≤ q) :
    (2 ^ 128 + 1) ^ 5 * e * 2 ^ 128 ≤ (2 ^ 128) ^ 5 * q * 2 ^ 0 :=
  calc (2 ^ 128 + 1) ^ 5 * e * 2 ^ 128 ≤ (2 ^ 128 + 1) ^ 5 * 2 ^ 32 * 2 ^ 128 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ he)
    _ ≤ (2 ^ 128) ^ 5 * 2 ^ 191 * 2 ^ 0 := nw_lit_elem
    _ ≤ (2 ^ 128) ^ 5 * q * 2 ^ 0 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hq)

end OnBytes.Slice

#print axioms OnBytes.Slice.nw_lit_elem
#print axioms OnBytes.Slice.far_pow_le
#print axioms OnBytes.Slice.mix_mono
#print axioms OnBytes.Slice.max_mul_le
#print axioms OnBytes.Slice.nw_elem_num
