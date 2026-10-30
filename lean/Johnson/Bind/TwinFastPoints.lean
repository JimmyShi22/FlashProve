-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/TwinFastPoints.lean: the exponents of the format's points, for the fast encoder
(Johnson/Bind/TwinFast.lean).

By OnBytes/Slice/Points.lean the point of a position x in a code of length 2^a is 7 times a power of
one constant of order 2^32 (`OnBytes.Slice.rootW`: not `Bind.Twin.rootW` of Johnson/Bind/Twin.lean,
the root of the committer's hash tree, which this file does not import), with the exponent
`expFrom x a 0`: bit j of x gives 2^(31 - j). This file proves what the fast encoder needs of these
exponents, for a up to 32:
   `expFrom_add`, `expFrom_top`, `expFrom_congr`: the exponent of a run of bits is the sum over its
      parts, and hangs on these bits alone;
   `dvd_expFrom`: the bits below k give a multiple of 2^(32 - k);
   `two_pow_mul_expFrom`: 2^k times what the bits from k on give is what the bits of x div 2^k give;
   `rootW_pow_shift`: so the constant to the power 2^k times the exponent of x is the constant to
      the power of the exponent of x div 2^k: raising a point to the power 2^k forgets the k lowest
      bits;
   `rootW_pow_half_eq`: the constant to the power 2^31 is -1.
Limits. Arithmetic of exponents alone; nothing on arrays or bytes.

-/
import OnBytes.Slice.Points

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Twin

open OnBytes.Slice (rootW expFrom)

theorem expFrom_zero (x i : Nat) : expFrom x 0 i = 0 := rfl

theorem expFrom_succ (x n i : Nat) :
    expFrom x (n + 1) i =
      (if x.testBit i = true then 2 ^ (32 - (i + 1)) else 0) + expFrom x n (i + 1) := rfl

/-- The exponent of m + n bits is that of the first m plus that of the next n. -/
theorem expFrom_add (x : Nat) : ∀ (m n i : Nat),
    expFrom x (m + n) i = expFrom x m i + expFrom x n (i + m)
  | 0, n, i => by
    rw [Nat.zero_add, expFrom_zero, Nat.zero_add, Nat.add_zero]
  | m + 1, n, i => by
    have e : m + 1 + n = (m + n) + 1 := by omega
    have e2 : i + 1 + m = i + (m + 1) := by omega
    rw [e, expFrom_succ, expFrom_succ, expFrom_add x m n (i + 1), e2, Nat.add_assoc]

/-- The highest bit's share, taken off. -/
theorem expFrom_top (x n i : Nat) :
    expFrom x (n + 1) i =
      expFrom x n i + (if x.testBit (i + n) = true then 2 ^ (32 - (i + n + 1)) else 0) := by
  rw [expFrom_add x n 1 i, expFrom_succ, expFrom_zero, Nat.add_zero]

/-- The exponent hangs on the bits that it reads alone. -/
theorem expFrom_congr (x y : Nat) : ∀ (n i : Nat),
    (∀ j, i ≤ j → j < i + n → x.testBit j = y.testBit j) → expFrom x n i = expFrom y n i
  | 0, _, _ => rfl
  | n + 1, i, h => by
    rw [expFrom_succ, expFrom_succ, h i (Nat.le_refl i) (by omega),
      expFrom_congr x y n (i + 1) fun j h1 h2 => h j (by omega) (by omega)]

/-- The bits below k give a multiple of 2^(32 - k). -/
theorem dvd_expFrom (x k : Nat) : ∀ (n i : Nat), i + n ≤ k → 2 ^ (32 - k) ∣ expFrom x n i
  | 0, _, _ => Nat.dvd_zero _
  | n + 1, i, h => by
    rw [expFrom_succ]
    refine Nat.dvd_add ?_ (dvd_expFrom x k n (i + 1) (by omega))
    by_cases hb : x.testBit i = true
    · rw [if_pos hb]
      exact Nat.pow_dvd_pow 2 (by omega)
    · rw [if_neg hb]
      exact Nat.dvd_zero _

/-- 2^k times what the bits from k + i on give is what the bits of x div 2^k from i on give. -/
theorem two_pow_mul_expFrom (x k : Nat) : ∀ (n i : Nat), k + i + n ≤ 32 →
    2 ^ k * expFrom x n (k + i) = expFrom (x / 2 ^ k) n i
  | 0, _, _ => Nat.mul_zero _
  | n + 1, i, h => by
    have e : k + i + 1 = k + (i + 1) := by omega
    rw [expFrom_succ, expFrom_succ, Nat.mul_add, e, two_pow_mul_expFrom x k n (i + 1) (by omega),
      Nat.testBit_div_two_pow, Nat.add_comm i k]
    congr 1
    by_cases hb : x.testBit (k + i) = true
    · rw [if_pos hb, if_pos hb, ← Nat.pow_add]
      congr 1
      omega
    · rw [if_neg hb, if_neg hb, Nat.mul_zero]

/-- The constant to a multiple of 2^32 is 1. -/
theorem rootW_pow_mul_top (c : Nat) : rootW ^ (2 ^ 32 * c) = 1 := by
  rw [pow_mul, OnBytes.Slice.rootW_pow_top, one_pow]

/-- **Raising to the power 2^k forgets the k lowest bits.** -/
theorem rootW_pow_shift (x a k : Nat) (hk : k ≤ a) (ha : a ≤ 32) :
    rootW ^ (2 ^ k * expFrom x a 0) = rootW ^ expFrom (x / 2 ^ k) (a - k) 0 := by
  have e : a = k + (a - k) := by omega
  obtain ⟨c, hc⟩ := dvd_expFrom x k k 0 (by omega)
  have h2 : 2 ^ k * expFrom x (a - k) (k + 0) = expFrom (x / 2 ^ k) (a - k) 0 :=
    two_pow_mul_expFrom x k (a - k) 0 (by omega)
  have h3 : 2 ^ k * (2 ^ (32 - k) * c) = 2 ^ 32 * c := by
    rw [← Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega
  have h4 : expFrom x a 0 = expFrom x k 0 + expFrom x (a - k) (0 + k) := by
    conv_lhs => rw [e]
    exact expFrom_add x k (a - k) 0
  rw [h4, Nat.mul_add, hc, h3, Nat.zero_add, pow_add, rootW_pow_mul_top, one_mul]
  rw [Nat.add_zero] at h2
  rw [h2]

/-- The constant to the power 2^31 is -1. -/
theorem rootW_pow_half_eq : rootW ^ 2 ^ 31 = -1 := by
  have h : rootW ^ 2 ^ 31 * rootW ^ 2 ^ 31 = 1 := by
    rw [← pow_add]
    exact OnBytes.Slice.rootW_pow_top
  rcases mul_self_eq_one_iff.1 h with h1 | h1
  · exact absurd h1 OnBytes.Slice.rootW_pow_half
  · exact h1

end Bind.Twin

#print axioms Bind.Twin.expFrom_add
#print axioms Bind.Twin.expFrom_top
#print axioms Bind.Twin.expFrom_congr
#print axioms Bind.Twin.dvd_expFrom
#print axioms Bind.Twin.two_pow_mul_expFrom
#print axioms Bind.Twin.rootW_pow_mul_top
#print axioms Bind.Twin.rootW_pow_shift
#print axioms Bind.Twin.rootW_pow_half_eq
#print axioms Bind.Twin.expFrom_zero
#print axioms Bind.Twin.expFrom_succ
