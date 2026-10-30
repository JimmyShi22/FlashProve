-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/RealLaws.lean: the planner's arithmetic on numbers m * 2 ^ e, as far as a round's
verdict needs it: cutting, comparing, and adding and multiplying upward.

OnBytes/Params/Real.lean renders the integer arithmetic in which both programs derive sizes and
decide whether a round holds; it states no theorem. This file gives a number of that arithmetic its
value, a rational number, and proves: a cut lies on its side of the value; `le` says yes only of
numbers in that order; a sum and a product that are rounded up are at least the true sum and
product.

Main definition: `Binary.val`.
Main theorems, all in the namespace `Binary`: `val_cut_up`, `val_cut_down`, `le_sound`,
`val_add_up`, `val_mul_up`.
What is not claimed: that `le` says yes of all numbers in that order (OnBytes/Params/CmpLaws.lean
has the order that `cmp` returns). Nothing on how near a cut lies to the value. Nothing here on
`lt`, on a sum or a product that is rounded down, on `sub`, `div`, `pow`, `floor` or on `Bound`:
these are in OnBytes/Params/BoundLaws.lean. Nothing on `sqrt` and `ceil`. Nothing on the C++
arithmetic, of which OnBytes/Params/Real.lean is a rendering. For proofs only; the program, that is
the Lean port built from OnBytes/, does not import this file.

-/
import Mathlib.Tactic
import OnBytes.Params.Real

set_option autoImplicit false

namespace OnBytes.Params
namespace Binary

/-- The value of a number: m * 2 ^ e. -/
def val (a : Binary) : ℚ := (a.m : ℚ) * (2 : ℚ) ^ a.e

/-- A value is not negative. -/
theorem val_nonneg (a : Binary) : 0 ≤ a.val :=
  mul_nonneg (Nat.cast_nonneg _) (zpow_nonneg (by norm_num) _)

/-- The value of a natural number. -/
theorem val_ofNat (x : ℕ) : (ofNat x).val = x := by
  simp [val, ofNat]

/-- The value of a power of two. -/
theorem val_twoTo (n : ℤ) : (twoTo n).val = (2 : ℚ) ^ n := by
  simp [val, twoTo]

/-- The value of m * 2 ^ -k, as a quotient. -/
theorem val_neg (m k : ℕ) : (⟨m, -(k : ℤ)⟩ : Binary).val = (m : ℚ) / ((2 ^ k : ℕ) : ℚ) := by
  show (m : ℚ) * (2 : ℚ) ^ (-(k : ℤ)) = _
  rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
  push_cast
  rfl

/-- A shift of the exponent by a natural number. -/
theorem val_shift (m : ℕ) (e : ℤ) (s : ℕ) :
    ((m * 2 ^ s : ℕ) : ℚ) * (2 : ℚ) ^ e = (m : ℚ) * (2 : ℚ) ^ (e + s) := by
  rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
  push_cast
  ring

/-- A cut upward is at least the value. -/
theorem val_cut_up (a : Binary) : a.val ≤ (a.cut .up).val := by
  unfold cut
  dsimp only
  split
  · exact le_rfl
  · have h2 : (0 : ℚ) < (2 : ℚ) ^ a.e := zpow_pos (by norm_num) _
    generalize bitsOf a.m - realBits = s
    have hP : 0 < 2 ^ s := Nat.pos_of_ne_zero (by positivity)
    split
    · show (a.m : ℚ) * 2 ^ a.e ≤ ((a.m / 2 ^ s + 1 : ℕ) : ℚ) * 2 ^ (a.e + (s : ℤ))
      rw [← val_shift]
      refine mul_le_mul_of_nonneg_right ?_ h2.le
      have h1 : a.m < 2 ^ s * (a.m / 2 ^ s + 1) := Nat.lt_mul_div_succ a.m hP
      rw [Nat.mul_comm] at h1
      exact_mod_cast h1.le
    · rename_i hn
      have hz : a.m % 2 ^ s = 0 := by
        by_contra hne
        apply hn
        show (Dir.up == Dir.up && a.m % 2 ^ s != 0) = true
        simp [hne]
      show (a.m : ℚ) * 2 ^ a.e ≤ ((a.m / 2 ^ s : ℕ) : ℚ) * 2 ^ (a.e + (s : ℤ))
      rw [← val_shift]
      refine mul_le_mul_of_nonneg_right ?_ h2.le
      have h1 : a.m / 2 ^ s * 2 ^ s = a.m := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hz)
      exact_mod_cast h1.ge

/-- A cut downward is at most the value. -/
theorem val_cut_down (a : Binary) : (a.cut .down).val ≤ a.val := by
  unfold cut
  dsimp only
  split
  · exact le_rfl
  · have h2 : (0 : ℚ) < (2 : ℚ) ^ a.e := zpow_pos (by norm_num) _
    generalize bitsOf a.m - realBits = s
    have hle : a.m / 2 ^ s * 2 ^ s ≤ a.m := Nat.div_mul_le_self _ _
    have hf : (Dir.down == Dir.up && anyBelow a.m s) = false := rfl
    rw [if_neg (by rw [hf]; exact Bool.false_ne_true)]
    show ((a.m / 2 ^ s : ℕ) : ℚ) * 2 ^ (a.e + (s : ℤ)) ≤ (a.m : ℚ) * 2 ^ a.e
    rw [← val_shift]
    refine mul_le_mul_of_nonneg_right ?_ h2.le
    exact_mod_cast hle

/-- A product that is rounded up is at least the product. -/
theorem val_mul_up (a b : Binary) : a.val * b.val ≤ (a.mul b .up).val := by
  refine le_trans (le_of_eq ?_) (val_cut_up _)
  show (a.m : ℚ) * 2 ^ a.e * ((b.m : ℚ) * 2 ^ b.e) = ((a.m * b.m : ℕ) : ℚ) * 2 ^ (a.e + b.e)
  rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  push_cast
  ring

/-- The value with the exponent lowered to e. -/
theorem val_lower (m : ℕ) (x e : ℤ) (h : e ≤ x) :
    ((m * 2 ^ (x - e).toNat : ℕ) : ℚ) * (2 : ℚ) ^ e = (m : ℚ) * (2 : ℚ) ^ x := by
  rw [val_shift, Int.toNat_of_nonneg (by omega)]
  congr 2
  omega

/-- A sum that is rounded up is at least the sum. -/
theorem val_add_up (a b : Binary) : a.val + b.val ≤ (a.add b .up).val := by
  unfold add
  split
  · rename_i h
    have : a.m = 0 := by simpa [isZero] using h
    simp [val, this]
  · split
    · rename_i h
      have : b.m = 0 := by simpa [isZero] using h
      simp [val, this]
    · refine le_trans (le_of_eq ?_) (val_cut_up _)
      show (a.m : ℚ) * 2 ^ a.e + (b.m : ℚ) * 2 ^ b.e =
        ((a.m * 2 ^ (a.e - min a.e b.e).toNat + b.m * 2 ^ (b.e - min a.e b.e).toNat : ℕ) : ℚ) *
          2 ^ (min a.e b.e)
      rw [Nat.cast_add, add_mul, val_lower _ _ _ (min_le_left _ _),
        val_lower _ _ _ (min_le_right _ _)]

/-- A number lies below two to the number of its digits. -/
theorem lt_two_bits (m : ℕ) : (m : ℚ) < (2 : ℚ) ^ (bitsOf m : ℤ) := by
  rw [zpow_natCast]
  unfold bitsOf
  split
  · rename_i h
    have : m = 0 := by simpa using h
    simp [this]
  · exact_mod_cast Nat.lt_log2_self

/-- A number other than 0 is at least two to the number of its digits less one. -/
theorem two_bits_le (m : ℕ) (h : m ≠ 0) : (2 : ℚ) ^ ((bitsOf m : ℤ) - 1) ≤ (m : ℚ) := by
  have e : ((bitsOf m : ℤ) - 1) = (Nat.log2 m : ℤ) := by
    unfold bitsOf
    rw [if_neg (by simpa using h)]
    push_cast
    ring
  rw [e, zpow_natCast]
  exact_mod_cast Nat.log2_self_le h

/-- The value lies below two to the place of the top digit. -/
theorem val_lt_top (a : Binary) : a.val < (2 : ℚ) ^ a.top := by
  have h2 : (0 : ℚ) < (2 : ℚ) ^ a.e := zpow_pos (by norm_num) _
  show (a.m : ℚ) * 2 ^ a.e < 2 ^ ((bitsOf a.m : ℤ) + a.e)
  rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  exact mul_lt_mul_of_pos_right (lt_two_bits a.m) h2

/-- A value other than 0 is at least two to the place of the top digit less one. -/
theorem top_le_val (a : Binary) (h : a.m ≠ 0) : (2 : ℚ) ^ (a.top - 1) ≤ a.val := by
  have h2 : (0 : ℚ) < (2 : ℚ) ^ a.e := zpow_pos (by norm_num) _
  show (2 : ℚ) ^ ((bitsOf a.m : ℤ) + a.e - 1) ≤ (a.m : ℚ) * 2 ^ a.e
  have e : (bitsOf a.m : ℤ) + a.e - 1 = ((bitsOf a.m : ℤ) - 1) + a.e := by ring
  rw [e, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  exact mul_le_mul_of_nonneg_right (two_bits_le a.m h) h2.le

/-- `le` says yes only of numbers in that order. -/
theorem le_sound (a b : Binary) (h : a.le b = true) : a.val ≤ b.val := by
  unfold le cmp at h
  simp only [bne_iff_ne, ne_eq] at h
  split at h
  · split at h
    · rename_i _ ha
      have : a.m = 0 := by simpa [isZero] using ha
      rw [val, this]
      simpa using b.val_nonneg
    · exact absurd rfl h
  · rename_i hz
    have ha : a.m ≠ 0 := by
      intro h0
      apply hz
      simp [isZero, h0]
    have hb : b.m ≠ 0 := by
      intro h0
      apply hz
      simp [isZero, h0]
    split at h
    · split at h
      · rename_i _ hlt
        have h1 : (2 : ℚ) ^ a.top ≤ (2 : ℚ) ^ (b.top - 1) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        exact ((val_lt_top a).le.trans h1).trans (top_le_val b hb)
      · exact absurd rfl h
    · have h2 : ∀ e : ℤ, (0 : ℚ) < (2 : ℚ) ^ e := fun e => zpow_pos (by norm_num) _
      split at h
      · rename_i he
        have hn : a.m * 2 ^ (a.e - b.e).toNat ≤ b.m := Nat.compare_ne_gt.1 h
        show (a.m : ℚ) * 2 ^ a.e ≤ (b.m : ℚ) * 2 ^ b.e
        rw [← val_lower a.m a.e b.e he]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (h2 _).le
      · rename_i he
        have hn : a.m ≤ b.m * 2 ^ (b.e - a.e).toNat := Nat.compare_ne_gt.1 h
        show (a.m : ℚ) * 2 ^ a.e ≤ (b.m : ℚ) * 2 ^ b.e
        rw [← val_lower b.m b.e a.e (by omega)]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (h2 _).le

end Binary
end OnBytes.Params

#print axioms OnBytes.Params.Binary.val_cut_up
#print axioms OnBytes.Params.Binary.val_cut_down
#print axioms OnBytes.Params.Binary.val_mul_up
#print axioms OnBytes.Params.Binary.val_add_up
#print axioms OnBytes.Params.Binary.le_sound
