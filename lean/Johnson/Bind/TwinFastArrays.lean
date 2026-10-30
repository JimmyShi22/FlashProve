-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/TwinFastArrays.lean: the fast encoder's transform on arrays
(Johnson/Bind/TwinFast.lean) computes the values of a polynomial, if its factors are the points'
powers.

`butterflies` and `spread` work in place on an array of words. This file reads the words as elements
of the base field (`OnBytes.Slice.toF`) and proves, for any function z from positions to the field
and any tables of roots and of powers of 7:
   `getD_butterflies`: what one step leaves at each place of the array;
   `spread_spec`: if at each step k and block B the factor `twiddle roots sev k B` is z(x)^(2^k) at
      the positions x of the lower half of the block and its negative at those of the upper half
      (`Factors`), then, for an array that has the places off to off + 2^k - 1 and a block B within
      the first 2^a positions, `spread roots sev k B off A` leaves at the place off + i the value at
      z(B 2^k + i) of the polynomial whose 2^k coefficients stood at off, off + 1, ..; it changes no
      other place and not the array's size.
Limits. `Factors` is a hypothesis here: Johnson/Bind/TwinFastFactors.lean shows that the format's
points meet it. Nothing on bytes, and nothing on whether the words that are left are below p.

-/
import Johnson.Bind.TwinFast
import OnBytes.Slice.ProgField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Twin

open OnBytes (addF subF mulF normF)
open OnBytes.Slice (toF)

/-! ### Two entries set -/

theorem getD_set (A : Array UInt64) (i j : Nat) (v : UInt64) (hi : i < A.size) :
    (A.setIfInBounds i v).getD j 0 = if j = i then v else A.getD j 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h : j = i
  · subst h
    simp [hi]
  · have h' : ¬ i = j := fun e => h e.symm
    simp [h, h']

section
variable (A : Array UInt64) (p q : Nat) (v w : UInt64) (hp : p < A.size) (hq : q < A.size)
include hp hq

omit hp in
theorem getD_two_snd : ((A.setIfInBounds p v).setIfInBounds q w).getD q 0 = w := by
  rw [getD_set _ _ _ _ (by rw [Array.size_setIfInBounds]; exact hq), if_pos rfl]

theorem getD_two_fst (hne : p ≠ q) : ((A.setIfInBounds p v).setIfInBounds q w).getD p 0 = v := by
  rw [getD_set _ _ _ _ (by rw [Array.size_setIfInBounds]; exact hq), if_neg hne,
    getD_set _ _ _ _ hp, if_pos rfl]

theorem getD_two_other (x : Nat) (h1 : x ≠ p) (h2 : x ≠ q) :
    ((A.setIfInBounds p v).setIfInBounds q w).getD x 0 = A.getD x 0 := by
  rw [getD_set _ _ _ _ (by rw [Array.size_setIfInBounds]; exact hq), if_neg h2,
    getD_set _ _ _ _ hp, if_neg h1]

end

/-! ### One step -/

/-- What one step leaves, where j + n ≤ half and the array has the places below off + 2 half: at the
places off + i and off + half + i, for i from j to j + n - 1, the sum and the difference; elsewhere
what was there; and the size. -/
theorem getD_butterflies (t : UInt64) (off half : Nat) :
    ∀ (n j : Nat) (A : Array UInt64), j + n ≤ half → off + 2 * half ≤ A.size →
      (butterflies t off half n j A).size = A.size ∧
      (∀ i, j ≤ i → i < j + n → (butterflies t off half n j A).getD (off + i) 0 =
        addF (A.getD (off + i) 0) (mulF t (A.getD (off + half + i) 0))) ∧
      (∀ i, j ≤ i → i < j + n → (butterflies t off half n j A).getD (off + half + i) 0 =
        subF (A.getD (off + i) 0) (mulF t (A.getD (off + half + i) 0))) ∧
      (∀ x, (∀ i, j ≤ i → i < j + n → x ≠ off + i ∧ x ≠ off + half + i) →
        (butterflies t off half n j A).getD x 0 = A.getD x 0)
  | 0, j, A, _, _ =>
    ⟨rfl, fun i h1 h2 => absurd h2 (by omega), fun i h1 h2 => absurd h2 (by omega),
      fun _ _ => rfl⟩
  | n + 1, j, A, hj, hA => by
    have hp : off + j < A.size := by omega
    have hq : off + half + j < A.size := by omega
    have hne : off + j ≠ off + half + j := by omega
    generalize hlo : addF (A.getD (off + j) 0) (mulF t (A.getD (off + half + j) 0)) = lo
    generalize hhi : subF (A.getD (off + j) 0) (mulF t (A.getD (off + half + j) 0)) = hi
    have hstep : butterflies t off half (n + 1) j A = butterflies t off half n (j + 1)
        ((A.setIfInBounds (off + j) lo).setIfInBounds (off + half + j) hi) := by
      rw [← hlo, ← hhi]
      rfl
    have hsz :
        ((A.setIfInBounds (off + j) lo).setIfInBounds (off + half + j) hi).size = A.size := by
      rw [Array.size_setIfInBounds, Array.size_setIfInBounds]
    obtain ⟨i1, i2, i3, i4⟩ := getD_butterflies t off half n (j + 1)
      ((A.setIfInBounds (off + j) lo).setIfInBounds (off + half + j) hi) (by omega)
      (by rw [hsz]; exact hA)
    rw [hstep]
    refine ⟨i1.trans hsz, fun i h1 h2 => ?_, fun i h1 h2 => ?_, fun x hx => ?_⟩
    · by_cases e : i = j
      · subst e
        rw [i4 _ fun i' g1 g2 => ⟨by omega, by omega⟩, getD_two_fst A _ _ _ _ hp hq hne, hlo]
      · rw [i2 i (by omega) (by omega), getD_two_other A _ _ _ _ hp hq _ (by omega) (by omega),
          getD_two_other A _ _ _ _ hp hq _ (by omega) (by omega)]
    · by_cases e : i = j
      · subst e
        rw [i4 _ fun i' g1 g2 => ⟨by omega, by omega⟩, getD_two_snd A _ _ _ _ hq, hhi]
      · rw [i3 i (by omega) (by omega), getD_two_other A _ _ _ _ hp hq _ (by omega) (by omega),
          getD_two_other A _ _ _ _ hp hq _ (by omega) (by omega)]
    · have hj' := hx j (Nat.le_refl j) (by omega)
      rw [i4 x fun i' g1 g2 => hx i' (by omega) (by omega),
        getD_two_other A _ _ _ _ hp hq x hj'.1 hj'.2]

/-! ### The whole transform -/

/-- The factors are the points' powers: at the step k of the block B (a block of 2^(k + 1) positions
within the first 2^a; at a = 0 there is none and the condition asks nothing) the factor is
z(x)^(2^k) at the positions x of the block's lower half, and its negative at those of the upper
half. -/
def Factors (z : Nat → Cb.Gl.F) (roots sev : Array UInt64) (a : Nat) : Prop :=
  ∀ k B i, i < 2 ^ k → (B + 1) * 2 ^ (k + 1) ≤ 2 ^ a →
    z (2 * B * 2 ^ k + i) ^ 2 ^ k = toF (twiddle roots sev k B) ∧
      z ((2 * B + 1) * 2 ^ k + i) ^ 2 ^ k = -toF (twiddle roots sev k B)

/-- A polynomial of 2 h coefficients, cut in two halves, at a point x. -/
theorem sum_halves (c : Nat → Cb.Gl.F) (x : Cb.Gl.F) (h : Nat) :
    ∑ j ∈ Finset.range (h + h), c j * x ^ j =
      ∑ j ∈ Finset.range h, (c j + x ^ h * c (h + j)) * x ^ j := by
  rw [Finset.sum_range_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_add]
  ring

/-- **The transform computes the polynomial's values**, if the factors are the points' powers. -/
theorem spread_spec (z : Nat → Cb.Gl.F) (roots sev : Array UInt64) (a : Nat)
    (hF : Factors z roots sev a) :
    ∀ (k B off : Nat) (A : Array UInt64), off + 2 ^ k ≤ A.size → (B + 1) * 2 ^ k ≤ 2 ^ a →
      (spread roots sev k B off A).size = A.size ∧
      (∀ i, i < 2 ^ k → toF ((spread roots sev k B off A).getD (off + i) 0) =
        ∑ j ∈ Finset.range (2 ^ k), toF (A.getD (off + j) 0) * z (B * 2 ^ k + i) ^ j) ∧
      (∀ x, x < off ∨ off + 2 ^ k ≤ x → (spread roots sev k B off A).getD x 0 = A.getD x 0)
  | 0, B, off, A, _, _ => by
    refine ⟨rfl, fun i hi => ?_, fun _ _ => rfl⟩
    have hi0 : i = 0 := by
      rw [pow_zero] at hi
      omega
    subst hi0
    show toF (A.getD (off + 0) 0) = _
    rw [pow_zero, Finset.sum_range_one, pow_zero, mul_one]
  | k + 1, B, off, A, hA, hB => by
    generalize ht : twiddle roots sev k B = t
    have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
    generalize hh : 2 ^ k = h at hp
    rw [hp] at hA hB
    have hB1 : (2 * B + 1) * h ≤ 2 ^ a := by
      have e : (B + 1) * (h + h) = (2 * B + 1) * h + h := by ring
      omega
    have hB2 : (2 * B + 1 + 1) * h ≤ 2 ^ a := by
      have e : (B + 1) * (h + h) = (2 * B + 1 + 1) * h := by ring
      omega
    obtain ⟨b1, b2, b3, b4⟩ := getD_butterflies t off h h 0 A (by omega) (by omega)
    generalize hA1 : butterflies t off h h 0 A = A1 at b1 b2 b3 b4
    obtain ⟨s1, s2, s3⟩ := spread_spec z roots sev a hF k (2 * B) off A1
      (by rw [hh, b1]; omega) (by rw [hh]; exact hB1)
    generalize hA2 : spread roots sev k (2 * B) off A1 = A2 at s1 s2 s3
    obtain ⟨u1, u2, u3⟩ := spread_spec z roots sev a hF k (2 * B + 1) (off + h) A2
      (by rw [hh, s1, b1]; omega) (by rw [hh]; exact hB2)
    have hstep : spread roots sev (k + 1) B off A =
        spread roots sev k (2 * B + 1) (off + h) A2 := by
      rw [← hA2, ← hA1, ← ht, ← hh]
      rfl
    rw [hstep, hp]
    rw [hh] at s2 s3 u2 u3
    have hfac := fun i (hi : i < h) => hF k B i (by rw [hh]; exact hi)
      (by rw [pow_succ, hh]; have e : (B + 1) * (h * 2) = (B + 1) * (h + h) := by ring
          omega)
    rw [hh, ht] at hfac
    refine ⟨u1.trans (s1.trans b1), fun i hi => ?_, fun x hx => ?_⟩
    · by_cases hlow : i < h
      · have ex : B * (h + h) + i = 2 * B * h + i := by ring
        rw [u3 _ (Or.inl (by omega)), s2 i hlow, sum_halves, ex, (hfac i hlow).1]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' : j < h := Finset.mem_range.1 hj
        have eo : off + (h + j) = off + h + j := by omega
        rw [b2 j (Nat.zero_le j) (by omega), OnBytes.Slice.toF_addF, OnBytes.Slice.toF_mulF, eo]
      · have ei : off + i = off + h + (i - h) := by omega
        have ex : B * (h + h) + i = (2 * B + 1) * h + (i - h) := by
          have e1 : (2 * B + 1) * h = B * (h + h) + h := by ring
          omega
        rw [ei, u2 (i - h) (by omega), sum_halves, ex, (hfac (i - h) (by omega)).2]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' : j < h := Finset.mem_range.1 hj
        have eo : off + (h + j) = off + h + j := by omega
        rw [s3 _ (Or.inr (by omega)), b3 j (Nat.zero_le j) (by omega), OnBytes.Slice.toF_subF,
          OnBytes.Slice.toF_mulF, eo]
        ring
    · rw [u3 x (by omega), s3 x (by omega), b4 x fun i' _ g2 => ⟨by omega, by omega⟩]

end Bind.Twin

#print axioms Bind.Twin.sum_halves
#print axioms Bind.Twin.spread_spec
#print axioms Bind.Twin.getD_set
#print axioms Bind.Twin.getD_two_snd
#print axioms Bind.Twin.getD_two_fst
#print axioms Bind.Twin.getD_two_other
#print axioms Bind.Twin.getD_butterflies
