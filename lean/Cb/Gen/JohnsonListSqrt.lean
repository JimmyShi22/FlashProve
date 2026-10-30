-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/JohnsonListSqrt.lean: the condition "below the Johnson radius" with its square root.

Cb/Gen/JohnsonList.lean writes the condition in natural numbers: `InJohnson n d e` is
n (n - d) < (n - e)^2 (n positions, distance d, radius e). Books write it as
e < n - sqrt (n (n - d)), that is, in fractions of n, e / n < 1 - sqrt (1 - d / n).

Main names:
  `Spec.inJohnson_iff_sqrt`: the two say the same, for all natural numbers n, d, e (also for d > n
    or e > n, where the subtractions of natural numbers give 0 and the real root of a negative
    number is 0 by Mathlib's convention). Proved here as `inJohnson_iff_sqrt`.

Why: this file is here so that a reader can check the condition against a book.

Limits: Nothing else uses this file. It does not state the form in fractions of n.
Terms: lean/GLOSSARY.md.
-/
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Cb.Gen.JohnsonList

set_option autoImplicit false

namespace Cb

/-- `InJohnson n d e` of Cb/Gen/JohnsonList.lean says that e is below the Johnson radius as the
books write it. -/
def Spec.inJohnson_iff_sqrt : Prop :=
  ∀ n d e : ℕ, InJohnson n d e ↔ (e : ℝ) < (n : ℝ) - Real.sqrt ((n : ℝ) * ((n : ℝ) - (d : ℝ)))

theorem inJohnson_iff_sqrt : Spec.inJohnson_iff_sqrt := by
  intro n d e
  unfold InJohnson
  rcases lt_or_ge e n with he | he
  · have hy : (0 : ℝ) < (n : ℝ) - (e : ℝ) := sub_pos.mpr (Nat.cast_lt.mpr he)
    have h1 : ((e : ℝ) < (n : ℝ) - Real.sqrt ((n : ℝ) * ((n : ℝ) - (d : ℝ)))) ↔
        (n : ℝ) * ((n : ℝ) - (d : ℝ)) < ((n : ℝ) - (e : ℝ)) ^ 2 := by
      rw [← Real.sqrt_lt' hy]
      constructor <;> intro h <;> linarith
    rw [h1]
    have h2 : ((n - e : ℕ) : ℝ) = (n : ℝ) - (e : ℝ) := Nat.cast_sub he.le
    rcases le_or_gt d n with hd | hd
    · have h3 : ((n - d : ℕ) : ℝ) = (n : ℝ) - (d : ℝ) := Nat.cast_sub hd
      rw [← h2, ← h3]
      exact_mod_cast Iff.rfl
    · have h3 : n - d = 0 := by omega
      have h4 : (n : ℝ) * ((n : ℝ) - (d : ℝ)) ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inl ⟨Nat.cast_nonneg n, sub_nonpos.mpr (Nat.cast_le.mpr hd.le)⟩)
      have h5 : 0 < n - e := by omega
      rw [h3, Nat.mul_zero]
      exact ⟨fun _ => lt_of_le_of_lt h4 (pow_pos hy 2), fun _ => pow_pos h5 2⟩
  · have h0 : n - e = 0 := by omega
    rw [h0]
    constructor
    · intro h
      exact absurd h (by simp)
    · intro h
      have h5 := Real.sqrt_nonneg ((n : ℝ) * ((n : ℝ) - (d : ℝ)))
      have h6 : (n : ℝ) ≤ (e : ℝ) := Nat.cast_le.mpr he
      linarith

end Cb
