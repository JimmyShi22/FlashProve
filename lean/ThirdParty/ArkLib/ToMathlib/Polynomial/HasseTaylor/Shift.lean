/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/ToMathlib/Polynomial/HasseTaylor/Shift.lean, commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13.
Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 23 of the 85 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
* Lemmas are called by their names in Lean 4.29.1 and this Mathlib: finsetSum_coeff became
  finset_sum_coeff (1 time); ite_eq_left became if_pos (1 time); ite_eq_right became if_neg (2
  times).
-/

import Mathlib.Algebra.Lie.OfAssociative
import ThirdParty.ArkLib.ToMathlib.Polynomial.HasseTaylor.FiniteJet

/-!
# Hasse--Taylor shifts and backward residuals

Characteristic-independent shift, vanishing, and moving-point backward Hasse identities. The
elementary shift increment quotient and the paper's truncation-dependent backward error are
different constructions and are named separately.

The moving-point API formalizes the finite form of the backward identity used as Equation (13)
and its normalized remainder from Equation (16) of ECCC TR26-164. For truncation order `d`,
correction term `j` has Hasse order `j + 1`, sign `(-1)^j`, and derivative evaluated at the
moving point `a + X`. The numerator is divisible by `X ^ (d + 1)` and its normalized error by
`X ^ d`.

## Main declarations

* `X_pow_dvd_taylor_iff`: truncated Hasse vanishing as divisibility.
* `hasseDeriv_taylor`: Hasse derivatives commute with Taylor shifts.
* `backwardTaylorReconstruction`: finite moving-point backward reconstruction.
* `X_pow_succ_dvd_backwardTaylorResidual`: divisibility of the unnormalized numerator.
* `X_pow_dvd_normalizedBackwardTaylorError`: divisibility after removing one factor of `X`.
* `X_mul_normalizedBackwardTaylorError`: the normalized-error identity itself.

## References

* Joshua Brakensiek, Yeyuan Chen, Aaron Putterman, Zihan Zhang, and Kai Zhe Zheng,
  *Algorithmic List Decoding of Reed--Solomon Codes up to Capacity in the Low-Rate Regime*,
  [ECCC TR26-164](https://eccc.weizmann.ac.il/report/2026/164/), 2026.
-/

namespace Polynomial

noncomputable section

section Semiring

variable {R : Type*} [Semiring R]

/-! ### Elementary shift quotients -/

end Semiring

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-! ### Hasse derivatives under shifts -/

/-- Hasse differentiation commutes with shifting the polynomial's input. -/
theorem hasseDeriv_taylor (p : R[X]) (a : R) (k : ℕ) :
    hasseDeriv k (taylor a p) = taylor a (hasseDeriv k p) := by
  ext n
  rw [hasseDeriv_coeff, taylor_coeff, taylor_coeff]
  have h := LinearMap.congr_fun (hasseDeriv_comp (R := R) n k) p
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h
  rw [h, eval_smul, Nat.choose_symm_add]
  simp [nsmul_eq_mul]

end CommSemiring

section Ring

variable {R : Type*} [Ring R]

/-! ### Shifted-difference congruences -/

end Ring

section CommRing

variable {R : Type*} [CommRing R]

/-! ### Scalar Hasse vanishing and root multiplicity -/

/-! ### Generic backward correction in shifted coordinates -/

private theorem Int.alternating_sum_choose_succ {n : ℕ} (hn : n ≠ 0) :
    (∑ j ∈ Finset.range n, (-1 : ℤ) ^ j * (n.choose (j + 1) : ℤ)) = 1 := by
  have h := Int.alternating_sum_range_choose_of_ne hn
  rw [Finset.sum_range_succ'] at h
  simp only [Nat.choose_zero_right, Int.natCast_one, pow_zero, one_mul] at h
  rw [show (∑ x ∈ Finset.range n, (-1 : ℤ) ^ (x + 1) * ↑(n.choose (x + 1))) =
      -(∑ x ∈ Finset.range n, (-1 : ℤ) ^ x * ↑(n.choose (x + 1))) by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ]
    ring] at h
  omega

private theorem alternating_sum_choose_succ {n : ℕ} (hn : n ≠ 0) :
    (∑ j ∈ Finset.range n, (-1 : R) ^ j * (n.choose (j + 1) : R)) = 1 := by
  have h := congrArg (Int.castRingHom R) (Int.alternating_sum_choose_succ hn)
  simpa using h

/-- First `d` moving-Hasse correction terms for a polynomial in shifted coordinates. -/
def backwardHasseSum (d : ℕ) (q : R[X]) : R[X] :=
  ∑ j ∈ Finset.range d,
    C ((-1 : R) ^ j) * (X ^ (j + 1) * hasseDeriv (j + 1) q)

/-- Through degree `d`, the correction sum reproduces every nonconstant coefficient. -/
theorem coeff_backwardHasseSum {d n : ℕ} (q : R[X]) (hn : n ≠ 0) (hnd : n ≤ d) :
    (backwardHasseSum d q).coeff n = q.coeff n := by
  rw [backwardHasseSum, finset_sum_coeff]
  rw [← Finset.sum_subset (Finset.range_mono hnd)]
  · have hterm : ∀ j ∈ Finset.range n,
        (C ((-1 : R) ^ j) * (X ^ (j + 1) * hasseDeriv (j + 1) q)).coeff n =
          ((-1 : R) ^ j * (n.choose (j + 1) : R)) * q.coeff n := by
      intro j hj
      rw [coeff_C_mul, coeff_X_pow_mul', if_pos]
      · rw [hasseDeriv_coeff]
        have hsub : n - (j + 1) + (j + 1) = n := by
          have := Finset.mem_range.mp hj
          omega
        rw [hsub]
        simp [mul_assoc]
      · have := Finset.mem_range.mp hj
        omega
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
      alternating_sum_choose_succ hn, one_mul]
  · intro j hjd hjn
    rw [coeff_C_mul, coeff_X_pow_mul', if_neg]
    · simp
    · have hjd' := Finset.mem_range.mp hjd
      have hjn' : ¬j < n := by simpa using hjn
      omega

/-- Numerator remaining after the constant and first `d` moving-Hasse terms are removed. -/
def backwardHasseResidual (d : ℕ) (q : R[X]) : R[X] :=
  q - C (q.coeff 0) - backwardHasseSum d q

/-- The generic backward numerator is divisible by `X ^ (d + 1)`. -/
theorem X_pow_succ_dvd_backwardHasseResidual (d : ℕ) (q : R[X]) :
    X ^ (d + 1) ∣ backwardHasseResidual d q := by
  rw [X_pow_dvd_iff]
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp [backwardHasseResidual, backwardHasseSum]
  · rw [backwardHasseResidual, coeff_sub, coeff_sub, coeff_C, if_neg hn0, sub_zero,
      coeff_backwardHasseSum q hn0 (by omega), sub_self]

/-- Backward residual after removing its guaranteed factor of `X`. -/
def normalizedBackwardHasseResidual (d : ℕ) (q : R[X]) : R[X] :=
  (backwardHasseResidual d q).divX

/-- Removing one `X` leaves a residual divisible by `X ^ d`. -/
theorem X_pow_dvd_normalizedBackwardHasseResidual (d : ℕ) (q : R[X]) :
    X ^ d ∣ normalizedBackwardHasseResidual d q := by
  rw [X_pow_dvd_iff]
  intro n hn
  rw [normalizedBackwardHasseResidual, coeff_divX]
  exact X_pow_dvd_iff.mp (X_pow_succ_dvd_backwardHasseResidual d q) (n + 1) (by omega)

/-- Multiplication by `X` reconstructs the generic backward numerator. -/
theorem X_mul_normalizedBackwardHasseResidual (d : ℕ) (q : R[X]) :
    X * normalizedBackwardHasseResidual d q = backwardHasseResidual d q := by
  have hzero := X_pow_dvd_iff.mp (X_pow_succ_dvd_backwardHasseResidual d q) 0 (by omega)
  simpa only [normalizedBackwardHasseResidual, hzero, C_0, add_zero] using
    X_mul_divX_add (backwardHasseResidual d q)

/-! ### Moving-point backward reconstruction -/

/-- Paper-facing correction sum. Derivatives are evaluated at moving point `a + X`. -/
def movingHasseSum (a : R) (p : R[X]) (d : ℕ) : R[X] :=
  ∑ j ∈ Finset.range d,
    C ((-1 : R) ^ j) * (X ^ (j + 1) * taylor a (hasseDeriv (j + 1) p))

@[simp]
theorem movingHasseSum_zero (a : R) (d : ℕ) : movingHasseSum a 0 d = 0 := by
  simp [movingHasseSum]

/-- Moving derivatives of `p` are ordinary Hasse derivatives of its Taylor shift. -/
theorem movingHasseSum_eq_backwardHasseSum (a : R) (p : R[X]) (d : ℕ) :
    movingHasseSum a p d = backwardHasseSum d (taylor a p) := by
  apply Finset.sum_congr rfl
  intro j _
  rw [hasseDeriv_taylor]

/-- Numerator left by the finite paper-facing moving-Hasse correction sum. -/
def backwardTaylorResidual (a : R) (p : R[X]) (d : ℕ) : R[X] :=
  taylor a p - C (p.eval a) - movingHasseSum a p d

@[simp]
theorem backwardTaylorResidual_zero (a : R) (d : ℕ) : backwardTaylorResidual a 0 d = 0 := by
  simp [backwardTaylorResidual]

/-- The paper-facing residual is the generic residual applied to the shifted polynomial. -/
theorem backwardTaylorResidual_eq (a : R) (p : R[X]) (d : ℕ) :
    backwardTaylorResidual a p d = backwardHasseResidual d (taylor a p) := by
  rw [backwardTaylorResidual, backwardHasseResidual, movingHasseSum_eq_backwardHasseSum,
    taylor_coeff_zero]

/-- Canonical normalized moving-point error; unlike the increment quotient, this depends on `d`. -/
def normalizedBackwardTaylorError (a : R) (p : R[X]) (d : ℕ) : R[X] :=
  (backwardTaylorResidual a p d).divX

/-- The normalized moving-point error is divisible by `X ^ d`. -/
theorem X_pow_dvd_normalizedBackwardTaylorError (a : R) (p : R[X]) (d : ℕ) :
    X ^ d ∣ normalizedBackwardTaylorError a p d := by
  rw [normalizedBackwardTaylorError, backwardTaylorResidual_eq]
  exact X_pow_dvd_normalizedBackwardHasseResidual d (taylor a p)

/-- Cleared-denominator form of Equation (16): multiplying the normalized moving error by `X`
recovers its numerator. -/
theorem X_mul_normalizedBackwardTaylorError (a : R) (p : R[X]) (d : ℕ) :
    X * normalizedBackwardTaylorError a p d = backwardTaylorResidual a p d := by
  rw [normalizedBackwardTaylorError, backwardTaylorResidual_eq]
  exact X_mul_normalizedBackwardHasseResidual d (taylor a p)

/-- Coefficients of the normalized error are shifted numerator coefficients. -/
theorem coeff_normalizedBackwardTaylorError (a : R) (p : R[X]) (d n : ℕ) :
    (normalizedBackwardTaylorError a p d).coeff n =
      (backwardTaylorResidual a p d).coeff (n + 1) := by
  rw [normalizedBackwardTaylorError, coeff_divX]

@[simp]
theorem normalizedBackwardTaylorError_zero_poly (a : R) (d : ℕ) :
    normalizedBackwardTaylorError a 0 d = 0 := by
  ext n
  simp [coeff_normalizedBackwardTaylorError]

/-- Finite moving-point backward reconstruction, with signs `+,-,+,...` from Hasse order one. -/
theorem backwardTaylorReconstruction (a : R) (p : R[X]) (d : ℕ) :
    taylor a p = C (p.eval a) + movingHasseSum a p d +
      X * normalizedBackwardTaylorError a p d := by
  calc
    taylor a p = C (p.eval a) + movingHasseSum a p d + backwardTaylorResidual a p d := by
      simp only [backwardTaylorResidual]
      ring
    _ = _ := by rw [X_mul_normalizedBackwardTaylorError]

/-- Reconstruction with a caller-supplied center value `y`. -/
theorem backwardTaylorReconstruction_of_eval_eq {a y : R} {p : R[X]} (d : ℕ)
    (h : p.eval a = y) :
    taylor a p = C y + movingHasseSum a p d + X * normalizedBackwardTaylorError a p d := by
  simpa only [h] using backwardTaylorReconstruction a p d

end CommRing

end

end Polynomial
