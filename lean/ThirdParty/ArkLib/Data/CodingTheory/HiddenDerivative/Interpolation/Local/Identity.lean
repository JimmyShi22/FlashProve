/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Local/Identity.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 11 of the 19 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import ThirdParty.ArkLib.Data.CodingTheory.HiddenDerivative.Substitution
import ThirdParty.ArkLib.Data.Polynomial.Differential.ShiftedJet
import ThirdParty.ArkLib.ToMathlib.Polynomial.HasseTaylor.Shift

/-!
# The local backward-error identity

The local substitutions of `ArkLib.Data.CodingTheory.HiddenDerivative.Substitution` are formal.
This file connects them to an actual polynomial `P`. Evaluate the local variables in `R[X]` by

```text
T ↦ X,   E ↦ error,   Y_(j+1) ↦ (D^(j+1) P)(center + X),
```

where `D^j` is the `j`-th Hasse derivative (`localPolynomialEvaluation`). Composing this
evaluation with the unscaled local substitution at `(center, received)` gives the shifted-jet
substitution `PolynomialDifferential.shiftedJetSubstitution center P` exactly when

```text
P(center + X) = received + sum_{j<d} (-1)^j X^(j+1) (D^(j+1) P)(center + X) + X · error,
```

the backward Taylor reconstruction of `P` at `center` with remainder `X · error`. At an agreement
point `P(center) = received`, the error `Polynomial.normalizedBackwardTaylorError center P d`
satisfies it, so the substitution followed by this evaluation recovers
`Q(center + X, P(center + X), ...)`, the Taylor translate of `Q(X, P, D¹P, ...)`. This is the
bridge from local coefficient constraints to multiplicity of `Q(X, P, D¹P, ...)` at `center`.

The same holds for the normalized substitution, with `X^(d+1) · reducedError` in place of
`X · error`. The canonical reduced error `reducedHiddenTaylorError center P d` is the quotient of
the unscaled error by `X^d`, which is exact over every commutative ring.

Both identities are instances of a statement about arbitrary evaluations: for a commutative
`R`-algebra `A`, evaluating after the unscaled substitution equals an evaluation `y` of the
differential variables if and only if `y` has the three generator values
(`aeval_comp_unscaledLocalSubstitution_eq_aeval_iff`).

## Main statements

* `aeval_comp_unscaledLocalSubstitution_eq_aeval_iff` and its normalized analogue: the
  algebra-valued criterion.
* `localPolynomialEvaluation_comp_unscaled_eq_iff`: over `R[X]`, the criterion is the backward
  Taylor reconstruction.
* `localPolynomialEvaluation_unscaled_backwardError`: at an agreement point, evaluation at the
  backward Taylor error after the unscaled substitution is the shifted-jet substitution.
* `localPolynomialEvaluation_comp_unscaled_eq_iff_error_eq`: at an agreement point, that error is
  the only one for which the identity holds.
* `localPolynomialEvaluation_normalized_reducedError`: the normalized form.

## References

* [Brakensiek, J., Chen, Y., Putterman, A., Zhang, Z., and Zheng, K. Z., *Algorithmic List
  Decoding of Reed–Solomon Codes up to Capacity in the Low-Rate Regime*][BCPZZ26],
  Equations (13)--(16).
-/

open PolynomialDifferential
open scoped Polynomial

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R] {d : ℕ}

/-! ### Evaluation in an arbitrary algebra -/

section Algebra

variable {A : Type*} [CommRing A] [Algebra R A]

/-- Under an evaluation `v` of the local variables, the correction becomes
`∑_{j<d} (-1)^j v(T)^(j+1) v(Y_(j+1))`. -/
theorem aeval_localCorrection (v : LocalVariable d → A) :
    aeval v (localCorrection (R := R) d) =
      ∑ j : Fin d, (-1 : A) ^ j.val * v (localT d) ^ (j.val + 1) * v (localY j) := by
  simp [localCorrection]

/-- Evaluating the local variables by `v` after the unscaled substitution at
`(center, received)` is the evaluation `y` of the differential variables exactly when
`y(X) = center + v(T)`, `y(Y₀) = received + v(localCorrection d) + v(T) v(E)`, and
`y(Y_(j+1)) = v(Y_(j+1))`. Both sides are algebra maps out of a polynomial ring, so they agree
exactly when they agree on the generators. -/
theorem aeval_comp_unscaledLocalSubstitution_eq_aeval_iff (center received : R)
    (v : LocalVariable d → A) (y : JetVariable d → A) :
    (aeval v).comp (unscaledLocalSubstitution d center received) = aeval y ↔
      y none = algebraMap R A center + v (localT d) ∧
        y (some 0) = algebraMap R A received + aeval v (localCorrection (R := R) d) +
          v (localT d) * v (localE d) ∧
        ∀ j : Fin d, y (some j.succ) = v (localY j) := by
  constructor
  · intro h
    have hv := fun u => (DFunLike.congr_fun h (X u)).symm
    simp only [AlgHom.coe_comp, Function.comp_apply, aeval_X] at hv
    refine ⟨?_, ?_, fun j => ?_⟩
    · simpa using hv none
    · simpa using hv (some 0)
    · simpa using hv (some j.succ)
  · rintro ⟨hX, hY₀, hY⟩
    refine MvPolynomial.algHom_ext fun u => ?_
    rcases u with _ | j
    · simp [hX]
    · refine Fin.cases ?_ (fun i => ?_) j
      · simp [hY₀]
      · simp [hY i]

end Algebra

/-! ### Evaluation at the jets of an actual polynomial -/

/-- The local values attached to a polynomial `P` at `center` and a chosen error: `T ↦ X`,
`E ↦ error`, and `Y_(j+1) ↦ (D^(j+1) P)(center + X)`. -/
def localPolynomialValues (center : R) (P error : R[X]) : LocalVariable d → R[X]
  | none => Polynomial.X
  | some none => error
  | some (some j) => Polynomial.taylor center (Polynomial.hasseDeriv (j.val + 1) P)

/-- Evaluate the local variables at the displacement `X`, a chosen error, and the translated
Hasse derivatives of `P`. -/
def localPolynomialEvaluation (center : R) (P error : R[X]) :
    LocalPolynomial R d →ₐ[R] R[X] :=
  aeval (localPolynomialValues center P error)

/-- `localPolynomialEvaluation` sends `T` to `X`. -/
@[simp]
theorem localPolynomialEvaluation_T (center : R) (P error : R[X]) :
    localPolynomialEvaluation (d := d) center P error (X (localT d)) = Polynomial.X := by
  simp [localPolynomialEvaluation, localPolynomialValues, localT]

/-- `localPolynomialEvaluation` sends `E` to `error`. -/
@[simp]
theorem localPolynomialEvaluation_E (center : R) (P error : R[X]) :
    localPolynomialEvaluation (d := d) center P error (X (localE d)) = error := by
  simp [localPolynomialEvaluation, localPolynomialValues, localE, localAux]

/-- `localPolynomialEvaluation` sends `Y_(j+1)` to the `(j + 1)`-th Hasse derivative of `P`, shifted
to `center`. -/
@[simp]
theorem localPolynomialEvaluation_Y (center : R) (P error : R[X]) (j : Fin d) :
    localPolynomialEvaluation center P error (X (localY j)) =
      Polynomial.taylor center (Polynomial.hasseDeriv (j.val + 1) P) := by
  simp [localPolynomialEvaluation, localPolynomialValues, localY]

/-- Under the jets of `P`, the formal correction becomes the moving Hasse sum
`∑_{j<d} (-1)^j X^(j+1) (D^(j+1) P)(center + X)`. -/
theorem localPolynomialEvaluation_localCorrection (center : R) (P error : R[X]) :
    localPolynomialEvaluation center P error (localCorrection d) =
      Polynomial.movingHasseSum center P d := by
  rw [localPolynomialEvaluation, aeval_localCorrection, Polynomial.movingHasseSum,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [localPolynomialValues, localT, localY, map_pow, map_neg, map_one]
  ring

/-- Evaluating at the jets of `P` after the unscaled substitution is the shifted-jet
substitution exactly when `P(center + X)` has the backward Taylor reconstruction with remainder
`X · error`. -/
theorem localPolynomialEvaluation_comp_unscaled_eq_iff (center received : R) (P error : R[X]) :
    (localPolynomialEvaluation center P error).comp
        (unscaledLocalSubstitution d center received) = shiftedJetSubstitution center P ↔
      Polynomial.taylor center P = Polynomial.C received +
        Polynomial.movingHasseSum center P d + Polynomial.X * error := by
  rw [localPolynomialEvaluation, shiftedJetSubstitution,
    aeval_comp_unscaledLocalSubstitution_eq_aeval_iff, ← localPolynomialEvaluation,
    localPolynomialEvaluation_localCorrection]
  simp [localPolynomialValues, localT, localE, localAux, localY]

/-- The unscaled backward-error identity: at an agreement point `P(center) = received`,
evaluating at the jets of `P` and the backward Taylor error after the unscaled substitution is
the shifted-jet substitution. The agreement hypothesis is needed: the constant coefficient of
`Y₀` after both maps is `received` on one side and `P(center)` on the other. -/
theorem localPolynomialEvaluation_comp_unscaled_backwardError (center received : R) (P : R[X])
    (hP : P.eval center = received) :
    (localPolynomialEvaluation center P
        (Polynomial.normalizedBackwardTaylorError center P d)).comp
        (unscaledLocalSubstitution d center received) =
      shiftedJetSubstitution center P :=
  (localPolynomialEvaluation_comp_unscaled_eq_iff center received P _).mpr
    (Polynomial.backwardTaylorReconstruction_of_eval_eq d hP)

/-- The unscaled backward-error identity applied to one differential polynomial `Q`: the result
is `Q(center + X, P(center + X), (D¹P)(center + X), ...)`, which is the Taylor translate of
`Q(X, P, D¹P, ...)` by `taylor_differentialSpecialization`. -/
theorem localPolynomialEvaluation_unscaled_backwardError (Q : DifferentialPolynomial R d)
    (center received : R) (P : R[X]) (hP : P.eval center = received) :
    localPolynomialEvaluation center P (Polynomial.normalizedBackwardTaylorError center P d)
        (unscaledLocalSubstitution d center received Q) =
      shiftedJetSubstitution center P Q :=
  DFunLike.congr_fun
    (localPolynomialEvaluation_comp_unscaled_backwardError center received P hP) Q

/-! ### The reduced error -/

end ReedSolomon.HiddenDerivative
