/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/Polynomial/Differential/ShiftedJet.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 6 of the 8 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import ThirdParty.ArkLib.Data.Polynomial.Differential.Basic

/-!
# Shifted-jet substitution

For a center `a` and a polynomial `P`, the shifted-jet substitution sends a differential
polynomial `Q(X, Y₀, ..., Y_d)` to

```text
Q(a + X, P(a + X), (D¹P)(a + X), ..., (DᵈP)(a + X)),
```

where `Dʲ` is the `j`-th Hasse derivative. It describes `Q(X, P, D¹P, ...)` in the displacement
coordinate `X - a`: by `taylor_differentialSpecialization` it is the Taylor translate of the
differential specialization of `Q` at `P`. Every statement holds over a commutative semiring.

## Main statements

* `shiftedJetSubstitution`: the substitution, with its generator images.
* `taylorAlgHom_comp_differentialSpecializationHom`: Taylor translation after differential
  specialization is the shifted-jet substitution.
* `taylor_differentialSpecialization`: the same identity applied to one polynomial.
* `coeff_zero_shiftedJetSubstitution`: the constant coefficient is the jet evaluation at the
  center.
-/

namespace PolynomialDifferential

noncomputable section

open Polynomial

variable {R : Type*} [CommSemiring R] {d : ℕ}

/-- The shifted-jet substitution at center `a`: `X ↦ a + X` and `Y_j ↦ (DʲP)(a + X)`, where
`Dʲ` is the `j`-th Hasse derivative. -/
def shiftedJetSubstitution (center : R) (P : R[X]) :
    DifferentialPolynomial R d →ₐ[R] R[X] :=
  MvPolynomial.aeval fun v : JetVariable d ↦ match v with
    | none => C center + X
    | some j => taylor center (hasseDeriv j.val P)

/-- The shifted-jet substitution sends `X` to `C center + X`. -/
@[simp]
theorem shiftedJetSubstitution_X (center : R) (P : R[X]) :
    shiftedJetSubstitution (d := d) center P (MvPolynomial.X none) = C center + X := by
  simp [shiftedJetSubstitution]

/-- The shifted-jet substitution sends `Y_j` to the Taylor translate at `center` of
`hasseDeriv j P`. -/
@[simp]
theorem shiftedJetSubstitution_Y (center : R) (P : R[X]) (j : Fin (d + 1)) :
    shiftedJetSubstitution center P (MvPolynomial.X (some j)) =
      taylor center (hasseDeriv j.val P) := by
  simp [shiftedJetSubstitution]

/-- Taylor translation by `a` after differential specialization at `P` is the shifted-jet
substitution at `a`. On `X` this is `taylor a X = X + C a`; on `Y_j` it is the definition. -/
theorem taylorAlgHom_comp_differentialSpecializationHom (center : R) (P : R[X]) :
    (taylorAlgHom center).comp (differentialSpecializationHom (d := d) P) =
      shiftedJetSubstitution center P := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rcases v with _ | j
  · simp [differentialSpecializationHom, add_comm]
  · simp [differentialSpecializationHom]

/-- The shifted-jet substitution of `Q` is the Taylor translate of `Q(X, P, D¹P, ..., DᵈP)`. -/
theorem taylor_differentialSpecialization (Q : DifferentialPolynomial R d) (center : R)
    (P : R[X]) :
    taylor center (differentialSpecialization Q P) = shiftedJetSubstitution center P Q := by
  rw [← taylorAlgHom_comp_differentialSpecializationHom, AlgHom.comp_apply,
    differentialSpecializationHom_apply]
  rfl

/-- The constant coefficient of the shifted-jet substitution is `Q` evaluated at the center and
the Hasse jet of `P` there. -/
theorem coeff_zero_shiftedJetSubstitution (Q : DifferentialPolynomial R d) (center : R)
    (P : R[X]) :
    (shiftedJetSubstitution center P Q).coeff 0 =
      jetEvaluation Q center (polynomialJet center P) := by
  rw [← taylor_differentialSpecialization, taylor_coeff_zero, eval_differentialSpecialization]

end

end PolynomialDifferential
