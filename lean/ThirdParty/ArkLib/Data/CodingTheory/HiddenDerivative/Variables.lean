/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/HiddenDerivative/Variables.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 18 of the 28 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Basic
import ThirdParty.MathlibBackport.Data.Finsupp.Weight

/-!
# Local variables and weights for hidden-derivative interpolation

After translating a differential polynomial to an agreement point, the hidden-derivative argument
works with polynomials in the following local variables:

* `localT d`, the displacement `T`;
* `localU d = localE d`, one auxiliary slot, called `U` before the hidden-derivative rewrite and
  `E` (the hidden error) afterwards;
* `localY j` for `j : Fin d`, the visible jet `Y_(j+1)`.

Two weights on these variables govern the local constraints. The contact weight gives `T`
weight one, `E` weight `d`, and every visible jet weight zero, so the monomial `T^i E^b Y^c` has
contact order `i + d * b`. The `T`-weight counts only the exponent of `T`. The jet weights
`localFirstJetWeight`, `localHigherJetWeight`, `localDerivativeJetWeight`, and
`localJetDegreeWeight` measure the visible jets.

For `d > 0`, `localExponentCoordinatesEquiv` identifies a local exponent with its `T`, `U`, and
`Y₁` degrees and the degree vector of `Y₂, ..., Y_d`. The weight lemmas
`weight_localFirstJetWeight`, `weight_localHigherJetWeight`, and `weight_localJetDegreeWeight`
compute the jet weights in these coordinates, and `localContactOrder_eq` computes the contact
order.

## References

* [Brakensiek, J., Chen, Y., Putterman, A., Zhang, Z., and Zheng, K. Z., *Algorithmic List
  Decoding of Reed–Solomon Codes up to Capacity in the Low-Rate Regime*][BCPZZ26], Section 3.
-/

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {d : ℕ}

/-- Variables of a local expansion: `none` is `T`, `some none` is the auxiliary slot, and
`some (some j)` is the visible jet `Y_(j+1)`. -/
abbrev LocalVariable (d : ℕ) := Option (Option (Fin d))

/-- Polynomials in `T`, one auxiliary variable, and the visible jets `Y₁, ..., Y_d`. -/
abbrev LocalPolynomial (R : Type*) [CommSemiring R] (d : ℕ) :=
  MvPolynomial (LocalVariable d) R

/-- The local displacement variable `T`. -/
def localT (d : ℕ) : LocalVariable d := none

/-- The shared auxiliary slot. -/
def localAux (d : ℕ) : LocalVariable d := some none

/-- The auxiliary slot before it is rewritten in terms of the hidden error. -/
abbrev localU (d : ℕ) : LocalVariable d := localAux d

/-- The auxiliary slot after the rewrite, where it holds the hidden error. -/
abbrev localE (d : ℕ) : LocalVariable d := localAux d

/-- The local variable for the visible jet `Y_(j+1)`. -/
def localY {d : ℕ} (j : Fin d) : LocalVariable d := some (some j)

/-- Contact weights: `T` has weight one, `E` has weight `d`, and visible jets have weight zero. -/
def localContactWeight (d : ℕ) : LocalVariable d → ℕ
  | none => 1
  | some none => d
  | some (some _) => 0

/-- The contact weight of `T` is `1`. -/
@[simp]
theorem localContactWeight_T (d : ℕ) : localContactWeight d (localT d) = 1 := rfl

/-- The contact weight of `E` is `d`. -/
@[simp]
theorem localContactWeight_E (d : ℕ) : localContactWeight d (localE d) = d := rfl

/-- The contact weight of a visible jet is `0`. -/
@[simp]
theorem localContactWeight_Y (j : Fin d) : localContactWeight d (localY j) = 0 := rfl

/-- The contact order of a local monomial: `T^i E^b Y^c` has contact order `i + d * b`. -/
def localContactOrder (d : ℕ) (e : LocalVariable d →₀ ℕ) : ℕ :=
  Finsupp.weight (localContactWeight d) e

/-- The weight that counts only the exponent of `T`. -/
def localTWeight (d : ℕ) : LocalVariable d → ℕ
  | none => 1
  | some _ => 0

/-- The `T`-weight of `T` is `1`. -/
@[simp]
theorem localTWeight_T (d : ℕ) : localTWeight d (localT d) = 1 := rfl

/-- The `T`-weight of `E` is `0`. -/
@[simp]
theorem localTWeight_E (d : ℕ) : localTWeight d (localE d) = 0 := rfl

/-- The `T`-weight of a visible jet is `0`. -/
@[simp]
theorem localTWeight_Y (j : Fin d) : localTWeight d (localY j) = 0 := rfl

/-! ### Jet weights and degrees -/

/-- The weight counting every variable except `T`, so that `e.weight (localJetDegreeWeight d)` is
the total degree of `e` in the auxiliary slot and the visible jets. -/
def localJetDegreeWeight (d : ℕ) : LocalVariable d → ℕ
  | none => 0
  | some _ => 1

/-- Contact order is the `T` exponent plus `d` times the `E` exponent. -/
theorem localContactOrder_eq (e : LocalVariable d →₀ ℕ) :
    localContactOrder d e = e (localT d) + d * e (localE d) := by
  simp [localContactOrder, Finsupp.weight_eq_sum, Fintype.sum_option, localContactWeight, localT,
    localE, localAux, mul_comm]

/-! ### Exponent coordinates -/

end ReedSolomon.HiddenDerivative
