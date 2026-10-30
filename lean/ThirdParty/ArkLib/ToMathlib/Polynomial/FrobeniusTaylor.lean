/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/ToMathlib/Polynomial/FrobeniusTaylor.lean, commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13.
Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 2 of the 3 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Taylor expansion of a Frobenius pullback

Let `R` have exponential characteristic `p` and let `q = p ^ e`. Then `(X + C t) ^ q = X ^ q +
C (t ^ q)`, so translating the pullback `expand R q P` by `t` is the pullback of `P` translated by
`t ^ q`. Consequently the Taylor coefficients of `expand R q P` at `t` vanish at indices not
divisible by `q`, and the coefficient at `q * r` is the `r`-th Hasse derivative of `P` evaluated at
`t ^ q`.

## Main statements

* `Polynomial.taylor_expand_expChar_pow`: `taylor t (expand R (p ^ e) P) =
  expand R (p ^ e) (taylor (t ^ p ^ e) P)`.
* `Polynomial.coeff_taylor_expand_expChar_pow_mul` and
  `Polynomial.coeff_taylor_expand_expChar_pow_eq_zero`: the Taylor coefficients of a pullback.
-/

namespace Polynomial

variable {R : Type*} [CommSemiring R] (p e : ℕ) [ExpChar R p]

/-- Translation by `t` commutes with the pullback `X ↦ X ^ (p ^ e)` once the center is raised to
`t ^ (p ^ e)`. The hypothesis that `p` is the exponential characteristic of `R` is needed: over
`ℤ`, for `P = X`, `t = 1` and exponent `2`, the left side is `(X + 1) ^ 2 = X ^ 2 + 2 * X + 1`
while the right side is `X ^ 2 + 1`. -/
theorem taylor_expand_expChar_pow (P : R[X]) (t : R) :
    taylor t (expand R (p ^ e) P) = expand R (p ^ e) (taylor (t ^ (p ^ e)) P) := by
  simp only [taylor_apply, expand_eq_comp_X_pow, comp_assoc, pow_comp, X_comp, add_comp, C_comp]
  rw [add_pow_expChar_pow, ← C_pow]

/-- The Taylor coefficients of the pullback at indices not divisible by `p ^ e` vanish. -/
theorem coeff_taylor_expand_expChar_pow_eq_zero (P : R[X]) (t : R) {r : ℕ}
    (hr : ¬p ^ e ∣ r) : (taylor t (expand R (p ^ e) P)).coeff r = 0 := by
  simp [taylor_expand_expChar_pow, coeff_expand (pow_pos (expChar_pos R p) e), hr]

end Polynomial
