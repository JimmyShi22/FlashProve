/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/
/-
Adapted from Mathlib (https://github.com/leanprover-community/mathlib4), file
Mathlib/RingTheory/Polynomial/HilbertPoly.lean, commit 5ed2965256430c3649e86755f9576b54eca72435
(v4.34.0), lines 90-101. Licence: Apache-2.0, see ThirdParty/MathlibBackport/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* Only the declarations below are taken over. This Mathlib does not have them.
* The namespace and variable lines around them are written anew, and this is an ordinary Lean file,
  not one of Lean's module system.
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.SimpleRing.Principal

open Nat PowerSeries
variable (F : Type*) [Field F]
namespace Polynomial

lemma preHilbertPoly_eq_choose_add_sub [CharZero F] (d : ℕ) {k n : ℕ} (hkn : k ≤ n + d) :
    (preHilbertPoly F d k).eval (n : F) = (n + d - k).choose d := by
  have : (d ! : F) ≠ 0 := by norm_cast; positivity
  rcases le_or_gt k n with h | h
  · calc
    _ = (↑d !)⁻¹ * eval (↑(n - k + 1)) (ascPochhammer F d) := by simp [cast_sub h, preHilbertPoly]
    _ = (n + d - k).choose d := by
      rw [ascPochhammer_nat_eq_natCast_ascFactorial]
      simp [field, ascFactorial_eq_factorial_mul_choose, Nat.sub_add_comm h]
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    simpa [preHilbertPoly] using
      Or.inr ⟨k - n - 1, by omega, by rw [Nat.sub_sub, Nat.cast_sub h]; push_cast; ring⟩

end Polynomial
