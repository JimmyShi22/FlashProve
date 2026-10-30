-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/ClaimsTrue.lean: two lemmas of algebra: a form with coefficients 0 (`Setup.sum_zero_coef`)
and two equations added (`add_eq`).
-/
import Blocks.EqN
import Code.Facts
import Blocks.LevelDef
import Iop.InteractiveOracleProof
import Mathlib.Data.FinEnum

set_option autoImplicit false

namespace Blocks

open Finset

/-! ## Sums over the rows of a vector -/

namespace Setup

variable {F : Type} [Field F] [Fintype F] {E : Type} [Field E] [Fintype E] [DecidableEq E]
    [Algebra F E]

omit [Fintype E] in
omit [DecidableEq E] in
/-- A form with coefficients 0. -/
theorem sum_zero_coef {R m k : ℕ} (M : Fin R → Fin k → E) :
    ∑ i : Fin R, ∑ j : Fin m, (0 : E) * nat (M i) j.val = 0 := by
  simp

end Setup

/-! ## Two equations -/

/-- Two equations, added. -/
theorem add_eq {M : Type} [Add M] {a a' b b' : M} (h : a = a') (h' : b = b') : a + b = a' + b' := by
  rw [h, h']

end Blocks
