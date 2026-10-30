-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/DigitsOf.lean: THE SMALLNESS TEST: "THE DIGITS ARE IN THEIR TABLES", AS ONE
NAMED SENTENCE, IN A LIGHT FILE OVER THE LIBRARY ALONE. A DEFINITION. NO THEOREM. NO SOUNDNESS IS
CLAIMED.

Two threads end in this sentence: the law of the smallness test spends it, the law of the lookup on
the digits proves it. So that neither writes its body out a second time, it stands here by itself.
  `DigitsOf tl A`: tl: the smallness test's part of the verifier's state (the Lean structure
    `HTailF2`), or the plan's value of it; A: a table of cells (array, row, column). For every
    matrix μ, every combination u and every row i of cells of μ: the cell of the digits' array
    (number `tl.ix.ZZ`) in row u, at the column that `zzCol` gives for the low digit of row i, is in
    the low digits' table; the like for the high digit.
It reads of tl: the number of matrices, the matrices' rows, the number of combinations, the digits'
array's number, and the two fields from which `zzCol` makes a column.

-/
import OnBytes.Tie.Pv.Tail.SizeOf
import Cb.Gen.RngAlg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open OnBytes OnBytes.Model

/-- The digits are in their tables, at a value of the smallness test's part of the verifier's state
and a table of cells. -/
def DigitsOf (tl : HTailF2) (A : ℕ → ℕ → ℕ → Cb.Gl.E) : Prop :=
  ∀ μ, μ < tl.NM → ∀ u, u < tl.tau → ∀ i, i < (tl.mats.getD μ {}).m →
    Cb.Rng.InTab (OnBytes.Tie.Pv.Tail.sizeOf tl).size.lo
        (A tl.ix.ZZ u ((tl.zzCol μ 0 0).getD 0 + i)) ∧
      Cb.Rng.InTab (OnBytes.Tie.Pv.Tail.sizeOf tl).size.hi
        (A tl.ix.ZZ u ((tl.zzCol μ 1 0).getD 0 + i))

end VerifiableInference.Desc.First.K8
