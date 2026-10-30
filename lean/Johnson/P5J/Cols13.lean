-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/Cols13.lean: AtMgA's FIELD cols13 (2 ^ (P13 Zp).lin.kCol = cols) FROM THE ONE TEST ON A SHAPE THAT WE HAVE ALREADY: fullShapeB, AT THE FIRST CHAIN's OWN (READ-BACK) SHAPE. Two theorems.
  cols_of_shape: fullShapeB S = true → 2 ^ S.kCol = colsAt numsFull (kCol := kLo + the index's v: 7 + 11; cols := 2 ^ (7 + the decoder's data's v)).
  At.cols13_of: so cols13 holds where fullShapeB (P13 Zp).lin = true.
Limits. (P13 Zp).lin is the first chain's parameters' own shape, READ BACK from the parameter bytes; "shape" (PlanOk) is paid in scope at the SIZED shape: that the two are one is shown by nobody here. The full size alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.LettersAt2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At

theorem cols_of_shape (S : OnBytes.Params.LinShape) (h : Desc.K14.Law.fullShapeB S = true) :
    2 ^ S.kCol = colsAt OnBytes.Flat.numsFull := by
  have hi := Desc.K14.Law.full_index S h
  unfold Desc.K14.Law.fullShapeB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  unfold OnBytes.Params.LinShape.kCol
  rw [h.2, hi]
  rfl

theorem cols13_of (Zp : ProofFile.Pub) (h : Desc.K14.Law.fullShapeB (P13 Zp).lin = true) :
    2 ^ (P13 Zp).lin.kCol = colsAt OnBytes.Flat.numsFull := cols_of_shape _ h

end P5J.At

#print axioms P5J.At.cols_of_shape
#print axioms P5J.At.cols13_of
