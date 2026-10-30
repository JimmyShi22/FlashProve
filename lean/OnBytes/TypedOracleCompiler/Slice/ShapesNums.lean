-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ShapesNums.lean: the numbers of a table's record that a file's analysis asks, from
"the sizes fit".

`RecNums T eM lg s εs` (OnBytes/TypedOracleCompiler/Slice/ThreeDelivers.lean) lists eight conditions on the numbers
of a table's record: seven on the code, the radius, the coordinates and the answers, and one on a
price. `Size.Fit` (OnBytes/TypedOracleCompiler/Slice/ShapesAt.lean) has the seven. So at sizes that fit the price
alone is owed.

Main theorems: `recNums_of_fit`; `recNums_full`, `recNums_small`: at the two written sizes.

What is not claimed. THE PRICE IS A HYPOTHESIS: that the record's bound is at most an error εs is
shown of no εs here. Nothing on any part. No probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.ThreeDelivers
import OnBytes.TypedOracleCompiler.Slice.ShapesAtFull
import OnBytes.TypedOracleCompiler.Slice.ShapesAtSmall

set_option autoImplicit false

namespace OnBytes.Slice.Shapes
open Iop Rom Prob
open scoped ENNReal

/-- At sizes that fit, the numbers of a table's record are in order as soon as the price is. -/
theorem recNums_of_fit (z : Size) (h : z.Fit) (εs : ℝ≥0∞)
    (price : kapSl 128 ^ (seedBS z.lg z.s).b *
      ((((Cb.listMax (2 ^ z.T.a) (2 ^ z.T.a - (z.T.r + z.T.l) + 1) z.eM).choose 2 *
        (recZ z.T.l z.lg z.s).err : ℕ) : ℝ≥0∞) / Fintype.card (recZ z.T.l z.lg z.s).D) ≤ εs) :
    TypedOracleCompiler.Slice.RecNums z.T z.eM z.lg z.s εs where
  pos := h.pos
  depth := h.depth
  dim := h.dim
  radius := h.radius
  johnson := h.johnson
  pads := h.pads
  cube := h.cube
  price := price

/-- At the sizes of the full-size parameter file with a record. -/
theorem recNums_full (εs : ℝ≥0∞)
    (price : kapSl 128 ^ (seedBS zFull.lg zFull.s).b *
      ((((Cb.listMax (2 ^ zFull.T.a) (2 ^ zFull.T.a - (zFull.T.r + zFull.T.l) + 1) zFull.eM).choose
        2 * (recZ zFull.T.l zFull.lg zFull.s).err : ℕ) : ℝ≥0∞) /
          Fintype.card (recZ zFull.T.l zFull.lg zFull.s).D) ≤ εs) :
    TypedOracleCompiler.Slice.RecNums zFull.T zFull.eM zFull.lg zFull.s εs :=
  recNums_of_fit zFull zFull_fit εs price

/-- At the sizes of the small example of the setting with a record. -/
theorem recNums_small (εs : ℝ≥0∞)
    (price : kapSl 128 ^ (seedBS zSmall.lg zSmall.s).b *
      ((((Cb.listMax (2 ^ zSmall.T.a) (2 ^ zSmall.T.a - (zSmall.T.r + zSmall.T.l) + 1)
        zSmall.eM).choose 2 * (recZ zSmall.T.l zSmall.lg zSmall.s).err : ℕ) : ℝ≥0∞) /
          Fintype.card (recZ zSmall.T.l zSmall.lg zSmall.s).D) ≤ εs) :
    TypedOracleCompiler.Slice.RecNums zSmall.T zSmall.eM zSmall.lg zSmall.s εs :=
  recNums_of_fit zSmall zSmall_fit εs price

end OnBytes.Slice.Shapes
