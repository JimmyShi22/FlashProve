-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Own/Shapes.lean: two small tests on shapes, in the description's own text, for every
block that reads opened columns in order or takes in a linear form.

  colsStand key W cols xs
      THE OPENED COLUMNS STAND AS ASKED. A column is (key, position, words). Laid beside the list xs
      of the positions asked for, pair by pair as far as both lists go: each column bears the tree's
      key, stands at the position asked for, and has W words. IT DOES NOT COMPARE THE TWO LISTS'
      LENGTHS: whoever calls it asks that too.
  tensorInOrder v
      A TENSOR IS IN ORDER. It has at most 63 variables; if it has a written-out factor, the slice
      of 2 ^ (number of dense variables) values from "first" on lies inside its vector; each dense
      variable is one of the tensor's variables and has the pair (1, 1); no dense variable is named
      twice.
  formFits f vars
      A FORM FITS A VECTOR OF 2 ^ vars ENTRIES. Each of its tensors has just vars variables and is
      in order; each of its single entries has an index below 2 ^ vars.
What is taken from the hand-written program's files: the records Tensor and Form with their fields,
the type E of an element with its equality, and its 1. No function of these files that says yes or
no is called: a walk by constants beneath the three finds none (colsStand: no constant of these
files at all).
That the three say just what the program's Blk.columnsFit, Tensor.ok and Form.fits say, at all
arguments, is proved beside, in Johnson/Desc/Own/ShapesAgree.lean, which no block imports.
LIMIT: whether these tests ask enough is not said here.
No theorem here. Nothing on soundness.

-/
import OnBytes.Iop.Tensor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own

/-- The opened columns stand as asked, as far as both lists go. -/
def colsStand (key W : Nat) (cols : List (Nat × Nat × List UInt64)) (xs : List Nat) : Bool :=
  (cols.zip xs).all fun p => p.1.1 == key && p.1.2.1 == p.2 && p.1.2.2.length == W

/-- A tensor is in order. -/
def tensorInOrder (v : OnBytes.Tensor) : Bool :=
  decide (v.pairs.length ≤ 63) &&
    (v.denseVars.isEmpty || decide (v.first + 2 ^ v.denseVars.length ≤ v.values.size)) &&
    (v.denseVars.all fun d => v.pairs[d]? == some (OnBytes.oneE, OnBytes.oneE)) &&
    decide v.denseVars.Nodup

/-- A form fits a vector of 2 ^ vars entries. -/
def formFits (f : OnBytes.Form) (vars : Nat) : Bool :=
  (f.tensors.all fun v => v.pairs.length == vars && tensorInOrder v) &&
    f.entries.all fun e => decide (e.1 < 2 ^ vars)

end VerifiableInference.Desc.Own
