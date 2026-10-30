-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/NormCells.lean: the rows of digits of all norms of a feed-forward segment,
made of the segment's own streams.

WHAT IT DOES NOT SHOW. No law and no test here. The rows are made of whatever limbs the given cells
hold for the residual streams: nothing says that these are a model's run, that a limb is a byte, or
that a digit made here lies in the range that the lookup asks. A limb is read as the whole number
nearest to 0 that its word stands for; cells that are not small give rows that are false. THE PLAN
IS TAKEN TO HAVE FIVE LIMBS: a row made here has 99 cells, and at a plan with four limbs, whose rows
have 74, the array is false without a word.

WHAT IT DEFINES. Of all cells of a segment, those of the tensor of the norms' rows are tied to other
cells by the verifier's claims on the norms (docs/format/11-2-feed-forward-segment.md, groups 5 and
6): norm i's row at token t spells the sum of squares of stream i at t, its root and the reciprocal.
For a synthetic input that is to meet these claims the rows have to be reckoned from the streams.
  normM, normEps   a norm's two public numbers
  normCells        all rows, as one array: cell j of norm i's row at token t at (i NR + j) T + t
  cellWithRows     a reader of cells with the rows' cells taken from such an array
Definitions with code. No theorem.

Limits. normCells reads d times the number of limbs cells for each norm and token. cellWithRows is
handed the array: whoever calls it makes the array once and passes it on; made inside a reader it
would be made anew at every read.
Nothing on any property.
No property is claimed.
-/
import Johnson.Desc.K4.Honest.Cells
import Johnson.Desc.K4.Honest.NormRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest
open OnBytes
open OnBytes.Model (fOfInt ledNR)
open OnBytes.Model.Layer (LM1 LM2 matIx)

/-- The exponent M of norm i of the group: word LM1 or LM2 of the scales of the norm's layer, as the
verifier's twoM reads it (OnBytes/Model/Layer.lean). -/
def normM (Q : K4Pub) (i : Nat) : Nat :=
  Q.P.sc.kl (Q.g * Q.P.y.Lam + i / Q.P.y.NN) (if i % 2 == 1 then LM2 else LM1)

/-- The constant eps of norm i of the group, as the verifier's epsOf has it. -/
def normEps (Q : K4Pub) (i : Nat) : Nat := if i % 2 == 1 then Q.P.y.h.eps2 else Q.P.y.h.eps1

/-- **The rows of all norms of the segment**, made of the streams' limbs as cell has them. Cell j of
norm i's row at token t stands at the index (i NR + j) T + t, NR the cells of a row. -/
def normCells (Q : K4Pub) (cell : Nat → Nat → Nat → F) : Array F :=
  let y := Q.P.y
  let xs := tensorOf y "xs"
  let NR := ledNR y.h.xl
  let rows : Array (Array Int) := (Array.range (y.NI * y.T)).map fun x =>
    normRow (normM Q (x / y.T)) (normEps Q (x / y.T))
      (limbSums y.h.xl y.h.d fun lb j => intOfF (streamLimb y cell xs (x / y.T) lb j (x % y.T)))
  (Array.range (y.NI * NR * y.T)).map fun x =>
    fOfInt ((rows.getD (x / y.T / NR * y.T + x % y.T) #[]).getD (x / y.T % NR) 0)

/-- **The cells with the norms' rows laid over.** rows: normCells' array. In the matrix ar a column
holds fr = (its rows) / T features, so the cell in row r and column c belongs to feature
c fr + r / T and token r mod T; the features of the tensor of rows are read from the array, every
other cell from cell. -/
def cellWithRows (Q : K4Pub) (rows : Array F) (cell : Nat → Nat → Nat → F) (mu r c : Nat) : F :=
  let y := Q.P.y
  if mu == (matIx y).iAR then
    let X := tensorOf y "row"
    let ft := c * (y.mrow.getD 2 0 / y.T) + r / y.T
    if X.OFF ≤ ft && ft < X.OFF + X.cnt * X.J then rows.getD ((ft - X.OFF) * y.T + r % y.T) 0
    else cell mu r c
  else cell mu r c

end OnBytes.Desc.First.K4.Honest
