-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Own/Stretch.lean: row weights that are written out on a stretch of rows, as a named
part of the description.

A link's pending row says something of the rows first .. first + n - 1 of the weight matrix, under
n written-out weights, and of no other row. The test on the matrix takes row weights as a sum of
vectors of product form. So the stretch is cut into aligned blocks of 2^d rows, at most two of each
size, and each block becomes one such vector: its written-out factor is a slice of the weights or,
for a block of one row, its scalar is the weight.

  `weightsOnRows S first values`: values[i] on row first + i, 0 on every other row.

WHERE IT RETURNS NOTHING, AND WHAT EACH REFUSAL CHECKS. A mark [n] behind a line numbers the case:
three lines, three cases. All compare numbers: the first row, how many weights there are, the
matrix's number of rows. None reads a weight.
  [1] the stretch is not inside the matrix: first + n is more than the matrix's number of rows. Why
      it is asked, by verify-on-bytes's own note (not traced here): the test on the matrix counts no
      weight from that row on, and drops a block that lies wholly there without a refusal; a caller
      that counts more rows than the shape does would lose its claims on the surplus rows unnoticed.
  [2] the matrix has 63 or more row variables, or the stretch is not inside the cube of its rows
  [3] the blocks do not cover the stretch: their numbers of rows do not add up to n (the bound on
      their number, 2 kRow + 2, leaves room for two of each size)

HOW FAR THE TEXT IS ITS OWN. It is the program `verify-on-bytes`'s memberWeightsOnRows with
stretchInTheCube written out inside it (OnBytes/Iop/Lin.lean), token for token. IT ADDS NO SECOND,
INDEPENDENT EYE ON WHAT SHOULD BE ASKED. It is a drop-in at the same arguments. That it returns the
same at all arguments, and just when it returns something: StretchAgree.lean, beside this file,
which no block's text imports.

Of that verifier this file names the record LinShape with its field matrixRows, and two functions
that always return: LinShape.kRow (a number) and stretchBlocks (the list of blocks).

A definition with code; no theorem. Nothing on soundness, on an honest prover or on hiding.

-/
import OnBytes.Iop.Lin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes OnBytes.Params

/-- **Row weights on a stretch of rows**: values[i] on row first + i, and 0 on every other row, as a
sum of vectors of product form. -/
def weightsOnRows (S : LinShape) (first : Nat) (values : Array E) : Option (List Tensor) :=
  if first + values.size ≤ S.matrixRows then
    if S.kRow < 63 && first + values.size ≤ 2 ^ S.kRow then
      let blocks := stretchBlocks S.kRow first values (2 * S.kRow + 2) first
      if (blocks.map fun t => 2 ^ t.denseVars.length).sum == values.size then some blocks
      else none                                                                          -- [3]
    else none                                                                            -- [2]
  else none                                                                              -- [1]

end VerifiableInference.Desc.Own
