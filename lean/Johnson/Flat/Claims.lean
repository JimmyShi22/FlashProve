-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/Claims.lean: what a key's and a proof's statements read of a decoded stored table: the
committed matrix, cell by cell, and the index that it holds.

Definitions, and one equation. OnBytes/Slice/ConfOf.lean makes the library's configuration with a
record from a decoder D of a stored table and from A : `D.Claims X` (OnBytes/Slice/DecoderRec.lean):
the indices are `A.Mat`, the instances X. This file gives an A at X := `Instance' ppref`.

The placement is that of docs/format/11-5-weights-in-the-table.md, "From W to the table": the
committed matrix has m0 rows and 2 ^ (k_lo + v) columns, where the table has 2 ^ v rows; the cell in
row y and column c, with c = j + 2 ^ k_lo * r and j below 2 ^ k_lo, is entry j + 2 ^ k_lo * y of the
message of the table's row r. The two numbers m0 and k_lo are words of the parameter item "the test
on the table" (docs/format/09-key-and-leaf-files.md, R13.13).

Main names:
  `MatrixNums`: the numbers m0 and k_lo.
  `Cells D N`: a matrix of m0 rows and 2 ^ (k_lo + v) columns over the extension field.
  `cellsOf D N u`: the matrix that the decoded table u holds. An entry at or behind the pads, or
    outside a row's message, is read as 0.
  `cellsOf_cut`: it reads no pad.
  `Says D N M W`: the integer matrix W says the cells of M, and is 0 outside M's shape.
  `indexIn D N M`: an index of Cm/RelBase.lean, a well-formed matrix of digits at the reference
    numbers, that says M, if there is one.
  `claims D N s`: the A. In range: M holds an index. The claim of an instance: at the index that M
    holds, if it holds one, the request is true (`Cm.PaperTrue`, Cm/RelTruePaper.lean): AN
    IMPLICATION, never to be laid as a relation without "in range" before it: the docstring.
  `numsFit v cut l N P line`: a test that the decoder's numbers, the matrix's and the model's sizes
    fit each other.
  `nextTokenOf D N s`: the integer model's next token at the index that M holds.
Limits: nothing is proved beside `cellsOf_cut`. `Cells D N` is EVERY matrix of the shape over the
extension field: most hold no model. Nothing here shows that a matrix is in range: by the page that
is what a key file states of the cells, so it is for the key file's protocol. No definition asks
`numsFit`: with other numbers an index cut to the smaller shape can say a matrix. EXACT MATCH ALONE.
THE TABLE OF SCALES s IS A LETTER IN THIS FILE, and is not asked to be lawful. That at most
one index says a matrix is shown in Johnson/Flat/LedgerClaim.lean (`holds_unique`), not here;
`indexIn` picks one by choice and cannot be run. That the library's reading of the weights off a
matrix of digits (Inst/Model/Layout.lean) is the programs' placement of the weights in the committed
matrix (the same page, from "Units" on) is not shown. The reference numbers alone.

-/
import OnBytes.Slice.DecoderRec
import Johnson.Flat.Instance
import Cm.RelTruePaper
import Inst.Model.Layout

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Slice Inst.Model

/-- The numbers of the committed matrix. -/
structure MatrixNums where
  /-- its rows: m0 -/
  rows : ℕ
  /-- the logarithm of the number of its columns that one row of the table holds: k_lo -/
  kLo : ℕ

variable (D : DecR) (N : MatrixNums)

/-- A matrix of the committed matrix's shape, over the extension field. -/
abbrev Cells : Type := Fin N.rows → Fin (2 ^ (N.kLo + D.v)) → GE

/-- The table's row number n: bit i of n is the row's coordinate i. -/
def rowAt (v n : ℕ) : Fin v → Bool := fun i => n.testBit i.val

/-- The matrix that a decoded table holds. -/
def cellsOf (u : D.ix.Row × D.toDec.En → GE) : Cells D N := fun y c =>
  if h : c.val % 2 ^ N.kLo + 2 ^ N.kLo * y.val < D.T.l ∧
      c.val % 2 ^ N.kLo + 2 ^ N.kLo * y.val < D.cut then
    u (rowAt D.v (c.val / 2 ^ N.kLo), ⟨c.val % 2 ^ N.kLo + 2 ^ N.kLo * y.val, h.1⟩)
  else 0

/-- The matrix reads no pad. -/
theorem cellsOf_cut (u u' : D.ix.Row × D.toDec.En → GE) (h : D.Agree u u') :
    cellsOf D N u = cellsOf D N u' := by
  funext y c
  unfold cellsOf
  split
  · rename_i hc
    exact h _ ⟨_, hc.1⟩ hc.2
  · rfl

/-- The integer matrix W says the cells of M, and is 0 outside M's shape. -/
def Says (M : Cells D N) (W : Mat) : Prop :=
  (∀ y c, M y c = ((W y.val c.val : ℤ) : GE)) ∧
    ∀ y c, ¬ (y < N.rows ∧ c < 2 ^ (N.kLo + D.v)) → W y c = 0

open Classical in
/-- An index that says M, if there is one. -/
noncomputable def indexIn (M : Cells D N) : Option Cm.Idx :=
  if h : ∃ i : Cm.Idx, Says D N M i.mat then some (Classical.choose h) else none

/-- **What the statements read of a decoded table**, at a table of scales s. THE CLAIM `Rel` IS AN
IMPLICATION: "if the matrix holds an index, then the request is true there": a proof file's protocol
has no test on the cells' ranges, so it can show no more. At a matrix that holds no index it is true
of every instance. SO IT IS NEVER TO BE LAID AS A CONFIGURATION's RELATION WITHOUT `inRange` BEFORE
IT: a relation runs over all matrices, and "whatever is in the relation is the model's output" is
false at a matrix without an index, where the next token is `none`. -/
noncomputable def claims (s : Cm.Scales) : D.Claims (Instance' ppref) where
  Mat := Cells D N
  mat := cellsOf D N
  inRange := fun M => (indexIn D N M).isSome = true
  Rel := fun M x => ∀ i, indexIn D N M = some i → Cm.PaperTrue s.kap s.nf i x
  mat_cut := cellsOf_cut D N

/-- True if the numbers fit each other: the matrix fits a row's message before the pads (the page:
"A verifier rejects the public files unless m0 2^k_lo entries fit a row's message beside its pads"),
the pads lie in the message, and m0 is the sum of the rows of the library's units at the sizes P and
2 ^ (k_lo + v) columns, rounded up to a multiple of `line`, the parameter file's line D. -/
def numsFit (v cut l : ℕ) (N : MatrixNums) (P : Params) (line : ℕ) : Bool :=
  decide (N.rows * 2 ^ N.kLo ≤ cut) && decide (cut ≤ l) &&
    N.rows == (Layout.off (N.kLo + v) (Layout.units P) (Layout.units P).length + (line - 1)) /
      line * line

/-- The next token at the index that M holds; `none` if it holds none. -/
noncomputable def nextTokenOf (s : Cm.Scales) (M : Cells D N)
    (tokens : List VerifiableInference.Token) : Option VerifiableInference.Token :=
  (indexIn D N M).bind fun i => nextTokenAt s i tokens

end OnBytes.Flat
