-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/FormsKeysMat.lean: the cells of a layer sub-proof's matrices, read in the matrices'
entries; and what a table of the reads says of a matrix.

The theorems on the forms of the lookup's segments speak of cells c mat φ i: the matrix's number (0
af, 1 ad, 2 ar, 3 qa, 4 and 5 the two matrices at the borders of the stream), the feature, counted
across all parts of the matrix, and the position (Johnson/Road/FormsKeysKit.lean). There c is free.
This file defines such cells from the entries M of the matrices of a sub-proof's list, by the rule
that the verifier's tables of reads follow: a column of a part holds the cells of neighbouring
features, feature after feature, T positions each; the columns of a part follow each other; then
the parts.

Only definitions.
 - Mats: the entries of the matrices of a sub-proof's list: number in the list, row, column.
 - firstM, rowsM, colsM, partsM, fcM: for each of the six numbers the first part's number in the
   list, the rows and the columns of a part, the number of parts, the features of a column; all from
   the verifier's layout.
 - cellsAt: the cells.
 - Holds: what a table of the reads (HFun) says of its matrix, entry by entry, in a world.

What is not claimed. M is any function: nothing here ties it to a commitment, or to what was fixed
before a point was drawn. The verifier never tests Holds: for each table and each run of rows it
adds one claim, a random combination over the columns. That step is not looked at. Holds speaks of
an entry of a virtual row of the array of reads (World.entry); that this array has one row, which is
its virtual row, is not shown. The program does not import this file.

-/
import Johnson.Road.FormsKeysKit
import OnBytes.Model.Tail

set_option autoImplicit false

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World HFun HTailF2)
open OnBytes.Model.Layer (Lay matIx)

/-- The entries of the matrices of a sub-proof's list: the matrix's number in the list, the row of
cells, the column. -/
abbrev Mats (K : Type) := ℕ → ℕ → ℕ → K

/-- The number in the sub-proof's list of the first part of the matrix with the kit's number mat. -/
def firstM (y : Lay) : ℕ → ℕ
  | 0 => (matIx y).iAF
  | 1 => (matIx y).iAD
  | 2 => (matIx y).iAR
  | 3 => (matIx y).iQA
  | 4 => (matIx y).iXI
  | 5 => (matIx y).iXO
  | _ => 0

/-- The rows of a part. -/
def rowsM (y : Lay) : ℕ → ℕ
  | 4 => y.mxb
  | 5 => y.mxb
  | m => y.mrow.getD m 0

/-- The columns of a part. -/
def colsM (y : Lay) : ℕ → ℕ
  | 4 => y.kxb
  | 5 => y.kxb
  | m => y.kcol.getD m 0

/-- The number of parts: af and ad may lie in several parts, the other four matrices are one part
each. -/
def partsM (y : Lay) : ℕ → ℕ
  | 0 => y.parts.getD 0 0
  | 1 => y.parts.getD 1 0
  | _ => 1

/-- The features whose cells a column holds. -/
def fcM (y : Lay) (mat : ℕ) : ℕ := rowsM y mat / y.T

/-- The cells, read in the matrices' entries: the cell of feature φ at position i stands in row
(φ mod fc) T + i of column number φ / fc, counted across the parts; column number C is column
C mod k of part C / k. -/
def cellsAt {K : Type} (y : Lay) (M : Mats K) : Cells K := fun mat φ i =>
  M (firstM y mat + φ / fcM y mat / colsM y mat) (φ % fcM y mat * y.T + i)
    (φ / fcM y mat % colsM y mat)

/-- What the table Fn says of its matrix, entry by entry, in the world W: the entry of the reads for
column c and run sg of the matrix's rows holds the sum of the column's entries in that run under the
table's weights. tl: the smallness test's numbers, from which the entry's place is taken (tabAt);
iU3, K3: the array that holds the reads, and the number of its columns. -/
def Holds {K : Type} [Field K] (ρ : Reading K) (W : World K) (tl : HTailF2) (iU3 K3 : ℕ)
    (M : Mats K) (Fn : HFun) : Prop :=
  ∀ c sg pos, tl.tabAt Fn c sg = some pos →
    W.entry iU3 (pos / K3) (pos % K3) =
      ∑ j ∈ range Fn.len, ρ.val (Fn.phi.getD j zeroE) * M Fn.mat (sg * Fn.len + j) c

end OnBytes.Road
