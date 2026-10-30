-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/Window.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: the random
combinations of the cells, their window and their digits, as plain functions on integers.
DEFINITIONS, WITH CODE. NO THEOREM. NOTHING IS CLAIMED ON COMPLETENESS, SOUNDNESS OR HIDING.

The kind's block draws a matrix with entries -1, 0, 1 and sends nothing
(Johnson/Desc/First/K8/Hear.lean). Behind it the prover commits to the digits of every combination
of every row of cells (docs/format/11-1-machinery.md, "The cells, the arrays of the matrices, U3 and
ZZ"). By that page a combination has digits only if it lies in its window, from -2^17 to 2^17 - 1.
Here a combination is the sum, over a matrix's columns, of a drawn entry times a cell; no mask and
no pad is added to it; whether all combinations lie in the window is computed from the cells and the
drawn matrix.

  `entry p drawn mu c u`   the drawn entry of column c of matrix mu and combination u
  `comb p cell drawn mu i u`   combination u of row i of cells of matrix mu
  `inWindow z`             z lies in the window
  `leaves p cell drawn`    the first (matrix, row, combination) whose combination leaves the
                           window; none if all lie in it
  `cellsSmall p cell`      every cell of the place's matrices is at most 128 in absolute value: a
                           test, with code, for whoever has to say that of an honest prover's cells.
                           (By the format's page, in the paragraph that begins "The honest prover",
                           in the programs a cell is a signed byte; 128 is the bound that the laws
                           on the window spend.)
  `low z`, `high z`       low z is (z + 2^17) mod 2^10; high z is floor ((z + 2^17) / 2^10) mod 2^8.
                           Both are in range at every integer; inside the window they are the
                           format's digits
  `digitAt p cell drawn u col`   the entry in row u and column col of the array of digits; 0 beyond
                           its tau rows and beyond its columns
THE ORDER OF THE DRAWN ENTRIES is the verifier's: entry number (first column of mu + c) * tau + u of
the one drawn sequence (OnBytes/Model/Tail.lean: `foldSums` with `foldColumn`; the format's page,
"The sampled matrix").

WORDS. A place: where a block of this kind stands in a chain; its numbers are `Par`
(Johnson/Desc/First/K8/Hear.lean). The place's list: the matrices that the test at that place
covers, those of earlier links of the chain among them.

Limits. OF A DRAWN SEQUENCE THAT IS TOO SHORT EVERY ENTRY BEYOND ITS END COUNTS AS 0: `entry` reads
with the fallback 0, so at the empty sequence every combination is 0 and `leaves` finds nothing. And
nothing here asks that an entry is -1, 0 or 1: `entry` takes whatever integer stands there, while
the verifier reads an entry by its sign: the two agree at -1, 0 and 1 alone. A round of the kind
draws (all columns) * tau entries, each -1, 0 or 1. `leaves` and `cellsSmall` go through as many
matrices as the list of columns has, `allRows` and `digitAt` through the list of rows: that the two
lists are of one length is asked by the kind's test on the plan (Hear.lean: `planOk`), not here.
Nothing here says that an honest prover's cells pass `cellsSmall`, and `leaves` does not ask it.
`cellsSmall` asks EVERY entry of the shape of EVERY matrix of the place's list: matrices of earlier
links, the matrices that hold the bits of a lookup's multiplicities, and the cells that no other
claim reads, among them. Beyond a matrix's rows and columns `cell` is whatever it yields; `comb`
reads the columns below the place's number alone, and asks nothing of u: from tau on it reads
another column's entries (`leaves` and `digitAt` call it below tau alone). Outside the window `low`
and `high` lie in their ranges still, and do not give the combination back.

-/
import Johnson.Desc.First.K8.Hear
import OnBytes.Model.Tail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes.Model (lbz t2D0 t2D1)

/-- The cells of a place's matrices: the matrix's number in the place's list, the row, the column.
-/
abbrev CellsAt : Type := Nat → Nat → Nat → Int

/-- The drawn entry of column c of matrix mu and combination u; 0 beyond the sequence's end. Beyond
the list of matrices the first column is what `firstColumns` yields with the fallback 0: at the
list's length the number of all columns, beyond that 0; `comb` reads no column there. -/
def entry (p : Par) (drawn : Array Int) (mu c u : Nat) : Int :=
  drawn.getD (((firstColumns p).getD mu 0 + c) * p.tau + u) 0

/-- Combination u of row i of cells of matrix mu. -/
def comb (p : Par) (cell : CellsAt) (drawn : Array Int) (mu i u : Nat) : Int :=
  (List.range (p.ks.getD mu 0)).foldl (fun z c => z + entry p drawn mu c u * cell mu i c) 0

/-- From -2^17 to 2^17 - 1. -/
def inWindow (z : Int) : Bool := decide (-((2 : Int) ^ lbz) ≤ z) && decide (z < (2 : Int) ^ lbz)

/-- The first combination that leaves its window: matrix, row of cells, combination. -/
def leaves (p : Par) (cell : CellsAt) (drawn : Array Int) : Option (Nat × Nat × Nat) :=
  (List.range p.ks.length).findSome? fun mu =>
    (List.range (p.ms.getD mu 0)).findSome? fun i =>
      (List.range p.tau).findSome? fun u =>
        if inWindow (comb p cell drawn mu i u) then none else some (mu, i, u)

/-- Every cell of the place's matrices is at most 128 in absolute value. -/
def cellsSmall (p : Par) (cell : CellsAt) : Bool :=
  (List.range p.ks.length).all fun mu =>
    (List.range (p.ms.getD mu 0)).all fun i =>
      (List.range (p.ks.getD mu 0)).all fun c => decide ((cell mu i c).natAbs ≤ 128)

/-- The low digit of z + 2^17: its remainder modulo 2^10, which is not negative. -/
def low (z : Int) : Nat := ((z + (2 : Int) ^ lbz) % (2 : Int) ^ t2D0).toNat

/-- The high digit of z + 2^17: of its quotient by 2^10, rounded down, the remainder modulo 2^8. -/
def high (z : Int) : Nat := (((z + (2 : Int) ^ lbz) / (2 : Int) ^ t2D0) % (2 : Int) ^ t2D1).toNat

/-- The rows of cells of all matrices together. -/
def allRows (p : Par) : Nat := p.ms.foldl (· + ·) 0

/-- The matrix and the row in it of a row of cells that is counted through all matrices. mu: the
number of the list's first matrix. -/
def rowAt : List Nat → Nat → Nat → Option (Nat × Nat)
  | [], _, _ => none
  | m :: ms, mu, r => if r < m then some (mu, r) else rowAt ms (mu + 1) (r - m)

/-- The entry in row u and column col of the array of digits: the low digits of all rows of cells,
then the high digits. 0 beyond the array's rows and beyond its columns. -/
def digitAt (p : Par) (cell : CellsAt) (drawn : Array Int) (u col : Nat) : Nat :=
  let mz := allRows p
  match rowAt p.ms 0 (if col < mz then col else col - mz) with
  | some (mu, i) =>
    if u < p.tau then
      if col < mz then low (comb p cell drawn mu i u) else high (comb p cell drawn mu i u)
    else 0
  | none => 0

end VerifiableInference.Desc.First.K8.Honest
