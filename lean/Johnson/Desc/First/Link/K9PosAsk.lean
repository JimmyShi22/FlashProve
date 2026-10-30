-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/K9PosAsk.lean: ONE TEST WITH CODE ON PUBLIC NUMBERS, A SEGMENT AT A TIME:
"EVERY TABLE ENDS INSIDE THE ARRAY OF THE VECTOR OF READS": for each table of the segment's plan
(matrix, rows in a block, first entry): first entry + the matrix's columns times its stretches of
rows is at most the number of columns of the planned array of the third vector.
Definitions alone. No Mathlib. For the cutting-in as a conjunct of the test `k9Entry`
(Johnson/Desc/First/Link/K9Asks.lean, not in this library): the list of tables must not be empty;
the head says what the test is not.

  `placeB l p`: a list of tables (matrix, rows in a block, entries), laid one behind the other from
    entry p on: (matrix, rows in a block, first entry).
  `layTriples`, `attPlaced`, `headTriples`: the tables of a layers' segment, of an attention segment
    and of the head, off the public parameters alone. `triplesAt W l`: by the segment's number.
  `colsB F t`: the columns of array t of a ledger; 0 where there is none.
  `posPlanB W l X`: **THE TEST.**
EVERY "none" ENDS IN false: no plan of the group; no table can be laid. SO DOES AN EMPTY LIST OF
TABLES (`layTriples` at a g beyond `P.tails` lays none): ONE CLAUSE THAT IS NO LAW's PREMISE.
IT IS NO TEST OF TILING: it asks that each table END INSIDE the array, not that the tables lie
apart: a table made twice as long that runs over its neighbours and still ends inside passes.
A TABLE IS PASSED OVER where its matrix's number is not below NM, where it has no stretch of rows
(m / len = 0; so too at len = 0) or where its matrix has no column: no read names an entry of it.
SECOND TEXTS: `layTriples` repeats `layShapes` (OnBytes/Tie/Pv/Tail/ShapesLay.lean); `placeB`
repeats `place` (ShapesAtt.lean); `colsB` repeats `colsU` (OnBytes/Tie/Pv/Tail/EndLoops.lean).
`attTriples` and `headTabs` are K9RowsAsk.lean's. The ties are in Law/K9PosAskLaw.lean.
DEFAULTS: `(tl.ix.U.getD 2 none).getD 0`: where the structure names no array for the third vector:
array 0. `getD … {}`: an empty matrix (m = 0, k = 0): the table is passed over. `colsB` at an array
that is not there: 0: so a table that is not passed over fails the test there.
LOOPS AND POWERS: those of K9RowsAsk.lean, and no other. The caller asks l < 25 alone.
Limits. A yes says what the clause says and no more.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Link.K9RowsAsk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9Asks
open OnBytes OnBytes.Model

/-- Tables laid one behind the other from entry p on. -/
def placeB : List (Nat × Nat × Nat) → Nat → List (Nat × Nat × Nat)
  | [], _ => []
  | a :: l, p => (a.1, a.2.1, p) :: placeB l (p + a.2.2)

/-- A layers' segment's tables: matrix, rows in a block, first entry. -/
def layTriples (P : Layer.Pub) (g : Nat) : Option (List (Nat × Nat × Nat)) :=
  (Layer.layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k))
    (Layer.tableAsks P.y P.rd g) 0).map fun x =>
      x.2.1.flatMap fun a => a.2.map fun m => (m.1, a.1.L, m.2)

def attPlaced (S : Attention.Shape) : List (Nat × Nat × Nat) := placeB (attTriples S (unitsB S)) 0

def headTriples (h : Head.Shape) (hp : Head.HPlanH2) : Option (List (Nat × Nat × Nat)) :=
  (headTabs h hp).map fun t => t.funs.toList.map fun Fn => (Fn.mat, Fn.len, Fn.start)

/-- The segment's tables. -/
def triplesAt (W : Verify.Public) (l : Nat) : Option (List (Nat × Nat × Nat)) :=
  if l = 24 then headTriples W.hS W.H
  else if l % 2 = 0 then layTriples W.layers (l / 2)
  else (W.A[l / 2]?).map fun a => attPlaced a.S

/-- The columns of array t. -/
def colsB (F : Fork) (t : Nat) : Nat := ((F.trees[t]?).map (·.K)).getD 0

/-- One table ends inside the array, or no read names an entry of it. -/
def tableIn (tl : HTailF2) (cols : Nat) (t : Nat × Nat × Nat) : Bool :=
  !decide (t.1 < tl.NM) || (tl.mats.getD t.1 {}).m / t.2.1 == 0 || (tl.mats.getD t.1 {}).k == 0 ||
    decide (t.2.2 + (tl.mats.getD t.1 {}).k * ((tl.mats.getD t.1 {}).m / t.2.1) ≤ cols)

/-- **THE TEST.** -/
def posPlanB (W : Verify.Public) (l : Nat) (X : Stages.LinkH) : Bool :=
  match triplesAt W l with
  | some ts =>
    !ts.isEmpty && ts.all (tableIn X.tl (colsB X.Fp ((X.tl.ix.U.getD 2 none).getD 0)))
  | none => false

end VerifiableInference.Desc.K9Asks
