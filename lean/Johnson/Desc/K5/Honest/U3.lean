-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/U3.lean: the honest prover's side of an attention segment: the array U3,
entry by entry. Definitions with code; no theorem.

U3 holds the segment's tables. A table has a committed matrix, a block length and a public vector of
weights; it has one entry for each column and each block of rows of its matrix: the column's cells
in that block, summed under the weights. Which tables there are, and each one's matrix, block
length, weights and first entry, is what the verifier's own function `tablesP`
(Johnson/Desc/First/Att/TablesP.lean) makes of the place's numbers, the points and what the lookup
hands in. It is called here; no table is typed a second time. The place of an entry in its table
follows `tabAt` (OnBytes/Model/Tail.lean): first entry + column * blocks + block. In the format's
pages: docs/format/11-3-attention-segment.md, "The parts of U3".

  `blocksOf`, `elemsOf`   a table's number of blocks; its number of entries
  `entryOf`              an entry of one table, by its number in the table
  `u3Of`                 an entry of the array, by its number, from a list of tables
  `u3Att`                the array at a place: the verifier's tables, made once, and the reader of
                         entries
  `u3List`               the first entries in order

An entry is made when it is asked for: the tables on the lookup's planes' matrix are large, and the
three runs of claims in Johnson/Desc/First/Att/RunsP.lean name none of them (the lookup's claims
do). Each asking walks the list of tables anew.

The letters. mats: rows and columns of each matrix of the segment's list. nW: the array's length.
Both are fixed by the plan; the verifier's function refuses a length or a matrix that does not fit
its tables. cell: a cell by (the matrix's number in the list, row, column). lk: the lookup's point
and its three vectors of weights, taken as they come. c: the lookup calls' key points and all
challenges of the segment's own rounds.

Limits. `u3Att` is nothing where the verifier's functions for the points or the tables refuse. Where
it is something the tables tile the numbers below nW, and an entry's number from nW on gives 0. A
weight that lacks counts as 0. Most tables' weights depend on the place's own challenges, through
the laying of these in Johnson/Desc/K5/Honest/Points.lean: that laying is held against the
verifier's own hearing in Johnson/Desc/K5/Honest/PointsToy.lean, not here. Which name a matrix's
number bears, and how the entries lie in the committed rows, is not here. Nothing is said on what is
committed or sent.
Tests: Johnson/Desc/K5/Honest/U3Toy.lean.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Points

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes (E mulE zeroE)
open VerifiableInference.Desc.First.Att.P (Fun1 LookIn tablesP)

/-- The blocks of rows of a table's matrix. -/
def blocksOf (mats : Array (Nat × Nat)) (F : Fun1) : Nat := (mats.getD F.mat (0, 0)).1 / F.len

/-- A table's number of entries: columns times blocks. -/
def elemsOf (mats : Array (Nat × Nat)) (F : Fun1) : Nat :=
  (mats.getD F.mat (0, 0)).2 * blocksOf mats F

/-- **Entry number n of one table**, from 0: n = column * blocks + block; the sum over the block's
rows of the weight times the cell. -/
def entryOf (mats : Array (Nat × Nat)) (cell : Nat → Nat → Nat → E) (F : Fun1) (n : Nat) : E :=
  let nsg := blocksOf mats F
  sumTo F.len fun j => mulE (F.phi.getD j zeroE) (cell F.mat (n % nsg * F.len + j) (n / nsg))

/-- **Entry number n of the array**: of the first table in whose stretch n lies; 0 if there is none.
-/
def u3Of (mats : Array (Nat × Nat)) (cell : Nat → Nat → Nat → E) (funs : Array Fun1) (n : Nat) :
    E :=
  match funs.find? fun F => F.start ≤ n && n < F.start + elemsOf mats F with
  | some F => entryOf mats cell F (n - F.start)
  | none => zeroE

/-- **The array U3 of an attention segment**, as a reader of entries. -/
def u3Att (P : Pub5) (mats : Array (Nat × Nat)) (nW : Nat) (cell : Nat → Nat → Nat → E)
    (lk : LookIn) (c : Chal) : Option (Nat → E) :=
  (ptsOf P c).bind fun p => (tablesP P.g mats nW lk p).map fun t => u3Of mats cell t.funs

/-- The first nW entries, in order. -/
def u3List (nW : Nat) (u : Nat → E) : Array E := (Array.range nW).map u

end H2K5.Honest
