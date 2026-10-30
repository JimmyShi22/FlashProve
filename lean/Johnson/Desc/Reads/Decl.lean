-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/Decl.lean: THE RECORD IN WHICH A KIND OF BLOCK DECLARES ONE READ, one type for
all kinds, and the address of each cell that a declared entry sums. It imports nothing.

A read is a table of sums of committed cells under public weights. The prover commits to all tables
of a link in one vector, the vector of reads. A kind's forms name entries of it; the smallness test
ties each entry to its cells. A declaration says, from the kind's side, what each entry is meant to
be: with no ledger, no run of the verifier and no table of the smallness test in it.

ALL OF THIS FILE IS A TOOL: definitions for all sizes; it names no description.
  Make: the four ways in which an entry's cells are counted off: short, long, part, column.
  ReadDecl E: the record. E: the type of a weight.
  cellOf: THE ONE RULE for a matrix with a position axis: where feature F at position p stands.
  ReadDecl.cells m k i j: cell number j of entry i: its matrix, its column, its row; m, k: the rows
    and the columns of each part of the matrix. The four makes' offsets are written here, once.
  ReadDecl.room m k: how many entries a table of this run has on these parts.
  Laid: the four numbers of one table as the smallness test lays it: vector, matrix, length, start.
  ReadDecl.tabs m k: THE TABLES OF THE SMALLNESS TEST TO WHICH ONE DECLARATION UNFOLDS: one for each
    part: the vector, its matrix, its run's length, its first entry. Written here, once, for all.
  Make.Fits make len m: column: len = m. long block: block * (len / block) = len, and a column's
    m / (len / block) features are m / len blocks. short, part: nothing.
  ReadDecl.Whole m k: the run is not empty, count is room, and the make fits.
  toy_short, toy_long, toy_part, toy_column, toy_tabs, toy_column_misfit, toy_long_misfit: worked
    out.
THE VECTOR. A declared read lies in the link's THIRD vector, which a table's record numbers 2. That
is no field: tabs lays the number as a constant (vectorOfReads). The programs lay every table of the
smallness test in that vector. A kind that ever reads from another vector needs a field here.
THE ORDER OF A TRIPLE. cellOf and cells return (MATRIX, COLUMN, ROW). The rule is that of placeIn
(Johnson/Road/HeadPlace.lean), BUT placeIn returns (part, ROW, COLUMN), and cellIn there reads a
list of matrices as M matrix ROW COLUMN. Whoever fills from placeIn or cellIn swaps the last two.
WHAT BINDS LITTLE. name is a label: this file's statements do not read it. make: at sizes that fit
all four makes give one address, row (i mod (m / len)) len + j of column (i / (m / len)) mod k of
part i / (m / len) / k: so a wrong make is caught by nothing there. SIZES THAT FIT: for short and
part: all; for long: the block divides the run's length, and divides the number m / T of features in
a column; FOR COLUMN: THE RUN'S LENGTH IS THE NUMBER OF ROWS. At m = 2 len the make column counts
entry k as row 0 of the NEXT matrix, where a table's entry k is a run of the first
(toy_column_misfit). Where a column holds three features and a block two, the make long counts a
block over the end of a column (toy_long_misfit). Whole asks that the make fits, so that the record
itself refuses a misfit. parts and count are bound by Whole alone. The vector's number is read by
FunsAre alone (Reads/DeclRow.lean).
THE WEIGHTS ARE A FUNCTION, NOT AN ARRAY. Where an array's reader fills w, with 0 beyond the array,
an array that is shorter than len puts the weight 0 INSIDE the run, in silence. The record cannot
see it. That each array is as long as its run is for the filling's own statement, as a test by name;
on the table's side lensB asks it (Reads/Stated.lean). Two fillings are never to be compared by
"=": they may differ from len on, where nothing reads them.
MORE PARTS THAN ONE are worked out here at toy_tabs alone. Whether a kind's matrix in more parts
than one has run anywhere is for the head of that kind's filling to say.
WHOSE FEATURES. A declaration counts THE MATRIX'S OWN features, as they lie in the committed matrix.
Where a kind numbers a borrowed matrix's features otherwise (limb l of channel k of the stream), the
renumbering is no field: it belongs to the address of a use (Addressed, Reads/DeclRow.lean).

Not said: that any table of the smallness test is as declared, that a form names the entry that
its clause means, or that the parts have one size: those are for statements over this record.
cells is total: beyond len, beyond count, or at sizes that do not fit, it returns some triple.

-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads

/-- How the cells of an entry are counted off.
short: the matrix has a run of T cells for each feature, one for each position; a column holds m / T
  features. Entry i is feature i; cell j is position j. The run's length is T.
long block: the same matrix. Entry i is the block of the features block * i, ..., block * i +
  block - 1; cell j is feature block * i + j / T at position j % T. The run's length is block * T.
part: no position axis. The rows of a column are cut in runs of len rows. Entry i is run number i,
  counted down a column, then column by column, then part by part; cell j is row j of the run.
column: entry i is column number i, counted through the parts; cell j is row j. The run's length is
  the number of rows. -/
inductive Make where
  | short
  | long (block : Nat)
  | part
  | column

/-- One read, as a kind declares it: a table of the link's THIRD vector, the vector of reads, in one
piece for each part of its matrix. -/
structure ReadDecl (E : Type) where
  /-- the name under which the kind's text asks for the table's first entry -/
  name : String
  /-- the number, in the link's list of committed matrices, of the first part of the matrix -/
  mat : Nat
  /-- the number of parts: the matrices mat, mat + 1, ..., mat + parts - 1 of that list; 1 for a
  matrix in one piece -/
  parts : Nat
  /-- how an entry's cells are counted off -/
  make : Make
  /-- the run's length: the number of cells that one entry sums, which is the number of weights -/
  len : Nat
  /-- the number of entries of the table, all parts together: THE TABLE'S LENGTH in the vector of
  reads (room), not the number of entries that the kind's forms read, which may be smaller. A table
  with two readers is one declaration. -/
  count : Nat
  /-- the place of entry 0 in the link's vector of reads, counted in entries from 0. A kind's text
  asks for it by name; as a formula it is the sum of the lengths of the tables in front. -/
  start : Nat
  /-- weight number j: a formula in the public numbers and the heard points. For the make long: the
  weight of feature block * i + r at position p has the number r * T + p. ONLY THE NUMBERS BELOW len
  COUNT: a plain function, so that a formula or an array's reader fills it as it stands; what it
  returns from len on is read by no statement over this record (joined_weights, addressed_weights
  in Reads/DeclRow.lean: two declarations that agree below len are joined and addressed alike). An
  array's reader over an array shorter than len returns 0 inside the run: see the head. -/
  w : Nat → E

/-- Where feature F at position p stands, in a matrix whose first part has the number mat, whose
parts have m rows and k columns, at T positions: a column holds m / T features; the features fill a
column, then the next column, then the next part. Returns the matrix, the column, the row. -/
def cellOf (mat m k T F p : Nat) : Nat × Nat × Nat :=
  (mat + F / (m / T) / k, F / (m / T) % k, F % (m / T) * T + p)

/-- Cell number j of entry i: the matrix, the column, the row. m, k: the rows and the columns of
each part. -/
def ReadDecl.cells {E : Type} (d : ReadDecl E) (m k i j : Nat) : Nat × Nat × Nat :=
  match d.make with
  | .short => cellOf d.mat m k d.len i j
  | .long block =>
    cellOf d.mat m k (d.len / block) (block * i + j / (d.len / block)) (j % (d.len / block))
  | .part => cellOf d.mat m k d.len i j
  | .column => (d.mat + i / k, i % k, j)

/-- The number of entries that a table with this run has on parts of m rows and k columns. -/
def ReadDecl.room {E : Type} (d : ReadDecl E) (m k : Nat) : Nat := d.parts * (k * (m / d.len))

/-- The number that a table's record bears for the third vector, the vector of reads. -/
def vectorOfReads : Nat := 2

/-- One table as the smallness test lays it, without its weights. -/
structure Laid where
  /-- the vector in which the table lies -/
  tree : Nat
  /-- the matrix, by its number in the link's list of committed matrices -/
  mat : Nat
  /-- the run's length -/
  len : Nat
  /-- the table's first entry in the vector -/
  start : Nat
  deriving DecidableEq

/-- The tables of the smallness test to which the declaration unfolds, in their order: for part q
below parts: in the third vector, the matrix mat + q, the run's length, the first entry
start + q * (k * (m / len)). Each has the weights w, those below len. -/
def ReadDecl.tabs {E : Type} (d : ReadDecl E) (m k : Nat) : List Laid :=
  (List.range d.parts).map fun q =>
    ⟨vectorOfReads, d.mat + q, d.len, d.start + q * (k * (m / d.len))⟩

/-- The make fits a run of len cells on parts of m rows. Whole columns: the run is the column. Long
blocks, at len / block positions: the block divides the run's length, and the m / (len / block)
features of a column are m / len whole blocks. Short and part: nothing is asked. -/
def Make.Fits : Make → Nat → Nat → Prop
  | .column, len, m => len = m
  | .long block, len, m => block * (len / block) = len ∧ m / (len / block) = m / len * block
  | _, _, _ => True

/-- The run is not empty, the number of entries is that of the tables on all parts, and the make
fits. -/
def ReadDecl.Whole {E : Type} (d : ReadDecl E) (m k : Nat) : Prop :=
  0 < d.len ∧ d.count = d.room m k ∧ d.make.Fits d.len m

/-! ## A toy at each make: a matrix in two parts, numbers 3 and 4 of the list, each of 8 rows and 2
columns -/

/-- A declaration on the toy's matrix. -/
def toyDecl (make : Make) (len : Nat) : ReadDecl Nat :=
  { name := "toy", mat := 3, parts := 2, make := make, len := len, count := 2 * (2 * (8 / len)),
    start := 0, w := fun _ => 0 }

/-- Two positions, so four features a column, sixteen in all. Feature 13 is the second of the last
column: part 1, column 1, rows 2 and 3. -/
theorem toy_short : (toyDecl .short 2).cells 8 2 13 1 = (4, 1, 3) ∧
    (toyDecl .short 2).room 8 2 = 16 := by decide

/-- Two positions, blocks of two features. Block 5 holds the features 10 and 11; cell 3 is feature
11 at position 1: part 1, column 0, row 7. -/
theorem toy_long : (toyDecl (.long 2) 4).cells 8 2 5 3 = (4, 0, 7) ∧
    (toyDecl (.long 2) 4).room 8 2 = 8 := by decide

/-- Runs of four rows, two a column. Run 5 is the lower half of column 0 of part 1. -/
theorem toy_part : (toyDecl .part 4).cells 8 2 5 3 = (4, 0, 7) ∧ (toyDecl .part 4).room 8 2 = 8 :=
  by decide

/-- Whole columns. Column 3 is column 1 of part 1. -/
theorem toy_column : (toyDecl .column 8).cells 8 2 3 6 = (4, 1, 6) ∧
    (toyDecl .column 8).room 8 2 = 4 := by decide

/-- Two tables, one for each part; the second begins behind the eight entries of the first. -/
theorem toy_tabs : (toyDecl .short 2).tabs 8 2 = [⟨2, 3, 2, 0⟩, ⟨2, 4, 2, 8⟩] ∧
    (toyDecl .short 2).Whole 8 2 :=
  ⟨by decide, by decide, by decide, True.intro⟩

/-- The make column at runs of four rows, half a column. Entry 2 is counted as row 0 of column 0 of
the NEXT part, where a table of this run has it in column 1 of the first. Whole fails; with the make
part it holds. -/
theorem toy_column_misfit : (toyDecl .column 4).cells 8 2 2 0 = (4, 0, 0) ∧
    (toyDecl .part 4).cells 8 2 2 0 = (3, 1, 0) ∧
    ¬ (toyDecl .column 4).Whole 8 2 ∧ (toyDecl .part 4).Whole 8 2 := by
  refine ⟨by decide, by decide, fun h => ?_, by decide, by decide, True.intro⟩
  have h' : (4 : Nat) = 8 := h.2.2
  exact absurd h' (by decide)

/-- The make long at two positions and blocks of two features, on parts of SIX rows: three features
a column. Block 1 holds the features 2 and 3: the last of column 0 and the first of column 1, where
a table's run of four rows lies in one column. The make does not fit; on parts of eight rows it
does. -/
theorem toy_long_misfit : (toyDecl (.long 2) 4).cells 6 2 1 0 = (3, 0, 4) ∧
    (toyDecl (.long 2) 4).cells 6 2 1 2 = (3, 1, 0) ∧
    ¬ (Make.long 2).Fits 4 6 ∧ (Make.long 2).Fits 4 8 := by
  refine ⟨by decide, by decide, fun h => ?_, by decide, by decide⟩
  have h' : (6 : Nat) / (4 / 2) = 6 / 4 * 2 := h.2
  exact absurd h' (by decide)

end VerifiableInference.Reads

#print axioms VerifiableInference.Reads.toy_tabs
#print axioms VerifiableInference.Reads.toy_column_misfit
#print axioms VerifiableInference.Reads.toy_long_misfit
#print axioms VerifiableInference.Reads.toy_short
#print axioms VerifiableInference.Reads.toy_long
#print axioms VerifiableInference.Reads.toy_part
#print axioms VerifiableInference.Reads.toy_column
