-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Plan/Units.lean: from the layout of the committed matrix to what the key's proof of the
ranges looks up.

The matrix. Its cells are signed bytes. Its rows come in units. A unit of D digits and R rows holds
R / D rows of numbers, plane by plane: digit q of number i is in the unit's row q (R / D) + i. D is
2 (a weight: low + 256 high) or 4 (numbers whose range is not claimed here: their digits are bytes,
and no more is said of them). After the last unit, up to a stated number of ranged rows, come rows
that hold bytes only.

Two statements. Bytes: every cell of the ranged rows lies in -128 .. 127. Weights: every number of
a unit of two digits lies in -4096 .. 4095. Each is one lookup in a range table.

The entries, in order. An entry is a pair of rows.
 1. For each unit of two digits, in the order of the list: digits 0 and 1 of each of its numbers.
    These are the entries of the weights, and the first entries of the bytes.
 2. For each unit of four digits: digits 0 and 1 of each number, then digits 2 and 3 of each.
 3. The rows after the last unit, in pairs of neighbours.
The lookup of the bytes takes each row of an entry as a key of its own. So a part of that lookup
holds both rows of the same entries, and a prover that unpacks a weight gets both bytes at once.

Main definitions: ShapeLookup, Shape, RowUnit, unitsOk, shapeOfUnits.
C++ counterpart: wf_units_fault and wf_shape_of_units in blocks/frame/wf_units.h; ShapeLookup and
Shape are WfShapeLookup and WfShape in blocks/frame/wf_frame.h.

Not claimed here: which units of a model have four digits. That is taken from the layout. Nor that
these are the right ranges for a model. The widths, offsets and digit weights are constants of this
file. No public file names them, so neither the digest of the public files nor the commitment ID
holds them. They are bound as the item "ranges" in the parameter bytes of the key's first chain
(docs/format/09-key-and-leaf-files.md, the head of section 9, and R13.14).
-/
import OnBytes.Params.Items

namespace OnBytes.Plan

open OnBytes.Params

/-- One lookup, before its keys are cut into parts. -/
structure ShapeLookup where
  /-- the lookup without parts, and with mu = live = 0: the planes follow from the parts -/
  lookup : WfLookup
  /-- all entries in order, as runs: the first row, how many entries, and the stride between an
  entry's rows. The first place is not read. -/
  entries : List WfRun
  /-- 2^logRowsApart rows of an entry are keys of their own -/
  logRowsApart : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- What the key's proof of the ranges looks up. -/
structure Shape where
  /-- the matrix has 2^kCol columns -/
  kCol : Nat
  /-- the rows of the matrix -/
  matrixRows : Nat
  /-- the lookups -/
  lookups : List ShapeLookup
  deriving DecidableEq, Repr, Inhabited

/-- A unit of rows of the matrix. -/
structure RowUnit where
  /-- its first row -/
  firstRow : Nat
  /-- how many rows it has -/
  rows : Nat
  /-- the digits of its numbers -/
  digits : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A cell lies in -2^7 .. 2^7 - 1. -/
def byteBits : Nat := 8

/-- A number of a unit of two digits lies in -2^12 .. 2^12 - 1. -/
def weightBits : Nat := 13

/-- True if the units follow one another without a gap from the row upto on, within the ranged rows,
and each has two or four digits and the same number of rows for each digit. One after the other, so
that no row is in two entries; without a gap, since a row between two units would be in no entry. -/
def unitsFollow (rangedRows : Nat) : Nat → List RowUnit → Bool
  | _, [] => true
  | upto, u :: us =>
    (u.digits == 2 || u.digits == 4) && u.rows != 0 && u.rows % u.digits == 0 &&
    decide (u.rows ≤ rangedRows) && decide (u.firstRow ≤ rangedRows - u.rows) &&
    u.firstRow == upto && unitsFollow rangedRows (u.firstRow + u.rows) us

/-- The conditions on units that come from a file: there is a unit; the ranged rows are an even
number and at most the rows of the matrix; the matrix has fewer than 2^40 rows; the units follow one
another from row 0 on (unitsFollow). -/
def unitsOk (matrixRows rangedRows : Nat) (units : List RowUnit) : Bool :=
  !units.isEmpty && decide (rangedRows ≤ matrixRows) && rangedRows % 2 == 0 &&
  decide (matrixRows < 2 ^ 40) && unitsFollow rangedRows 0 units

/-- What the key's proof of the ranges looks up, by the rule in this file's head. Nothing if unitsOk
fails. The planes of a multiplicity are left 0: they follow from the parts (lookupOfShape,
OnBytes/Plan/Ranges.lean). firstBound: where the matrix has 2^9 columns or more, the last level of a
part's tree of keys binds the bits 2, 1, 0, 5, 4, 3, 8, 7, 6 of the column first (a fast prover
takes them three at a time). With fewer columns no order is named. -/
def shapeOfUnits (kCol matrixRows rangedRows : Nat) (units : List RowUnit) : Option Shape :=
  let firstBound := if 9 ≤ kCol then [2, 1, 0, 5, 4, 3, 8, 7, 6] else []
  let ofWeights : List WfRun := (units.filter (·.digits == 2)).map fun u =>
    ⟨0, u.firstRow, u.rows / 2, u.rows / 2⟩
  let ofFour : List WfRun := (units.filter (·.digits == 4)).flatMap fun u =>
    [⟨0, u.firstRow, u.rows / 4, u.rows / 4⟩,
     ⟨0, u.firstRow + 2 * (u.rows / 4), u.rows / 4, u.rows / 4⟩]
  let behind := (units.getLast?.map fun u => u.firstRow + u.rows).getD 0
  let pairs : List WfRun := (List.range ((rangedRows - behind) / 2)).map fun i =>
    ⟨0, behind + 2 * i, 1, 1⟩
  let bytes : ShapeLookup :=
    { lookup :=
        { d := byteBits, mu := 0, live := 0, digitWeight := [1],
          offset := UInt64.ofNat (2 ^ (byteBits - 1)), paddingKey := 0, parts := [],
          firstBound := firstBound }
      entries := ofWeights ++ ofFour ++ pairs
      logRowsApart := 1 }
  let weights : ShapeLookup :=
    { lookup :=
        { d := weightBits, mu := 0, live := 0, digitWeight := [1, UInt64.ofNat (2 ^ byteBits)],
          offset := UInt64.ofNat (2 ^ (weightBits - 1)), paddingKey := 0, parts := [],
          firstBound := firstBound }
      entries := ofWeights }
  if unitsOk matrixRows rangedRows units then some ⟨kCol, matrixRows, [bytes, weights]⟩
  else none

end OnBytes.Plan
