-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Key/TestRanges.lean: tests of OnBytes/Key/Ranges.lean on small made-up lookups.

That file holds the conditions on the lookups by which a key file is meant to show that the entries
of the committed matrix lie in their ranges, and says where the lookups' planes lie in the prover's
oracle message. Its head explains key, digit, part, place, run, padding and plane.

How the values below are written. A run is ⟨first place, first row, number of places, stride⟩: the
place first place + p reads, for digit q, the matrix's row first row + p + q * stride. A part is
⟨logarithm of its number of places, its runs⟩. A matrix is ⟨logarithm of its number of columns,
number of rows⟩. In a lookup the range table has 2^d rows; there are 2^mu plane slots, of which the
first `live` are real planes (0: all); `firstBound` lists the variables that the first rounds of the
last key level bind.

Every test is checked when the file compiles. The expected values follow by hand from the rules in
that file's comments. The program does not import this file.
-/
import OnBytes.Key.Ranges

namespace OnBytes.Wf.Test

open OnBytes.Params (WfRun WfPart WfLookup)

/-- Single entries as keys: a table of 4 rows, 3 real planes of 4 slots, one part of 2 places that
covers the rows 0 and 1. -/
def single : WfLookup where
  d := 2
  mu := 2
  live := 3
  digitWeight := [1]
  offset := 2
  paddingKey := 0
  parts := [⟨1, [⟨0, 0, 2, 0⟩]⟩]
  firstBound := []

/-- Keys of two digits: a table of 8 rows, 2 planes, one part of one place. -/
def pair : WfLookup where
  d := 3
  mu := 1
  live := 0
  digitWeight := [1, 4]
  offset := 4
  paddingKey := 0
  parts := [⟨0, [⟨0, 0, 1, 1⟩]⟩]
  firstBound := []

/-- A block as a row of numbers: lookup, first plane, logarithm of the planes, logarithm of the
entries, row, first place. -/
def line (b : Block) : Nat × Nat × Nat × Nat × Nat × Nat :=
  (b.lookup, b.first, b.logPlanes, b.bits, b.row, b.firstPlace)

-- the real planes: `live` of them, or all 2^mu slots if `live` is 0
#guard planesOf single == 3 && planesOf pair == 2
-- the largest block comes first; a block that does not fit the row opens the next row
#guard (layout [single, pair] 16).map line ==
  [(1, 0, 1, 4, 0, 0), (0, 0, 1, 3, 1, 0), (0, 2, 0, 2, 1, 8)]
-- in longer rows all three lie in one row
#guard (layout [single, pair] 32).map line ==
  [(1, 0, 1, 4, 0, 0), (0, 0, 1, 3, 0, 16), (0, 2, 0, 2, 0, 24)]
-- ties keep the order of the lookups
#guard (layout [single, single] 8).map line ==
  [(0, 0, 1, 3, 0, 0), (1, 0, 1, 3, 1, 0), (0, 2, 0, 2, 2, 0), (1, 2, 0, 2, 2, 4)]

-- both lookups are in order by themselves
#guard lookupOk 64 single && lookupOk 64 pair
-- refused: mu out of range; live = all slots (that is written 0); one plane; a table of one row;
-- d + planes reaches the 64 bits; a weight 0; no digit
#guard !lookupOk 64 { single with mu := 0 }
#guard !lookupOk 64 { single with mu := 7 } && lookupOk 64 { single with mu := 6 }
#guard !lookupOk 64 { single with live := 4 } && !lookupOk 64 { single with live := 1 }
#guard !lookupOk 64 { single with d := 0 } && !lookupOk 64 { single with d := 61 } &&
  lookupOk 64 { single with d := 60 }
#guard !lookupOk 64 { single with digitWeight := [0] }
#guard !lookupOk 64 { single with digitWeight := [] }
-- refused: the prime itself as a weight, which would count as 0; an offset not below the prime
#guard !lookupOk 64 { single with digitWeight := [18446744069414584321] }
#guard !lookupOk 64 { single with offset := 18446744069414584321 } &&
  lookupOk 64 { single with offset := 18446744069414584320 }
#guard lookupOk 64 { single with digitWeight := [18446744069414584320] }
-- refused: padding outside the table; a variable named twice; no part
#guard !lookupOk 64 { single with paddingKey := 4 }
#guard !lookupOk 64 { single with firstBound := [0, 0] }
#guard !lookupOk 64 { single with parts := [] }
-- refused: a stride with one digit; no stride with two digits
#guard !lookupOk 64 { single with parts := [⟨1, [⟨0, 0, 2, 1⟩]⟩] }
#guard !lookupOk 64 { pair with parts := [⟨0, [⟨0, 0, 1, 0⟩]⟩] }
-- refused: a run without a place; runs that overlap; a run beyond its part; a part without a run;
-- a part of 2^41 places. Admitted: a part with a gap between its runs
#guard !partOk ⟨1, [⟨0, 0, 0, 0⟩]⟩ && !partOk ⟨2, [⟨0, 0, 2, 0⟩, ⟨1, 2, 1, 0⟩]⟩
#guard !partOk ⟨1, [⟨2, 0, 1, 0⟩]⟩ && !partOk ⟨1, [⟨1, 0, 2, 0⟩]⟩ && !partOk ⟨1, []⟩
#guard !partOk ⟨41, [⟨0, 0, 1, 0⟩]⟩ && partOk ⟨2, [⟨0, 0, 1, 0⟩, ⟨2, 5, 2, 0⟩]⟩

-- a matrix of two rows and two columns: 4 keys are fewer than 2^3
#guard fitsMatrix ⟨1, 2⟩ single && coversAllRows ⟨1, 2⟩ single
-- a third row is reached by no run
#guard !coversAllRows ⟨1, 3⟩ single
-- a lookup of two digits, or of one digit with another weight than 1, covers no row in this sense
#guard !coversAllRows ⟨1, 1⟩ pair && !coversAllRows ⟨1, 2⟩ { single with digitWeight := [2] }
-- the matrix's size: at least one row, at most 2^40 rows and 2^40 columns
#guard (⟨1, 2⟩ : Matrix).ok && !(⟨1, 0⟩ : Matrix).ok && !(⟨41, 2⟩ : Matrix).ok &&
  (⟨0, 2 ^ 40⟩ : Matrix).ok && !(⟨0, 2 ^ 40 + 1⟩ : Matrix).ok
-- a run that reads a row beyond the matrix
#guard !fitsMatrix ⟨1, 1⟩ single && !fitsMatrix ⟨1, 1⟩ pair && fitsMatrix ⟨1, 2⟩ pair
-- a part of one key: a part has two keys or more
#guard !fitsMatrix ⟨0, 2⟩ pair
-- refused: a part of 2^3 keys under 3 planes: a part's number of keys must have fewer bits than
-- there are planes
#guard !fitsMatrix ⟨2, 2⟩ single
-- the last level of a part of 2^2 keys has one variable
#guard fitsMatrix ⟨1, 2⟩ { single with firstBound := [0] }
#guard !fitsMatrix ⟨1, 2⟩ { single with firstBound := [1] }
-- stretches in any order, with an overlap, without a gap
#guard coversAllRows ⟨0, 5⟩
  { single with parts := [⟨2, [⟨0, 2, 3, 0⟩]⟩, ⟨2, [⟨0, 0, 3, 0⟩]⟩] }
-- a gap: row 2 is in no stretch
#guard !coversAllRows ⟨0, 5⟩
  { single with parts := [⟨2, [⟨0, 3, 2, 0⟩]⟩, ⟨2, [⟨0, 0, 2, 0⟩]⟩] }
-- a stretch inside an earlier one does not pull the covered rows back
#guard coversAllRows ⟨0, 5⟩
  { single with parts := [⟨2, [⟨0, 0, 4, 0⟩]⟩, ⟨2, [⟨0, 1, 1, 0⟩]⟩, ⟨2, [⟨0, 4, 1, 0⟩]⟩] }
-- 300,000 blocks of 2 places in rows of 4: the last one is in row 149999. The list is long on
-- purpose: the depth of `layLoop`'s calls must not grow with its list
#guard (layFrom 4 0 0 (List.replicate 300000 ⟨0, 0, 0, 1, 0, 0⟩)).getLast?.map (·.row) ==
  some 149999

end OnBytes.Wf.Test
