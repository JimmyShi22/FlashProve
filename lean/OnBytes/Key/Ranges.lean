-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Key/Ranges.lean: the lookups that a key file proves, as public values.

A key file says that the entries of the committed matrix lie in their ranges. What that means is
fixed by public values, which are in the parameter item "ranges" of the key's first chain.

A key is a public linear map of entries of the matrix M plus a public constant:
  key(place, column) = offset + sum over the digits q of
                       digitWeight[q] * M[row of (place, q)][column].
A lookup says that each of its keys is one of 0 .. 2^d - 1. A key is an element of the field. That
it is the integer that it looks like is the reader's conclusion from the ranges: digits in
small ranges and weights of a few bits cannot wrap around the prime.
The keys come in parts, for a prover that cannot hold all keys at once. A part has 2^logPlaces
places. Places are covered by runs: for digit q, the place firstPlace + p of a run reads the row
firstRow + p + q * stride of the matrix. A place that no run covers is padding: it holds a public
key, which the multiplicities do not count.

The prover sends how often each row of the range table is met, in bits. Bit j of all these
numbers is plane j. A lookup has 2^mu plane slots, of which the first `live` are real (0: all).

The lookups as values, and their reading from bytes, are in OnBytes/Params/Items.lean. This file
holds the conditions that a lookup must meet by itself and together with the matrix's size, and
where the planes lie in the main rows of the prover's oracle message.

Main definitions: `Wf.Matrix`, `Wf.planesOf`, `Wf.lookupOk`, `Wf.fitsMatrix`, `Wf.coversAllRows`,
`Wf.Block`, `Wf.layout`.
C++ counterpart: public_fault(), the part on the matrix of wf_fault(), wf_covers_all_rows() and
wf_layout() in blocks/iop/wf.h.

What is not claimed: no theorem is stated here.
-/
import OnBytes.Params.Items
import OnBytes.Iop.Lkp
import OnBytes.Chain.Lists

namespace OnBytes.Wf

open OnBytes.Params (WfRun WfPart WfLookup WfPublic LinShape)

/-- The number of real planes of a lookup. -/
def planesOf (l : WfLookup) : Nat := if l.live == 0 then 2 ^ l.mu else l.live

/-- The size of the committed matrix: `rows` rows of 2^kCol entries. It is no part of the item
"ranges": it is written once, in the shape of the test on the committed table. Written in both, the
two could differ: ranges that know of one row fewer than the test would leave that row unlooked at,
and every check would pass. -/
structure Matrix where
  kCol : Nat
  rows : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The matrix's size, from the shape of the test on the committed table. -/
def matrixOf (S : LinShape) : Matrix := ⟨S.kCol, S.matrixRows⟩

/-- The bits that spell a row of the matrix. -/
def Matrix.kRow (m : Matrix) : Nat := ceilLog2 m.rows

/-! ## Conditions on a lookup by itself -/

/-- The runs from a place on: each covers a place, begins at or after `upto` and inside the part,
and ends inside the part. -/
def runsOk (logPlaces : Nat) : Nat → List WfRun → Bool
  | _, [] => true
  | upto, r :: rs =>
    decide (1 ≤ r.places) && decide (upto ≤ r.firstPlace) &&
    decide (r.firstPlace < 2 ^ logPlaces) && decide (r.places ≤ 2 ^ logPlaces - r.firstPlace) &&
    runsOk logPlaces (r.firstPlace + r.places) rs

/-- The conditions on a part: at most 2^40 places; its runs rise without overlap and stay inside the
part (`runsOk`); some place is covered. -/
def partOk (p : WfPart) : Bool :=
  decide (p.logPlaces ≤ 40) && runsOk p.logPlaces 0 p.runs && !p.runs.isEmpty

/-- The conditions on a lookup. fBits: the length of the field's prime in bits.
 - 1 ≤ mu ≤ 6; fewer live planes than slots; 2 to 62 planes; d ≥ 1; d + planes < fBits;
 - at least one digit and one part; no digit has the weight 0: its entries would enter no key, every
   key of a lookup of one digit would be the constant offset, and a key file would be accepted for
   any matrix;
 - the weights and the offset are below the prime, so that a word other than 0 is an element other
   than 0;
 - a place of padding holds a row of the table;
 - no variable is named twice in firstBound;
 - every part passes `partOk`;
 - a stride is 0 exactly if a key has one digit: with one digit nobody would read it, and with
   several digits in one row a key would be a multiple of one entry. -/
def lookupOk (fBits : Nat) (l : WfLookup) : Bool :=
  decide (1 ≤ l.mu) && decide (l.mu ≤ 6) && decide (l.live < 2 ^ l.mu) &&
  decide (2 ≤ planesOf l) && decide (planesOf l ≤ 62) && decide (1 ≤ l.d) &&
  decide (l.d + planesOf l < fBits) &&
  !l.digitWeight.isEmpty && !l.parts.isEmpty &&
  (l.digitWeight.all fun w => w != 0 && okF w) && okF l.offset &&
  decide (l.paddingKey.toNat < 2 ^ l.d) &&
  distinctNats l.firstBound &&
  l.parts.all fun p =>
    partOk p && p.runs.all fun r => (r.stride == 0) == (l.digitWeight.length == 1)

/-! ## Conditions on a lookup and the matrix -/

/-- The conditions on the matrix's size. -/
def Matrix.ok (m : Matrix) : Bool :=
  decide (1 ≤ m.rows) && decide (m.kRow ≤ 40) && decide (m.kCol ≤ 40)

/-- The parts from a number of keys on. For each part: its keys have at least one bit, so it has two
keys or more, and fewer bits than there are planes; firstBound names variables that the last level
of its tree has (a part of 2^v keys has v - 1 there); every row that a run reads is a row of the
matrix; the keys so far can be counted in the planes. -/
def partsFit (m : Matrix) (l : WfLookup) : Nat → List WfPart → Bool
  | _, [] => true
  | keys, p :: ps =>
    decide (1 ≤ p.logPlaces + m.kCol) && decide (p.logPlaces + m.kCol < planesOf l) &&
    (l.firstBound.all fun v => decide (v + 1 < p.logPlaces + m.kCol)) &&
    (p.runs.all fun r =>
      decide (r.stride ≤ m.rows) && decide (r.firstRow < m.rows) &&
      decide (r.places ≤ m.rows - r.firstRow) &&
      decide ((l.digitWeight.length - 1) * r.stride ≤ m.rows - r.firstRow - r.places)) &&
    decide (keys + 2 ^ (p.logPlaces + m.kCol) < 2 ^ planesOf l) &&
    partsFit m l (keys + 2 ^ (p.logPlaces + m.kCol)) ps

/-- The lookup fits the matrix. -/
def fitsMatrix (m : Matrix) (l : WfLookup) : Bool := partsFit m l 0 l.parts

/-- Goes through stretches of rows, sorted by their first rows: true if they leave no gap from
`upto` on and reach `goal`. -/
def noGap (goal : Nat) : Nat → List (Nat × Nat) → Bool
  | upto, [] => decide (goal ≤ upto)
  | upto, s :: ss => decide (s.1 ≤ upto) && noGap goal (max upto s.2) ss

/-- True if the lookup takes single entries as keys, with the weight 1, and its runs reach every
row of the matrix. -/
def coversAllRows (m : Matrix) (l : WfLookup) : Bool :=
  l.digitWeight == [1] &&
  noGap m.rows 0
    ((l.parts.flatMap fun p => p.runs.map fun r => (r.firstRow, r.firstRow + r.places)).mergeSort
      fun a b => decide (a.1 ≤ b.1))

/-! ## Where the planes lie -/

/-- An aligned block of planes of one lookup, and where it lies in the main rows. `Lkp.liveBlocks`
cuts the real planes of a lookup into aligned blocks. A block of 2^b planes is a vector of 2^(b + d)
bits: entry (plane - first) + 2^b * (row of the range table). -/
structure Block where
  /-- the number of the lookup -/
  lookup : Nat
  /-- the first plane -/
  first : Nat
  /-- the logarithm of the number of planes -/
  logPlanes : Nat
  /-- the logarithm of the number of entries -/
  bits : Nat
  /-- the main row in which it lies -/
  row : Nat := 0
  /-- its first place in that row -/
  firstPlace : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- The loop of `layFrom`. done: the blocks that are placed, the last one first. -/
def layLoop (ell : Nat) : Nat → Nat → List Block → List Block → List Block
  | _, _, [], done => done.reverse
  | row, place, b :: bs, done =>
    if place + 2 ^ b.bits > ell then
      layLoop ell (row + 1) (2 ^ b.bits) bs ({ b with row := row + 1, firstPlace := 0 } :: done)
    else
      layLoop ell row (place + 2 ^ b.bits) bs ({ b with row := row, firstPlace := place } :: done)

/-- Puts blocks one after the other into rows of ell places. A block lies within one row. There are
as many blocks as the item "ranges" says, a few for each lookup, and no test bounds the number of
lookups. So `layLoop` calls itself as the last thing that it does, for the stack not to grow with
the list. -/
def layFrom (ell row place : Nat) (bs : List Block) : List Block := layLoop ell row place bs []

/-- All lookups' blocks, the largest first (ties: in the order of the lookups and of their blocks),
put into main rows of ell places. The blocks' sizes are powers of two and the largest come first, so
every block begins at a multiple of its size. -/
def layout (lookups : List WfLookup) (ell : Nat) : List Block :=
  let all : List Block := lookups.zipIdx.flatMap fun x =>
    (Lkp.liveBlocks (planesOf x.1)).map fun b => ⟨x.2, b.1, b.2, b.2 + x.1.d, 0, 0⟩
  layFrom ell 0 0 (all.mergeSort fun a b => decide (b.bits ≤ a.bits))

end OnBytes.Wf
