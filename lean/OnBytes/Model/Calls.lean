-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Calls.lean: how the segments of a lookup call are placed in the call's columns.

A sub-proof of the model looks up many keys in a few public tables. The keys of one call form a
matrix: one row for each token position and one column for each feature. A sub-proof of a group of
layers has one such matrix for each layer, with the same columns. The columns come in named
segments, for example all features of one tensor. The parameter file lists the calls as lines
"call NAME KIND SEGMENT ..". This file holds the rule that gives every entry of a segment its
column. The rule depends only on the segments' lengths, their order and a minimum number of columns.
It follows `place` in verifier/src/cp_verify.cpp.

The rule. Each segment's length is split into powers of two, the largest first. All pieces of all
segments are sorted by size, the largest first. Pieces of equal size keep the order of their
segments. The pieces are then placed one after another, starting at column 0. The number of
columns is the number of covered columns rounded up to a power of two, or the given minimum if
that is larger. A column that no piece covers holds padding.

Main definitions: `Seg`, `CallD`, `place`, `CallD.padding`, `CallD.seg?`, `callText`.
Not checked here: whether a list of calls is one that the verifier allows. The layout of each
sub-proof checks that.
-/
import OnBytes.Iop.Ground

namespace OnBytes.Model

/-- One segment of a call. -/
structure Seg where
  /-- the segment's name -/
  name : String
  /-- the number of its entries -/
  n : Nat
  /-- the column of each entry -/
  pos : Array Nat
  /-- the segment exists only on layers with routed experts; on other layers its columns hold
  padding -/
  moe : Bool := false
  deriving Inhabited

/-- One call with its segments placed in columns. -/
structure CallD where
  /-- the call's name -/
  name : String
  /-- the kind of table that the call looks up in -/
  kind : String
  /-- the segments, in the order of the call's line -/
  segs : List Seg
  /-- the number of columns, a power of two -/
  J : Nat
  /-- the logarithm of J -/
  lJ : Nat
  /-- for each column: 0 if it holds padding on every layer, 1 if it holds keys on every layer,
  2 if it holds keys only on layers with routed experts -/
  used : Array Nat
  deriving Inhabited

/-- A segment before it is placed: name, number of entries, and whether it exists only on layers
with routed experts. -/
abbrev SegAsk : Type := String × Nat × Bool

/-- The largest exponent of a piece. Higher bits of a length get no piece. -/
def topBit : Nat := 40

/-- The pieces of size 2^b, one for each segment whose length has bit b. Each piece is returned as
(number of the segment, b, first column). `off` is the first free column; the new one is returned
too. `s` is the number of the first segment in the list. -/
def piecesOfSize (b : Nat) : List Nat → Nat → Nat → List (Nat × Nat × Nat) × Nat
  | [], _, off => ([], off)
  | n :: ns, s, off =>
    if n.testBit b then
      let r := piecesOfSize b ns (s + 1) (off + 2 ^ b)
      ((s, b, off) :: r.1, r.2)
    else piecesOfSize b ns (s + 1) off

/-- All pieces of sizes 2^(k - 1) down to 1, in the order in which they are placed, and the first
free column after them. The arguments after the lengths: k, then the first free column. -/
def piecesBelow (lengths : List Nat) : Nat → Nat → List (Nat × Nat × Nat) × Nat
  | 0, off => ([], off)
  | k + 1, off =>
    let a := piecesOfSize k lengths 0 off
    let r := piecesBelow lengths k a.2
    (a.1 ++ r.1, r.2)

/-- The columns of segment number s, which has n entries. Its pieces come in the list in order of
decreasing size, which is the order of its entries. A length with a bit above `topBit` leaves its
last entries at column 0. -/
def columnsOf (pieces : List (Nat × Nat × Nat)) (s n : Nat) : Array Nat :=
  let laid := (pieces.filter fun p => p.1 == s).foldl
    (fun a p => a ++ (Array.range (2 ^ p.2.1)).map (· + p.2.2)) (#[] : Array Nat)
  laid ++ Array.replicate (n - laid.size) 0

/-- Marks the columns of a segment in `used`: with 2 if the segment exists only on layers with
routed experts, with 1 otherwise. -/
def markUsed (used : Array Nat) (g : Seg) : Array Nat :=
  g.pos.foldl (fun u p => u.setIfInBounds p (if g.moe then 2 else 1)) used

/-- Places the segments of a call in its columns. The number of columns is at least
2^`floorLg`. -/
def place (name kind : String) (asks : List SegAsk) (floorLg : Nat) : CallD :=
  let pieces := piecesBelow (asks.map (·.2.1)) (topBit + 1) 0
  let segs := asks.zipIdx.map fun x =>
    ({ name := x.1.1, n := x.1.2.1, pos := columnsOf pieces.1 x.2 x.1.2.1, moe := x.1.2.2 } : Seg)
  let lJ := max (ceilLog2 pieces.2) floorLg
  { name := name, kind := kind, segs := segs, J := 2 ^ lJ, lJ := lJ,
    used := segs.foldl markUsed (Array.replicate (2 ^ lJ) 0) }

/-- True if column j holds padding on layer lam, counted within its group. Layers with an odd number
have routed experts. The count of padding keys uses this rule (OnBytes/Model/LayerLayout.lean). The
expressions for the keys take the padding's columns from `pos` (weighedOf,
OnBytes/Model/LayerForms.lean). `used` is filled from `pos`, so both have one source. -/
def CallD.padding (c : CallD) (lam j : Nat) : Bool :=
  let u := c.used.getD j 0
  u == 0 || (u == 2 && lam % 2 == 0)

/-- The segment with this name, if the call has one. -/
def CallD.seg? (c : CallD) (name : String) : Option Seg := c.segs.find? fun g => g.name == name

/-- The calls as text, one line for each: `word`, the call's name, its kind and its segments'
names, separated by single spaces and ended by a line feed. A digest of this text is a part of the
statement. -/
def callText (word : String) (calls : List CallD) : String :=
  String.join (calls.map fun c =>
    word ++ " " ++ c.name ++ " " ++ c.kind ++ String.join (c.segs.map fun g => " " ++ g.name) ++
      "\n")

end OnBytes.Model
