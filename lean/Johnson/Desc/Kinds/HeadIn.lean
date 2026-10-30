-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/HeadIn.lean: THE OUTPUT HEAD'S OWN ROUNDS: what comes in from the lookup (the
classes In of HeadNorm.lean and HeadCells.lean, and each call's padding term), made of the lookup's
points and of the place of the nine keys in the lookup's calls. It shows nothing by itself.
Definitions with code; no theorem.

A CALL of the lookup has one table and 2^lJ columns of T keys. A key of the head (HeadCells.lean,
HeadNorm.lean) has an entry for each feature, digit or vocabulary entry, and each entry takes one
column of its call. The lookup leaves for each call a key point zk = (zj, zt): lJ coordinates on the
columns, lt on the positions. The public weight of an entry is the equality weight of its column at
zj. Columns that no entry takes hold the call's padding key.
After the format's 11.4, "A call's columns" and the table beneath it. The list of calls is the
format's default list; a parameter file can state another: not borne here.

-/
import Johnson.Desc.Kinds.HeadCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head

open OnBytes (E)
open Norm (lt ls d S2)
variable [Sizes]

/-- The six calls, each with its keys in order: two ranges of 16 bits; the range of 8 bits; the
table in two halves; the clamp's table. -/
def callList : List (List PlaceKey) :=
  [[.inl .remLow, .inl .remHigh, .inr .marginTop], [.inr .marginMid],
   [.inl .digits, .inr .marginLow], [.inr .tableA], [.inr .tableB], [.inl .clamp]]

/-- The number of a key's entries. -/
def lenOf : PlaceKey → Nat
  | .inl .digits => NR + 21
  | .inl _ => d
  | .inr k => len k

/-- The padding key of call number c: a row of its table: 0 in a range; row 0 of the table,
0 + 2^16 2^F; the clamp's row at 0, 2^15 + 2^39. -/
def padKey (c : Nat) : Nat :=
  if c == 3 || c == 4 then 2 ^ (16 + F) else if c == 5 then 2 ^ 15 + 2 ^ 39 else 0

/-- The sum of the powers of two above 2^b in n's binary writing. -/
def above (b n : Nat) : Nat := n / 2 ^ (b + 1) * 2 ^ (b + 1)

/-- A CALL'S COLUMNS. Each key's length is cut into powers of two, the largest first, so that the
first piece holds the entries from 0 on. The pieces of all the call's keys are sorted by decreasing
size; pieces of one size keep the keys' order. The sorted pieces take columns one after the other
from column 0. lens: the keys' lengths; s: a key's number in the call; x: an entry. Entry x lies in
the piece 2^b of its key; in front of that piece stand all larger pieces of all keys, and the pieces
2^b of the keys before s. -/
def column (lens : List Nat) (s x : Nat) : Nat :=
  let n := lens.getD s 0
  let b := ((List.range 41).find? fun b =>
    n.testBit b && above b n ≤ x && x < above b n + 2 ^ b).getD 0
  (lens.map (above b)).sum + ((lens.take s).filter (·.testBit b)).length * 2 ^ b + (x - above b n)

/-- The logarithm of a call's number of columns: enough for its keys, and at least floor - lt.
floor: the least allowed logarithm of a call's number of keys. -/
def lJ (floor : Nat) (keys : List PlaceKey) : Nat := max (clog2 (keys.map lenOf).sum) (floor - lt)

/-- The vocabulary entry for which entry 0 of a key stands; none for a key of the norm's. -/
def firstEntry : PlaceKey → Option Nat
  | .inr .tableB => some JVa
  | .inr _ => some 0
  | .inl _ => none

/-- WHICH COLUMNS OF A CALL HOLD PADDING: those that no entry takes, and those of the entries that
stand for a vocabulary entry from V on. For each column of the call with these keys: true if so. -/
def paddingColumns (floor : Nat) (keys : List PlaceKey) : Array Bool :=
  let lens := keys.map lenOf
  keys.zipIdx.foldl (fun m k =>
    (List.range (lenOf k.1)).foldl (fun m x =>
      let real := match firstEntry k.1 with
        | some v0 => decide (v0 + x < V)
        | none => true
      if real then m.set! (column lens k.2 x) false else m) m)
    (Array.replicate (2 ^ lJ floor keys) true)

/-- THE NUMBER OF PLACES THAT THE KEY FORMS TREAT AS PADDING: a function of the plan alone, for the
lookup's test on the plan. A column has T places. perTree: how many columns one tree of the lookup
holds. The list runs over the calls, and in a call over its trees. -/
def paddingPlaces (floor perTree : Nat) : List Nat :=
  callList.flatMap fun keys =>
    let m := paddingColumns floor keys
    (List.range (m.size / perTree)).map fun y =>
      Norm.T * ((m.extract (y * perTree) ((y + 1) * perTree)).filter id).size

/-- One key's weights, made once: ew, ewh, and their sums. -/
structure KeyWeights where
  (ew ewh : Array E)
  (wsum wx : E)
  deriving Inhabited

/-- zj: the call's point on its columns. ew x = eq zj (column x). ewh i = eq (zj without its last ls
coordinates) (column (S2 i) / S2): a block of S2 entries takes S2 neighbouring columns. wx: the sum
over the entries that stand for a vocabulary entry below V; entry x of the table's second half
stands for JVa + x. -/
def keyWeights (zj : Point) (lens : List Nat) (s : Nat) (k : PlaceKey) : KeyWeights :=
  let all := eqAll zj
  let blocks := eqAll (zj.extract 0 (zj.size - ls))
  let ew := (Array.range (lenOf k)).map fun x => all.getD (column lens s x) 0
  let v0 := (firstEntry k).getD 0
  { ew, ewh := (Array.range (lenOf k / S2)).map fun i => blocks.getD (column lens s (S2 * i) / S2) 0
    wsum := ew.foldl (· + ·) 0, wx := (ew.extract 0 (V - v0)).foldl (· + ·) 0 }

/-- What comes in from the lookup. -/
structure FromLookup where
  norm : FinalNorm.In
  head : In
  /-- for each call its padding's term and its keys -/
  calls : List (E × List PlaceKey)

/-- zx: the lookup's point, whose last ls + lt coordinates are (zl, zt). zk c: the key point of call
c. A call's padding term is its padding key times the weight of the columns that no entry takes; the
equality weights of all columns add up to 1. -/
def fromLookup (floor : Nat) (zx : Point) (zk : Nat → Point) : FromLookup :=
  let made := callList.zipIdx.map fun c =>
    let lens := c.1.map lenOf
    c.1.zipIdx.map fun k => (k.1, keyWeights ((zk c.2).extract 0 (lJ floor c.1)) lens k.2 k.1)
  let find (same : PlaceKey → Bool) : KeyWeights :=
    ((made.flatMap id).find? fun x => same x.1).map (·.2) |>.getD default
  let n (k : FinalNorm.Key) : KeyWeights := find fun
    | .inl a => a.idx == k.idx
    | .inr _ => false
  let h (k : Key) : KeyWeights := find fun
    | .inl _ => false
    | .inr a => a.idx == k.idx
  let n4 := #[n .remLow, n .remHigh, n .clamp, n .digits]
  let h5 := #[h .marginTop, h .marginMid, h .marginLow, h .tableA, h .tableB]
  let top := (h5.getD 0 default).ew
  let sums := ((List.range V).foldl (fun (a : Array E × E) v =>
    let s := a.2 + top.getD v 0
    (a.1.push s, s)) (#[0], 0)).1
  { norm :=
      { zt := zx.last lt, zl := (zx.last (ls + lt)).extract 0 ls
        ew := fun k x => (n4.getD k.idx default).ew.getD x 0
        ewh := fun k i => (n4.getD k.idx default).ewh.getD i 0
        wsum := fun k => (n4.getD k.idx default).wsum }
    head :=
      { ew := fun k x => (h5.getD k.idx default).ew.getD x 0
        ewh := fun k i => (h5.getD k.idx default).ewh.getD i 0
        wsum := fun k => (h5.getD k.idx default).wsum
        wx := fun k => (h5.getD k.idx default).wx
        below := fun v => sums.getD v 0 }
    calls := made.zipIdx.map fun c =>
      (padKey c.2 * (1 - (c.1.map (·.2.wsum)).foldl (· + ·) 0), c.1.map (·.1)) }

end VerifiableInference.Desc.Kinds.Head
