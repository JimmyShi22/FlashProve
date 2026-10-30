-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Port/FoNums.lean: the public numbers of a sub-proof's lookup, as functions of
the verifier's own record h : OnBytes.Model.Forest.Shape (with pub filled in). Numbers alone: no
proof, no Mathlib, all computable.

The typed lookup (forA, OnBytes/Tie/Pv/Lookup/Forest/FoA.lean) takes its sizes, cells, padding and
mask places from here.

Points. The verifier keeps a point of k coordinates as an array whose place 0 belongs to the top bit
of an index. The typed blocks number coordinates by bits: coordinate t is bit t. So place i of the
array holds coordinate k - 1 - i (placeOf). The verifier's «variable t» of a sumcheck (levelRounds,
OnBytes/Model/Psc.lean) reads and stores at place mu - 1 - t, so it is coordinate t, and its lists
of variables (orderDefault, orderForestRange) are orders of coordinates as they stand. Where the
verifier walks an array from place 0 up (the leaves, the bits) the order of coordinates is the list
of placeOf's.

Main definitions: nOf, kOf, t0Of, io, fst, co, tauN (the record's arrays, read with the verifier's
own defaults); w, planes, n, v', several; placeOf; ordK, ordT, ordE, ordB (round j binds the
variable in place j of the list); fK, fT (the call of a key, of a row), keyOf, rowOf, cellOf,
cellRC; padRow, padCount, pads; S, nMasks, nClaims (the numbering of the scalars that the prover
sends: TwNums' functions scs, firstOf, place, pTie to pBit, reIdx, which read v, d, w and planes of
S h and nothing else; S h is not meant to pass TwNums.Sizes.ok (its padAt is left empty), and
TwNums' ordK, keyEntry, padRow are not to be read at it); ok (what is asked of the public numbers,
as one Bool).
Limits: the file holds no theorem. keyOf, rowOf, cellOf, cellRC, padRow, padCount and the numbering
S are this file's own descriptions, written from the text of OnBytes/Model/Forest.lean and
OnBytes/Model/Look.lean; no statement compares them with what Forest.pad, Forest.join or
Forest.planesAt compute. That ok h follows from the success of Forest.shape and Forest.pubAsk is
shape_ok (OnBytes/Tie/Pv/Lookup/Port/FoShape.lean).

-/
import OnBytes.Model.Look
import OnBytes.Model.RoundSizes
import OnBytes.Tie.Pv.Lookup.Port.TwNums

set_option autoImplicit false

namespace FoNums
open OnBytes.Model

abbrev Sh : Type := Forest.Shape

/-! ### the record's arrays, read with the verifier's own defaults -/
def nOf (h : Sh) (c : Nat) : Nat := ((h.calls[c]?).map (·.n)).getD 0
def kOf (h : Sh) (c : Nat) : Nat := ((h.calls[c]?).map (·.k)).getD 0
def t0Of (h : Sh) (c : Nat) : Nat := ((h.calls[c]?).map (·.t0)).getD 0
def io (h : Sh) (c : Nat) : Nat := h.iota.getD c 0
def fst (h : Sh) (c : Nat) : Nat := h.first.getD c 0
def co (h : Sh) (y : Nat) : Nat := h.callOf.getD y 0
/-- row t of call c's table, as a number (Call.tauAt). It is below the prime where callAsk has taken
the call and t < 2^k; ok below does not test that. -/
def tauN (h : Sh) (c t : Nat) : Nat := ((h.calls.getD c {}).tauAt t).toNat

/-! ### the sizes -/
/-- 2^w slots of planes (Forest.tie draws a point of 5 coordinates; planForest has mu := 5; callAsk
asks kappa = 5) -/
def w : Nat := 5
/-- all count (Forest.tie: 31 steps, 32 roots) -/
def planes : Nat := 2 ^ w
/-- the tie has n + 1 steps; n + 2 planes count -/
def n : Nat := planes - 2
/-- a key's number has v' + 1 bits -/
def v' (h : Sh) : Nat := h.v - 1
/-- is the shift drawn (Forest.draws) -/
def several (h : Sh) : Bool := decide (1 < h.NC)

/-! ### array places and coordinates -/
/-- the array's place of coordinate t (and back: it is its own inverse below k) -/
def placeOf (k t : Nat) : Nat := k - 1 - t

/-! ### the orders, as lists of VARIABLES: round j binds variable (list)[j] -/
/-- the list that Forest.pad passes to Forest.level at key level l, to the letter -/
def ordK (h : Sh) (l : Nat) :
    List Nat := if l + 1 = h.v then Forest.orderForestRange l h.rK else orderDefault l
/-- the list that Forest.pad passes to Forest.level at table level l -/
def ordT (l : Nat) : List Nat := orderDefault (w + l)
/-- the leaves (Forest.pad): round j reads place j of the point's array -/
def ordE (h : Sh) : List Nat := (List.range (w + h.d)).map (placeOf (w + h.d))
/-- the bits (Forest.pad): round j reads place j of the reversed draw -/
def ordB (h : Sh) : List Nat := (List.range (w + h.d)).map (placeOf (w + h.d))

/-! ### keys, rows, cells -/
/-- the call of key X: the tree's number is the low rK bits; a tree of padding alone: call 0 (the
head of Forest.lean; Forest.draws, Forest.join) -/
def fK (h : Sh) (X : Nat) : Nat := if X % 2 ^ h.rK < h.NT then co h (X % 2 ^ h.rK) else 0
/-- the call of row u: the number c is the low cK bits; from NC on the last call's (joinedTableAt)
-/
def fT (h : Sh) (u : Nat) : Nat := min (u % 2 ^ h.cK) (h.NC - 1)
/-- key X is entry (index) of call (call)'s key vector; none: a tree of padding alone (Forest.pad:
zk c is the last iota_c coordinates of zy, then zx) -/
def keyOf (h : Sh) (X : Nat) : Option (Nat × Nat) :=
  if X % 2 ^ h.rK < h.NT then
    some (co h (X % 2 ^ h.rK), X /
        2 ^ h.rK + 2 ^ h.dT * (X % 2 ^ h.rK % 2 ^ io h (co h (X % 2 ^ h.rK))))
  else none
/-- row u of the joined table is row (row) of call (call)'s table: a shorter table is repeated
(Forest.pad reads tableAt at the last k_c coordinates of the row) -/
def rowOf (h : Sh) (u : Nat) : Nat × Nat := (fT h u, u / 2 ^ h.cK % 2 ^ kOf h (fT h u))
/-- bit j of row u's count: (t, c, j); none from NC on: the verifier has no cell there (planesAt) -/
def cellOf (h : Sh) (u j : Nat) : Option (Nat × Nat × Nat) :=
  if u % 2 ^ h.cK < h.NC then some (u / 2 ^ h.cK, u % 2 ^ h.cK, j) else none
/-- lm is the caller's number: the planes' matrix has 2^lm rows. The cell (t, c, j) lies in row (the
low lm − 5 bits of t | j) and column (c | the other bits of t) (planesAt, phiB). -/
def cellRC (h : Sh) (lm : Nat) (x : Nat × Nat × Nat) : Nat × Nat :=
  ((x.1 % 2 ^ (lm - w)) * planes + x.2.2, x.2.1 * 2 ^ (h.kT + w - lm) + x.1 / 2 ^ (lm - w))

/-! ### the padding -/
/-- the joined table's row that call c's padding keys hold -/
def padRow (h : Sh) (c : Nat) : Nat := c + 2 ^ h.cK * t0Of h c
/-- how many padding keys hold it: those of c's trees; for call 0 also the trees of padding alone -/
def padCount (h : Sh) (c : Nat) : Nat :=
  (((List.range h.NT).filter fun y => co h y = c).map fun y => h.pub.getD y 0).sum + if c = 0 then
      h.emptyKeys else 0
/-- (row, how many) -/
def pads (h : Sh) : List (Nat × Nat) := (List.range h.NC).map fun c => (padRow h c, padCount h c)

/-! ### the numbering of the scalars sent
nine rK: the nine variables that the last key level binds first (Forest.orderForestRange). S h: the
record that TwNums' numbering reads; that numbering reads its fields v, d, w and planes alone. -/
def nine (rK : Nat) : List Nat := [2, 1, 0, 5, 4, 3, 8, 7, 6].map (rK + ·)
def S (h : Sh) : TwNums.Sizes :=
  { v := h.v, d := h.d, w := w, planes := planes, first := nine h.rK, pads := pads h, padAt := [] }
def nMasks (h : Sh) : Nat := (S h).nMasks
def nClaims (h : Sh) : Nat := (S h).nClaims

/-! ### what is asked of the public numbers, as one Bool -/
/-- Each clause is a test of Forest.shape, callAsk or pubAsk, or follows from their loops: shape_ok
(OnBytes/Tie/Pv/Lookup/Port/FoShape.lean). -/
def ok (h : Sh) : Bool :=
  decide (10 ≤ h.dT) && decide (1 ≤ h.NC) && decide (h.NC ≤ 2 ^ h.cK) && decide (h.NT ≤ 2 ^ h.rK) &&
      decide (h.v < 32) &&
  h.pub.size == h.NT && h.calls.size == h.NC &&
  ((List.range h.NT).all fun y => decide (co h y < h.NC) && decide (fst h (co h y) ≤ y) && decide
      (y < fst h (co h y) + 2 ^ io h (co h y))) &&
  ((List.range h.NC).all fun c => decide (t0Of h c < 2 ^ kOf h c) && decide (kOf h c ≤ h.kT) && nOf
      h c == io h c + h.dT &&
    (List.range (2 ^ io h c)).all fun b => decide (fst h c + b < h.NT) && co h (fst h c + b) == c &&
        (fst h c + b) % 2 ^ io h c == b) &&
  ((pads h).all fun e => decide (e.1 < 2 ^ h.d)) && decide (((pads h).map Prod.snd).sum ≤ 2 ^ h.v)
      &&
  decide (h.kT ≤ 16) && decide (h.NC ≤ 16) && decide (2 ^ (h.d + 32) < OnBytes.pW.toNat)

end FoNums
