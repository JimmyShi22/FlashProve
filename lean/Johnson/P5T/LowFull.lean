-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/LowFull.lean: THE FIFTH TIE's CLOSED TEST `lowAtB`
(Johnson/Desc/First/Link/Law/FifthTieLow.lean: "every tree that a rider's pins name lies below the
first tree of the sub-protocol at that place") ACCEPTS AT THE WRITTEN VALUES, AT ALL 100 PLACES OF
THE KIND K9: BY LEAN's KERNEL. With what it ranges over, how tight it is, negative tests, and WHAT
IT DOES NOT SEE. Definitions with code and seven theorems, each by `decide +kernel`. No public
file is read.
At which values. The numbers: `NFull` (Johnson/P5T/FenceFull.lean): the written seats' core with
the counts of trees laid off the written tellings. The first tree at place k: `baseFull k` :=
`NFull.treesAt placesCut[k]?`. The places: `k9Places` := the 75 quiet places and the 25 of the one
equation (Johnson/Desc/First/Link/Law/FifthTieRiders.lean).
  `low_full`: **the test accepts at all of `k9Places`.**
  `low_ranges`: 100 places, all different; at each at least 1 and at most 8 trees of pins ride;
  295 in all: so no accept is idle.
  `low_tight`: the first trees run from 4 to 76; the first tree less the greatest tree that rides
  is at least 1, AND IS 1 AT 25 PLACES; at most 75.
  `low_rejects`: two negative tests: at the first tree 0, and at the greatest tree that rides, the
  test accepts at no place.
  `low_rejects_seats`: three negative tests on the seats: every sent tenant 1 tree higher:
  accepted at 75 places of 100; every kept tenant 200 higher: at 76; the index masks' seat 200
  higher: at none.
  `low_sorts`: at how many places a pin of each sort rides: sent 25, kept 25, the index masks'
  100, W's 0.
  `low_blind`: **A MEASURED LIMIT: W's seat 200 trees higher is accepted at all 100 places** (no
  pin of W's rides at a place of K9): THE TEST SAYS NOTHING OF W's SEAT; and it accepts every kept
  tenant, or the index masks' seat, 1 tree higher at all 100.
Every number here was printed by the evaluator before it was typed.
Limits. The written values alone: that they are a verifier's is another file's
(Johnson/P5T/LowAtMg.lean). The full size alone. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5T.FenceFull
import Johnson.Desc.First.Link.Law.FifthTieLow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (lowAtB ridersAt quietAt eqAt)

/-- The 100 places of the kind K9 at which the fifth tie asks the test. -/
def k9Places : List Nat := quietAt ++ eqAt

/-- The count of trees in front of place k, off the written tellings. -/
def baseFull (k : Nat) : Nat := NFull.treesAt placesCut[k]?

/-- The trees that an item's pins name. -/
def pinTrees (N : Numbers) : Item → List Nat
  | .pin m t => (N.sent m t).map (·.1)
  | .pinKept m => (N.keptOf m).map (·.1)
  | .pinI => [N.index.1]
  | .pinV => [N.w.1]
  | _ => []

/-- The trees that ride at place k; the greatest of them. -/
def ridesFull (k : Nat) : List Nat := (ridersAt k).flatMap (pinTrees NFull)
def topFull (k : Nat) : Nat := (ridesFull k).foldl max 0

/-- At how many of the 100 places the test accepts, at given numbers and first trees. -/
def lowCount (N : Numbers) (base : Nat → Nat) : Nat :=
  (k9Places.filter fun k => lowAtB N (base k) k).length

set_option maxRecDepth 1000000 in
/-- **By the kernel: the test accepts at all 100 places.** -/
theorem low_full : (k9Places.all fun k => lowAtB NFull (baseFull k) k) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- By the kernel: what it ranges over. -/
theorem low_ranges :
    (k9Places.length, k9Places.eraseDups.length,
      (k9Places.map fun k => (ridesFull k).length).foldl min 1000000,
      (k9Places.map fun k => (ridesFull k).length).foldl max 0,
      (k9Places.map fun k => (ridesFull k).length).foldl (· + ·) 0) = (100, 100, 1, 8, 295) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- By the kernel: how tight it is. -/
theorem low_tight :
    ((k9Places.map baseFull).foldl min 1000000, (k9Places.map baseFull).foldl max 0,
      (k9Places.map fun k => baseFull k - topFull k).foldl min 1000000,
      (k9Places.filter fun k => baseFull k - topFull k == 1).length,
      (k9Places.map fun k => baseFull k - topFull k).foldl max 0) = (4, 76, 1, 25, 75) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- By the kernel: two negative tests on the first tree: accepted at no place. -/
theorem low_rejects : (lowCount NFull fun _ => 0, lowCount NFull topFull) = (0, 0) := by
  decide +kernel

/-- The numbers with every sent tenant d trees higher. -/
def upSent (d : Nat) : Numbers :=
  { NFull with sent := fun m t => (NFull.sent m t).map fun x => (x.1 + d, x.2) }

/-- The numbers with every kept tenant d trees higher. -/
def upKept (d : Nat) : Numbers :=
  { NFull with keptOf := fun m => (NFull.keptOf m).map fun x => (x.1 + d, x.2) }

/-- The numbers with the seat of the index masks' message d trees higher. -/
def upIndex (d : Nat) : Numbers := { NFull with index := (NFull.index.1 + d, NFull.index.2) }

/-- The numbers with W's seat d trees higher. -/
def upW (d : Nat) : Numbers := { NFull with w := (NFull.w.1 + d, NFull.w.2) }

set_option maxRecDepth 1000000 in
/-- By the kernel: three negative tests on the seats: at how many places each is still accepted. -/
theorem low_rejects_seats :
    (lowCount (upSent 1) baseFull, lowCount (upKept 200) baseFull,
      lowCount (upIndex 200) baseFull) = (75, 76, 0) := by decide +kernel

/-- At how many of the 100 places an item with p rides. -/
def sortCount (p : Item → Bool) : Nat := (k9Places.filter fun k => (ridersAt k).any p).length

set_option maxRecDepth 1000000 in
/-- By the kernel: at how many places a pin of each sort rides. -/
theorem low_sorts :
    (sortCount fun i => match i with | .pin _ _ => true | _ => false,
      sortCount fun i => match i with | .pinKept _ => true | _ => false,
      sortCount fun i => match i with | .pinI => true | _ => false,
      sortCount fun i => match i with | .pinV => true | _ => false) = (25, 25, 100, 0) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **By the kernel: a measured limit**: W's seat 200 trees higher, every kept tenant 1 higher, the
index masks' seat 1 higher: each is accepted at all 100 places. -/
theorem low_blind :
    (lowCount (upW 200) baseFull, lowCount (upKept 1) baseFull, lowCount (upIndex 1) baseFull) =
      (100, 100, 100) := by decide +kernel

end P5T

#print axioms P5T.low_full
#print axioms P5T.low_ranges
#print axioms P5T.low_tight
#print axioms P5T.low_rejects
#print axioms P5T.low_rejects_seats
#print axioms P5T.low_sorts
#print axioms P5T.low_blind
