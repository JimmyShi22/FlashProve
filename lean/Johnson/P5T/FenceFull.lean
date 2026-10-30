-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/FenceFull.lean: THE TABLE's TEST `fenceFit` AS A CLOSED FACT AT THE FULL SIZE: at the
core of the table's numbers off the written sendings (`N0Full`, Johnson/P5T/PlanSeatsFull.lean),
filled off the written cut's places and tellings (`placesCut`, `toldCut`,
Johnson/Desc/First/CutWritten.lean). Seven definitions, eight theorems.
Why. The test says: at every border of the first chain, every sampled tenant of a pin that is open
there sits in a tree that the sub-protocols in front have told. It reads public data alone: the
sendings, the request's shape, the declared rounds and the cut. The verifier's list of entry tests
(`LPFD.lawsAsk`, Johnson/Desc/Laid/ProofAsks.lean) holds the declared rounds to their written
values in its first eight rows, and the three others in its first thirteen. There the test is a
fact on written values: outside `verify()`.
  `NFull`: the numbers: `N0Full.withTold placesCut toldCut`. `opensFull`: the open sets at the
  borders.
  `fence_walk_full`: by Lean's kernel: ONE walk over the open sets accepts (`fenceFrom`,
  Johnson/Desc/First/FenceWalk.lean).
  `fence_full`: **`fenceFit NFull linksFull placesCut = true`**: by `fenceFit_of_walk`, with no
  further evaluation.
THAT THE ACCEPT IS NOT EMPTY, AND WHAT THE TEST SEES, each by the kernel:
  `fence_ranges`: 359 borders; the walk ranges over 1,899 (border, tenant) pairs; at 356 of the
  borders at least one sampled tenant stands.
  `fence_tight`: the least of "trees told at the border" less "the tenant's tree" is 1, and it is
  1 at 500 of the 1,899 pairs: there the test has no slack.
  `fence_rejects`: three negative tests on what is told: nothing told; every telling one border
  late; the last sub-protocol that tells a tree (row 356 of the cut) mute: the walk rejects each.
  `fence_rejects_seats`: three negative tests on the seats: every tenant of a sending, the seat of
  the index masks' message, the seat of W: one tree higher: the walk rejects each.
  `fence_kept`: the core names 36 kept tenants; a kept pin is open at 100 borders; 145 of the
  1,899 pairs come of kept pins; among these the slack is 3 at the least and 4 at the most.
  `fence_blind_kept`: **A LIMIT OF THE TEST: with every KEPT tenant one tree higher, or two, the
  walk still accepts; with three it rejects.**
Limits. No tie to the verifier's own value is typed here (Johnson/P5T/FenceTie.lean has it). The
written values rest on prints of Lean's evaluator (their files' heads). `fenceFit` bounds a
tenant's tree from above and says nothing else of it: a seat that is wrong by less than its slack
passes. This file wants about 12 GB of memory to compile. The full size alone. No probability: no
soundness follows.
Terms: lean/GLOSSARY.md.


-/
import Johnson.P5T.PlanSeatsFull
import Johnson.Desc.First.CutWritten
import Johnson.Desc.First.FenceWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (linksFull)

/-- The table's numbers at the written values: the core, filled off the written cut. -/
def NFull : Numbers := N0Full.withTold placesCut toldCut

/-- The open sets at the 359 borders, at the written places. -/
def opensFull : List (List Item) := openSets linksFull placesCut (start linksFull)

set_option maxRecDepth 1000000 in
/-- By the kernel: one walk over the open sets accepts. -/
theorem fence_walk_full : fenceFrom N0Full toldCut 0 opensFull = true := by decide +kernel

/-- **The table's test on the fence holds at the written values.** -/
theorem fence_full : fenceFit NFull linksFull placesCut = true :=
  fenceFit_of_walk N0Full linksFull placesCut toldCut placesCut_nodup fence_walk_full

set_option maxRecDepth 1000000 in
/-- By the kernel: how many borders; over how many (border, tenant) pairs the walk ranges; at how
many borders at least one sampled tenant stands. -/
theorem fence_ranges :
    (opensFull.length, fenceCount N0Full opensFull,
      (opensFull.filter fun O => !(sampledIn N0Full O).isEmpty).length) = (359, 1899, 356) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- By the kernel: the least of "trees told at the border" less "the tenant's tree" is 1; at how
many pairs it is 1. -/
theorem fence_tight :
    ((opensFull.zipIdx.flatMap fun y =>
        (sampledIn N0Full y.1).map fun x => treesTold toldCut y.2 - x.1).foldl min 1000,
      (opensFull.zipIdx.flatMap fun y => (sampledIn N0Full y.1).filter fun x =>
        treesTold toldCut y.2 - x.1 == 1).length) = (1, 500) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- By the kernel: three negative tests on what is told: nothing told; every telling one border
late; the last sub-protocol that tells a tree mute. -/
theorem fence_rejects :
    (fenceFrom N0Full (toldCut.map fun _ => []) 0 opensFull,
      fenceFrom N0Full ([] :: toldCut) 0 opensFull,
      fenceFrom N0Full (toldCut.take 356) 0 opensFull) = (false, false, false) := by
  decide +kernel

/-- The core with every tenant of a sending one tree higher. -/
def plantSent : Numbers :=
  { N0Full with sent := fun m t => (N0Full.sent m t).map fun x => (x.1 + 1, x.2) }

/-- The core with every kept tenant d trees higher. -/
def plantKept (d : Nat) : Numbers :=
  { N0Full with keptOf := fun m => (N0Full.keptOf m).map fun x => (x.1 + d, x.2) }

/-- The kept pins among the open items. -/
def keptPins (O : List Item) : List Item :=
  O.filter fun i => match i with | .pinKept _ => true | _ => false

/-- The core with the seat of the index masks' message one tree higher. -/
def plantIndex : Numbers := { N0Full with index := (N0Full.index.1 + 1, N0Full.index.2) }

/-- The core with W's seat one tree higher. -/
def plantW : Numbers := { N0Full with w := (N0Full.w.1 + 1, N0Full.w.2) }

set_option maxRecDepth 1000000 in
/-- By the kernel: three negative tests on the seats: the walk rejects each. -/
theorem fence_rejects_seats :
    (fenceFrom plantSent toldCut 0 opensFull, fenceFrom plantIndex toldCut 0 opensFull,
      fenceFrom plantW toldCut 0 opensFull) = (false, false, false) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- By the kernel: how many kept tenants the core names; at how many borders a kept pin is open; how
many pairs come of kept pins; the least and the greatest slack among these. -/
theorem fence_kept :
    (((List.range 25).map fun m => (N0Full.keptOf m).length).sum,
      (opensFull.filter fun O => !(keptPins O).isEmpty).length,
      (opensFull.map fun O => (sampledIn N0Full (keptPins O)).length).sum,
      (opensFull.zipIdx.flatMap fun y => (sampledIn N0Full (keptPins y.1)).map fun x =>
        treesTold toldCut y.2 - x.1).foldl min 1000,
      (opensFull.zipIdx.flatMap fun y => (sampledIn N0Full (keptPins y.1)).map fun x =>
        treesTold toldCut y.2 - x.1).foldl max 0) = (36, 100, 145, 3, 4) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A limit of the test**, by the kernel: with every kept tenant one tree higher, or two, the walk
still accepts; with three it rejects. -/
theorem fence_blind_kept :
    (fenceFrom (plantKept 1) toldCut 0 opensFull, fenceFrom (plantKept 2) toldCut 0 opensFull,
      fenceFrom (plantKept 3) toldCut 0 opensFull) = (true, true, false) := by
  decide +kernel

end P5T

#print axioms P5T.fence_walk_full
#print axioms P5T.fence_full
#print axioms P5T.fence_ranges
#print axioms P5T.fence_tight
#print axioms P5T.fence_rejects
#print axioms P5T.fence_rejects_seats
#print axioms P5T.fence_kept
#print axioms P5T.fence_blind_kept
