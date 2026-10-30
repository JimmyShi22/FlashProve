-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/TreesOpened.lean: closed facts on the three written lists of rounds of the
proof file at the full size (dryProofFull, Johnson/G/DryProofLit.lean), for the field told of PlanAt
(Johnson/Desc/K1/Law/NewAtSending.lean). A law file; no running text imports it. Why they are asked.
The data of a file give a tree the shape UNDER WHICH SOME ROUND OF THE FILE OPENS IT (Three.shapeAt,
OnBytes/Three/Data.lean), and a bare shape (depth 0, one word a column) if no round opens it. The
field told asks that the data's shape of each tree of a sending has the depth and the width that the
IOP as written in Lean declares. At a tree that is never opened it would be false.
  laidFull, laid_83: for each tree of the first chain's 82 written sendings (
      proofSendsFull), in order: the depth and the width of its layout (layTrees at the written
      codes): 83 trees
  asLaidB here R: every opening in the list R that names a tree of the first chain names one of the
      83 and bears that tree's layout's depth and width
  all_as_laid: ⋆ so it is in all three lists: ONE WALK OF Lean's KERNEL OVER ALL 48,293 + 68 + 30
      ROUNDS
  openRounds: the 31 rounds of the first list that open a tree, each with the trees' numbers: a
      table, off a print of the evaluator; the kernel holds it against the list
  trees_opened: ⋆ EACH OF THE 83 TREES IS OPENED: 81 by a round of the first list itself (three a
      segment at its proximity test's round; six behind the segments), the index masks' tree (1) and
      W's (82) by a round of the third list: Lean's kernel
  bent_rejects, depth_rejects, unopened_rejects: the negative tests: with one width, with one depth
      of the table turned the walk rejects; a tree number 83 of the first chain is opened by nothing

What is not claimed. The sentence on Three.shapeAt itself (the first opening in the data's list that
bears the tree's number through the whole file has these two numbers): it follows from the two ⋆ by
membership alone, given that the first list counts 83 roots: NOT TYPED HERE. That the rounds of a
file in scope are the written lists: left to other files. That the declared depth and width are the
layout's: tells_reads, tells_digits (Johnson/Desc/K1/Law/TellsAtFifty.lean). Nothing on soundness.

-/
import Johnson.G.DryProofLit
import Johnson.G.SendsWritten
import OnBytes.Three.Data

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open OnBytes OnBytes.Three Johnson.G

/-- Depth and width of each tree that the first chain's written sendings lay, in order. -/
def laidFull : List (Nat × Nat) :=
  proofSendsFull.1.sends.flatMap fun s =>
    ((layTrees proofSendsFull.1.codes s.sent.toArray).map fun L =>
      L.shapes.toList.map fun t => (t.logN, t.mainWidth + t.maskWidth)).getD []

/-- Every opening in R that names a tree of the first chain bears the table's two numbers. -/
def asLaidB (tab : List (Nat × Nat)) (here : Nat) (R : OnBytes.Params.Rounds) : Bool :=
  R.all fun r => r.1.opens.all fun o =>
    match named here o.2 with
    | some (0, n) => tab[n]? == some (o.1.a, o.1.W)
    | _ => true

def allAsLaidB (tab : List (Nat × Nat)) : Bool :=
  asLaidB tab 0 dryProofFull.1 && asLaidB tab 1 dryProofFull.2.1 && asLaidB tab 2 dryProofFull.2.2

/-- The rounds of the first list that open a tree, with the trees' numbers. -/
def openRounds : List (Nat × List Nat) :=
  [(1981, [0, 2, 3]), (3860, [4, 5, 6]), (5838, [7, 8, 9]), (7717, [10, 11, 12]),
   (9695, [13, 14, 15]), (11574, [16, 17, 18]), (13552, [19, 20, 21]), (15431, [22, 23, 24]),
   (17409, [25, 26, 27]), (19288, [28, 29, 30]), (21266, [31, 32, 33]), (23145, [34, 35, 36]),
   (25123, [37, 38, 39]), (27002, [40, 41, 42]), (28980, [43, 44, 45]), (30859, [46, 47, 48]),
   (32837, [49, 50, 51]), (34716, [52, 53, 54]), (36694, [55, 56, 57]), (38573, [58, 59, 60]),
   (40551, [61, 62, 63]), (42430, [64, 65, 66]), (44408, [67, 68, 69]), (46288, [70, 71, 72]),
   (48236, [73, 74, 75]), (48241, [76]), (48248, [77]), (48254, [78]), (48260, [79]),
   (48267, [80]), (48269, [81])]

/-- Does the round name the first chain's tree n? -/
def opensB (here n : Nat) (r : Fmt.Round × List Fmt.Stored) : Bool :=
  r.1.opens.any fun o => named here o.2 == some (0, n)

/-- Tree n of the first chain is opened: at its round of the table, or by the third list. -/
def openedB (n : Nat) : Bool :=
  (openRounds.any fun x => x.2.contains n &&
    ((dryProofFull.1.drop x.1).head?).any (opensB 0 n)) || dryProofFull.2.2.any (opensB 2 n)

set_option maxRecDepth 1000000 in
theorem laid_83 : laidFull.length = 83 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- ⋆ **Every opening of a tree of the first chain is under its layout's depth and width.** -/
theorem all_as_laid : allAsLaidB laidFull = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- ⋆ **Each of the 83 trees is opened.** -/
theorem trees_opened : ((List.range 83).all openedB) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: one width turned. -/
theorem bent_rejects :
    allAsLaidB (laidFull.set 40 ((laidFull.getD 40 (0, 0)).1, (laidFull.getD 40 (0, 0)).2 + 1)) =
      false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: one depth turned. -/
theorem depth_rejects :
    allAsLaidB (laidFull.set 82 ((laidFull.getD 82 (0, 0)).1 + 1, (laidFull.getD 82 (0, 0)).2)) =
      false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the first chain has no tree number 83 that is opened. -/
theorem unopened_rejects : openedB 83 = false := by decide +kernel

end HashBuild

#print axioms HashBuild.laid_83
#print axioms HashBuild.all_as_laid
#print axioms HashBuild.trees_opened
#print axioms HashBuild.bent_rejects
#print axioms HashBuild.depth_rejects
#print axioms HashBuild.unopened_rejects
