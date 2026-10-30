-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofBack/Trees.lean: the value of `Johnson.G.OfPlan.treesSent`'s text (`treesW`,
Johnson/Unfolds/TreesLaw.lean) at the proof file's three chains of the full size: at the written
sendings (Johnson/G/SendsWritten.lean), the written rounds' entries (Johnson/G/DryProofLit.lean) and
the offset 0, AT EVERY NAME. In pieces that Lean's kernel bears.

The three chains have 48,293, 68 and 30 rounds (`dryProofFull_length`), 82, 9 and 4 sendings (held
by no theorem here), 83, 11 and 4 trees. A name's last sign says the chain: 0 the first, 1 the
shared, 2 the second.
  `es0`, `es1`, `es2`: the written entries of a chain's rounds.
  `extra0`, `extra1`, `extra2`: the trees that go in a round that is no "SEND seed": the shared
    chain's own masks; else none.
  `rs0`, `rs1`, `rs2`: the rounds of a chain's trees, written.
  `sent0`, `sent1`, `sent2`: BY THE KERNEL, behind the laws of Johnson/Unfolds/ on `String.splitOn`
    and `String.toNat?`: the `mapM` of `sentAt` returns.
  `rounds0`, `rounds1`, `rounds2`: BY THE KERNEL, behind these laws and that on `List.mergeSort`:
    the sorted trees' rounds are the written list.
  `walk0`, `walk1`, `walk2`: BY THE KERNEL: one walk down the rounds' roots and the written list
    accepts (`walkN`, Johnson/Unfolds/WalkLaw.lean).
  `len0` …, `sorted0` …, `below0` …: the number of rounds; the written list is sorted; all of it
    lies below that number.
  **`trees0`**, **`trees1`**, **`trees2`**: `treesW` at every name, at the chain's sendings, its
    entries, the offset 0 and its extra trees is the sorted trees, numbered: by
    `Johnson.Unfolds.trees_at` and `rootsC_of_walk`.
  Negative tests, BY THE KERNEL: `walk0_no`, `walk1_no`, `walk2_no`: with one number of the written
    list raised by one the walk rejects.

Limits. The full size alone. IT SPEAKS OF WRITTEN VALUES: that the written sendings, rounds and
sizes are what `sendsOf` and the planner make of any public files is not said here; nor that the
plans there have no entry that is no round (the offset 0). The trees stand as terms, not as a
written list. Nothing on soundness. On hiding nothing.

-/
import Johnson.Unfolds.MergeSort
import Johnson.Unfolds.SliceFoldl
import Johnson.Unfolds.SplitOn
import Johnson.Unfolds.WalkRoots
import Johnson.G.SendsWritten
import Johnson.G.DryProofLit
import Johnson.Desc.Ok.PlanWritten.SizedLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofBack
open Johnson.G Johnson.G.OfPlan Johnson.Unfolds
open VerifiableInference.PlanWritten (proofSizedFull)

/-! ## The second chain -/

/-- The written entries of its rounds. -/
def es2 : List Fmt.Entry := dryProofFull.2.2.map (·.1.entry)

/-- The second chain has 30 rounds. -/
theorem len2 : es2.length = 30 := by
  unfold es2
  rw [List.length_map]
  exact congrArg (fun x => x.2.2) dryProofFull_length

/-- The trees that go in a round that is no "SEND seed". -/
def extra2 : List Sent := []

set_option maxHeartbeats 0 in
/-- BY THE KERNEL: the `mapM` of `sentAt` returns at the second chain's sendings. -/
theorem sent2 : (proofSends2.sends.mapM (sentAt "" proofSends2.codes 0)).isOk = true := by
  unfold sentAt sendTag
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- The rounds of its 4 trees, in the order of sending. -/
def rs2 : List Nat :=
  [7, 14, 20, 26]

set_option maxHeartbeats 0 in
/-- BY THE KERNEL: the sorted trees' rounds are the written list. -/
theorem rounds2 : (sortedW (sentsOf proofSends2 0) extra2).map (·.round) = rs2 := by
  unfold sortedW sentsOf extra2 sentAt sendTag
  simp only [Johnson.Unfolds.mergeSort_eq, Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- The written list is sorted. -/
theorem sorted2 : rs2.Pairwise (· ≤ ·) := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- BY THE KERNEL: one walk down the rounds' roots and the written list accepts. -/
theorem walk2 : walkN (es2.map (·.roots)) 0 rs2 = true := by
  decide +kernel

/-- Every number of the written list lies below the number of rounds. -/
theorem below2 : (rs2.all fun r => decide (r < 30)) = true := by decide +kernel

/-- **Its trees, at every name.** -/
theorem trees2 (at_ : String) :
    treesW at_ proofSends2 es2 0 extra2 = .ok (sortedW (sentsOf proofSends2 0) extra2).zipIdx :=
  trees_at sent2 rounds2 (rootsC_of_walk sorted2 walk2) len2 below2 at_

/-! ## The shared chain -/

/-- The written entries of its rounds. -/
def es1 : List Fmt.Entry := dryProofFull.2.1.map (·.1.entry)

/-- The shared chain has 68 rounds. -/
theorem len1 : es1.length = 68 := by
  unfold es1
  rw [List.length_map]
  exact congrArg (fun x => x.2.1) dryProofFull_length

/-- The trees that go in a round that is no "SEND seed". -/
def extra1 : List Sent := ownMasks proofSends1.codes proofSizedFull.batch.shape
  (dryProofFull.2.1.map (·.1.entry))

set_option maxHeartbeats 0 in
/-- BY THE KERNEL: the `mapM` of `sentAt` returns at the shared chain's sendings. -/
theorem sent1 : (proofSends1.sends.mapM (sentAt "" proofSends1.codes 0)).isOk = true := by
  unfold sentAt sendTag
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- The rounds of its 11 trees, in the order of sending. -/
def rs1 : List Nat :=
  [1, 4, 4, 17, 25, 32, 39, 44, 49, 56, 63]

set_option maxHeartbeats 0 in
/-- BY THE KERNEL: the sorted trees' rounds are the written list. -/
theorem rounds1 : (sortedW (sentsOf proofSends1 0) extra1).map (·.round) = rs1 := by
  unfold sortedW sentsOf extra1 sentAt sendTag
  simp only [Johnson.Unfolds.mergeSort_eq, Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- The written list is sorted. -/
theorem sorted1 : rs1.Pairwise (· ≤ ·) := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- BY THE KERNEL: one walk down the rounds' roots and the written list accepts. -/
theorem walk1 : walkN (es1.map (·.roots)) 0 rs1 = true := by
  decide +kernel

/-- Every number of the written list lies below the number of rounds. -/
theorem below1 : (rs1.all fun r => decide (r < 68)) = true := by decide +kernel

/-- **Its trees, at every name.** -/
theorem trees1 (at_ : String) :
    treesW at_ proofSends1 es1 0 extra1 = .ok (sortedW (sentsOf proofSends1 0) extra1).zipIdx :=
  trees_at sent1 rounds1 (rootsC_of_walk sorted1 walk1) len1 below1 at_

/-! ## The first chain -/

/-- The written entries of its rounds. -/
def es0 : List Fmt.Entry := dryProofFull.1.map (·.1.entry)

/-- The first chain has 48,293 rounds. -/
theorem len0 : es0.length = 48293 := by
  unfold es0
  rw [List.length_map]
  exact congrArg Prod.fst dryProofFull_length

/-- The trees that go in a round that is no "SEND seed". -/
def extra0 : List Sent := []

set_option maxHeartbeats 0 in
/-- BY THE KERNEL: the `mapM` of `sentAt` returns at the first chain's sendings. -/
theorem sent0 : (proofSends0.sends.mapM (sentAt "" proofSends0.codes 0)).isOk = true := by
  unfold sentAt sendTag
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- The rounds of its 83 trees, in the order of sending. -/
def rs0 : List Nat :=
  [0, 0, 1218, 1221, 1980, 3128, 3131, 3859, 5075, 5078, 5837, 6985, 6988, 7716, 8932, 8935,
   9694, 10842, 10845, 11573, 12789, 12792, 13551, 14699, 14702, 15430, 16646, 16649, 17408,
   18556, 18559, 19287, 20503, 20506, 21265, 22413, 22416, 23144, 24360, 24363, 25122, 26270,
   26273, 27001, 28217, 28220, 28979, 30127, 30130, 30858, 32074, 32077, 32836, 33984, 33987,
   34715, 35931, 35934, 36693, 37841, 37844, 38572, 39788, 39791, 40550, 41698, 41701, 42429,
   43645, 43648, 44407, 45555, 45558, 46287, 47451, 47454, 48235, 48240, 48247, 48253, 48259,
   48266, 48290]

set_option maxHeartbeats 0 in
/-- BY THE KERNEL: the sorted trees' rounds are the written list. -/
theorem rounds0 : (sortedW (sentsOf proofSends0 0) extra0).map (·.round) = rs0 := by
  unfold sortedW sentsOf extra0 sentAt sendTag
  simp only [Johnson.Unfolds.mergeSort_eq, Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- The written list is sorted. -/
theorem sorted0 : rs0.Pairwise (· ≤ ·) := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- BY THE KERNEL: one walk down the rounds' roots and the written list accepts. -/
theorem walk0 : walkN (es0.map (·.roots)) 0 rs0 = true := by
  decide +kernel

/-- Every number of the written list lies below the number of rounds. -/
theorem below0 : (rs0.all fun r => decide (r < 48293)) = true := by decide +kernel

/-- **Its trees, at every name.** -/
theorem trees0 (at_ : String) :
    treesW at_ proofSends0 es0 0 extra0 = .ok (sortedW (sentsOf proofSends0 0) extra0).zipIdx :=
  trees_at sent0 rounds0 (rootsC_of_walk sorted0 walk0) len0 below0 at_

/-! ## Negative tests, stated positively: with one number of the list bent the walk rejects -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- BY THE KERNEL: the first chain: the sixth number raised by one. -/
theorem walk0_no : walkN (es0.map (·.roots)) 0 (rs0.set 5 3129) = false := by
  decide +kernel

/-- BY THE KERNEL: the shared chain: the first number raised by one. -/
theorem walk1_no : walkN (es1.map (·.roots)) 0 (rs1.set 0 2) = false := by
  decide +kernel

/-- BY THE KERNEL: the second chain: the first number raised by one. -/
theorem walk2_no : walkN (es2.map (·.roots)) 0 (rs2.set 0 8) = false := by
  decide +kernel

end Johnson.AtFull.ProofBack

#print axioms Johnson.AtFull.ProofBack.len2
#print axioms Johnson.AtFull.ProofBack.sent2
#print axioms Johnson.AtFull.ProofBack.rounds2
#print axioms Johnson.AtFull.ProofBack.sorted2
#print axioms Johnson.AtFull.ProofBack.walk2
#print axioms Johnson.AtFull.ProofBack.below2
#print axioms Johnson.AtFull.ProofBack.trees2
#print axioms Johnson.AtFull.ProofBack.len1
#print axioms Johnson.AtFull.ProofBack.sent1
#print axioms Johnson.AtFull.ProofBack.rounds1
#print axioms Johnson.AtFull.ProofBack.sorted1
#print axioms Johnson.AtFull.ProofBack.walk1
#print axioms Johnson.AtFull.ProofBack.below1
#print axioms Johnson.AtFull.ProofBack.trees1
#print axioms Johnson.AtFull.ProofBack.len0
#print axioms Johnson.AtFull.ProofBack.sent0
#print axioms Johnson.AtFull.ProofBack.rounds0
#print axioms Johnson.AtFull.ProofBack.sorted0
#print axioms Johnson.AtFull.ProofBack.walk0
#print axioms Johnson.AtFull.ProofBack.below0
#print axioms Johnson.AtFull.ProofBack.trees0
#print axioms Johnson.AtFull.ProofBack.walk0_no
#print axioms Johnson.AtFull.ProofBack.walk1_no
#print axioms Johnson.AtFull.ProofBack.walk2_no
