-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyScopeNums.lean: THEOREMS BY THE KERNEL's EVALUATION, EACH A TEST THAT CAN FAIL. Four premises that a theorem on the key file in other files names (the frame holds the trees 0 · 1 · 5 at the depths of the three sampled messages' codes; the ranges' test has a stage), AT THE WRITTEN CONSTANTS that scope gives: the key file's data Johnson.G.writtenKFull (Johnson/Flat/Dec/FitAtWritten.lean) and the sized key Lk6.AtPlan.keyFull (Johnson/Goal/PlanValues/KeySizedReturns.lean).
OBJECT: (fr₁ writtenKFull).all · keyFull.ranges.x.stages. USER: f0_written | f1_written | f2_written (Johnson/RunOne/KeyPinwStored.lean). The Boolean is holdsB, unfolded, to the letter of its text: Fr.all.any fun t => t.no == j && decide (a ≤ t.a).
HOW THE KERNEL GETS THROUGH. A first text asked «decide +kernel» of allOf writtenKFull outright: Lean ended with code 134. Here, by the library's own tools for long chains: the data over the twin that the kernel can evaluate (dKeyFull · writtenKFull_eq, FitAtWritten.lean) · the sums and the walk with the carried number evaluated at each step (sum_eq_sumE · treeShE_eq, Johnson/G/TestsEager.lean).
  t1_d | t2_d | n3_d   the three chains send 6 · 11 · 4 trees
  allOf_of             the frame's list at given numbers of trees, over the eager walk (general)
  trees_written        the frame's whole list: 21 trees with their depths
  holds0 | holds1 | holds5   the three, true
  holds0_no | holds1_no | holds5_no | holds21_no   the controls: one more than the depth; a tree that the file has not: false
  stages_full | hst_full   four stages
  allOf_at | at32 | a_written     WholeD.at turns the stored table's depth alone; it is 32 already
What is not claimed. That the data of any run, row or piece are writtenKFull, or any source's sized key keyFull: scope's theorems, elsewhere. Nothing on soundness.

-/
import Johnson.RunOne.KeySeatNumsW2
import Johnson.RunOne.KeyRowsAtFk
import Johnson.Flat.Dec.FitAtWritten
import Johnson.Goal.PlanValues.KeySizedReturns

set_option autoImplicit false

namespace Johnson.RunOne.KeyLetters

open OnBytes OnBytes.Maker
open VerifiableInference.Desc.Sound (allOf nAll nTrees)
open Johnson.RunOne.KeyRows23 (fr₁)
open Johnson.Pack (aOf)
open Johnson.Top.H (csKey shIdx shMul)
open Johnson.G (writtenKFull dKeyFull writtenKFull_eq sum_eq_sumE treeShE treeShE_eq)
open Lk6.AtPlan (keyFull)

set_option maxRecDepth 1000000 in
theorem t1_d : dKeyFull.t₁ = 6 := by
  show (dKeyFull.ds₁.map (·.trees.length)).sum = 6
  rw [sum_eq_sumE]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem t2_d : dKeyFull.t₂ = 11 := by
  show (dKeyFull.ds₂.map (·.trees.length)).sum = 11
  rw [sum_eq_sumE]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem n3_d : nTrees dKeyFull.ds₃ = 4 := by
  show (dKeyFull.ds₃.map (·.trees.length)).sum = 4
  rw [sum_eq_sumE]
  decide +kernel

/-- The frame's list of trees, at given numbers of trees, over the eager walk. -/
theorem allOf_of (D : WholeD) (a b c : ℕ) (h1 : D.t₁ = a) (h2 : D.t₂ = b) (h3 : nTrees D.ds₃ = c) :
    (allOf D).map (fun t => (t.no, t.a)) = (List.range (a + b + c)).map fun j =>
      (j, ((if j < a then (treeShE D.ds₁ j).map (·.a) else if j - a < b then (treeShE D.ds₂ (j - a)).map (·.a)
        else (treeShE D.ds₃ (j - a - b)).map (·.a))).getD 0) := by
  unfold allOf nAll
  rw [h1, h2, h3, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  show (j, (D.depth j).getD 0) = _
  unfold WholeD.depth
  rw [h1, h2, treeShE_eq, treeShE_eq, treeShE_eq]

set_option maxRecDepth 1000000 in
theorem trees_d : (allOf dKeyFull).map (fun t => (t.no, t.a)) =
    [(0, 13), (1, 22), (2, 19), (3, 17), (4, 20), (5, 22), (6, 24), (7, 22), (8, 13), (9, 21), (10, 17), (11, 13), (12, 14), (13, 13),
      (14, 18), (15, 14), (16, 15), (17, 18), (18, 15), (19, 13), (20, 15)] := by
  rw [allOf_of dKeyFull 6 11 4 t1_d t2_d n3_d]
  decide +kernel

/-- **The frame's whole list at the written data.** -/
theorem trees_written : (allOf writtenKFull).map (fun t => (t.no, t.a)) =
    [(0, 13), (1, 22), (2, 19), (3, 17), (4, 20), (5, 22), (6, 24), (7, 22), (8, 13), (9, 21), (10, 17), (11, 13), (12, 14), (13, 13),
      (14, 18), (15, 14), (16, 15), (17, 18), (18, 15), (19, 13), (20, 15)] := by
  rw [writtenKFull_eq]
  exact trees_d

/-- A test on the frame's trees that reads number and depth alone, off the list of pairs. -/
theorem any_pairs (D : WholeD) (g : ℕ × ℕ → Bool) :
    ((fr₁ D).all.any fun t => g (t.no, t.a)) = ((allOf D).map fun t => (t.no, t.a)).any g := by
  show (allOf D).any _ = _
  rw [List.any_map]
  rfl

theorem holds0 : ((fr₁ writtenKFull).all.any fun t => t.no == 0 && decide (aOf csKey shIdx ≤ t.a)) = true :=
  (any_pairs writtenKFull fun p => p.1 == 0 && decide (aOf csKey shIdx ≤ p.2)).trans (by rw [trees_written]; decide +kernel)
theorem holds1 : ((fr₁ writtenKFull).all.any fun t => t.no == 1 && decide (aOf csKey shMul ≤ t.a)) = true :=
  (any_pairs writtenKFull fun p => p.1 == 1 && decide (aOf csKey shMul ≤ p.2)).trans (by rw [trees_written]; decide +kernel)
theorem holds5 : ((fr₁ writtenKFull).all.any fun t => t.no == 5 && decide (aOf csKey Johnson.Top.H.shW ≤ t.a)) = true :=
  (any_pairs writtenKFull fun p => p.1 == 5 && decide (aOf csKey Johnson.Top.H.shW ≤ p.2)).trans (by rw [trees_written]; decide +kernel)

theorem holds0_no : ((fr₁ writtenKFull).all.any fun t => t.no == 0 && decide (aOf csKey shIdx + 1 ≤ t.a)) = false :=
  (any_pairs writtenKFull fun p => p.1 == 0 && decide (aOf csKey shIdx + 1 ≤ p.2)).trans (by rw [trees_written]; decide +kernel)
theorem holds1_no : ((fr₁ writtenKFull).all.any fun t => t.no == 1 && decide (aOf csKey shMul + 1 ≤ t.a)) = false :=
  (any_pairs writtenKFull fun p => p.1 == 1 && decide (aOf csKey shMul + 1 ≤ p.2)).trans (by rw [trees_written]; decide +kernel)
theorem holds5_no : ((fr₁ writtenKFull).all.any fun t => t.no == 5 && decide (aOf csKey Johnson.Top.H.shW + 1 ≤ t.a)) = false :=
  (any_pairs writtenKFull fun p => p.1 == 5 && decide (aOf csKey Johnson.Top.H.shW + 1 ≤ p.2)).trans (by rw [trees_written]; decide +kernel)
theorem holds21_no : ((fr₁ writtenKFull).all.any fun t => t.no == 21 && decide (0 ≤ t.a)) = false :=
  (any_pairs writtenKFull fun p => p.1 == 21 && decide (0 ≤ p.2)).trans (by rw [trees_written]; decide +kernel)

theorem stages_full : keyFull.ranges.x.stages.length = 4 := by decide +kernel
theorem hst_full : 0 < keyFull.ranges.x.stages.length := by decide +kernel

/-- WholeD.at turns the stored table's depth alone: the frame's list does not read it. -/
theorem allOf_at (D : WholeD) (a : ℕ) : allOf (D.at a) = allOf D := rfl
theorem at32 : allOf (writtenKFull.at 32) = allOf writtenKFull := allOf_at writtenKFull 32
theorem a_written : writtenKFull.a = 32 := rfl

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.t1_d
#print axioms Johnson.RunOne.KeyLetters.t2_d
#print axioms Johnson.RunOne.KeyLetters.n3_d
#print axioms Johnson.RunOne.KeyLetters.allOf_of
#print axioms Johnson.RunOne.KeyLetters.trees_written
#print axioms Johnson.RunOne.KeyLetters.holds0
#print axioms Johnson.RunOne.KeyLetters.holds1
#print axioms Johnson.RunOne.KeyLetters.holds5
#print axioms Johnson.RunOne.KeyLetters.holds0_no
#print axioms Johnson.RunOne.KeyLetters.holds1_no
#print axioms Johnson.RunOne.KeyLetters.holds5_no
#print axioms Johnson.RunOne.KeyLetters.holds21_no
#print axioms Johnson.RunOne.KeyLetters.stages_full
#print axioms Johnson.RunOne.KeyLetters.hst_full
#print axioms Johnson.RunOne.KeyLetters.allOf_at
#print axioms Johnson.RunOne.KeyLetters.at32
#print axioms Johnson.RunOne.KeyLetters.a_written
