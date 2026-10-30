-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/COpened.lean: the two tests "opened" of a key file's test on the file
(Johnson/Desc/Key/FileOk.lean), at written values: openedInBlocks at what WK's blocks say of the
roots and at the written declared rounds; openedAsTold at the closed source's declared rounds and
tenants as told. By evaluations in Lean's kernel; in openedAsTold the two sorts are first written
away by the law Johnson.Unfolds.mergeSort_eq (Johnson/Unfolds/MergeSort.lean). Negative tests: each
with the third chain's declared rounds struck (gross bends); and, for openedAsTold, one number
moved: a group as told.
Limits. At written values alone. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.WK
import Johnson.HB.LLHARD.KB4.SourceW
import Johnson.Unfolds.MergeSort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open Johnson.KB8 (declKeyFull)

set_option maxRecDepth 1000000 in
theorem openedIn_full : openedInBlocks WK.roots declKeyFull = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem openedIn_bent :
    openedInBlocks WK.roots (declKeyFull.1, declKeyFull.2.1, []) = false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem opened_full : openedAsTold YW = true := by
  unfold openedAsTold
  simp only [Johnson.Unfolds.mergeSort_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem opened_bent :
    openedAsTold { YW with D := (declKeyFull.1, declKeyFull.2.1, []) } = false := by
  unfold openedAsTold
  simp only [Johnson.Unfolds.mergeSort_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- One number moved: the group that the first chain's second tree's sampled tenant is told to
join: 101 for 100. -/
theorem opened_group_bent : openedAsTold { YW with told :=
    (toldKeyFull.1.set 1 ⟨22, 77, [⟨2, 27, 1, true, [101]⟩, ⟨0, 48, 1, false, []⟩]⟩,
      toldKeyFull.2.1, toldKeyFull.2.2) } = false := by
  unfold openedAsTold
  simp only [Johnson.Unfolds.mergeSort_eq]
  decide +kernel

end Johnson.KB4

#print axioms Johnson.KB4.openedIn_full
#print axioms Johnson.KB4.openedIn_bent
#print axioms Johnson.KB4.opened_full
#print axioms Johnson.KB4.opened_bent
#print axioms Johnson.KB4.opened_group_bent
