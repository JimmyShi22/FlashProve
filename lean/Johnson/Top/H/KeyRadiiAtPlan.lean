-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/KeyRadiiAtPlan.lean: the 18 radii that Johnson/Top/H/KeyTowers.lean writes out for the
stages of a key file's four proximity tests are the planner's: the upper end of the distance that
the planner's analysis gives for the stage's group, times the length of its main code, rounded down
(Params.upperRadius, OnBytes/Params/JohnsonLaws.lean). Each by one evaluation in Lean's kernel.

The groups are the typed groups of OnBytes/Params/KeyStagesRecordRanges.lean, KeyStagesRecordFolded,
KeyStagesRecordOmega and KeyStagesRecordOwn, which are the planner's at every file in the goals'
scope (Johnson/Top/H/KeySizesAtPlan.lean).

Main names: radiusOf; radius_R1 and its like; radii_written.

Limits. radiusOf is this file's own name for the number; KeyRows.lean's head says in words that the
written radii were taken so. That a typed test at such a radius has a small error is not said.
Nothing on soundness.

-/
import OnBytes.Params.MorePrices
import OnBytes.Params.KeyStagesRecordFolded
import OnBytes.Params.KeyStagesRecordOmega
import OnBytes.Params.KeyStagesRecordOwn
import OnBytes.Params.KeyStagesRecordRanges
import Johnson.Top.H.KeyTowers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.AtPlan
open OnBytes.Params Johnson.Top.H

/-- The upper end of the planner's distance for a group, in positions of its main code. -/
def radiusOf (g : GroupSize) : ℕ :=
  upperRadius (analysisOfM recordSet g).mainAt.delta (wordOf g.main).n

theorem radius_R1 : radiusOf keyR1 = eRng1 := by decide +kernel
theorem radius_R2 : radiusOf keyR2 = eRng2 := by decide +kernel
theorem radius_R3 : radiusOf keyR3 = eRng3 := by decide +kernel
theorem radius_R4 : radiusOf keyR4 = eRng4 := by decide +kernel
theorem radius_U1 : radiusOf keyU1 = eRow1 := by decide +kernel
theorem radius_U2 : radiusOf keyU2 = eRow2 := by decide +kernel
theorem radius_U3 : radiusOf keyU3 = eRow3 := by decide +kernel
theorem radius_U4 : radiusOf keyU4 = eRow4 := by decide +kernel
theorem radius_U5 : radiusOf keyU5 = eRow5 := by decide +kernel
theorem radius_O1 : radiusOf keyO1 = eOmg1 := by decide +kernel
theorem radius_O2 : radiusOf keyO2 = eOmg2 := by decide +kernel
theorem radius_O3 : radiusOf keyO3 = eOmg3 := by decide +kernel
theorem radius_O4 : radiusOf keyO4 = eOmg4 := by decide +kernel
theorem radius_W1 : radiusOf keyW1 = eOwn1 := by decide +kernel
theorem radius_W2 : radiusOf keyW2 = eOwn2 := by decide +kernel
theorem radius_W3 : radiusOf keyW3 = eOwn3 := by decide +kernel
theorem radius_W4 : radiusOf keyW4 = eOwn4 := by decide +kernel
theorem radius_W5 : radiusOf keyW5 = eOwn5 := by decide +kernel

/-- **The 18 written radii are the planner's.** -/
theorem radii_written : keyRStages.map (radiusOf ·.g) = [eRng1, eRng2, eRng3, eRng4] ∧
    keyUStages.map (radiusOf ·.g) = [eRow1, eRow2, eRow3, eRow4, eRow5] ∧
    keyOStages.map (radiusOf ·.g) = [eOmg1, eOmg2, eOmg3, eOmg4] ∧
    keyWStages.map (radiusOf ·.g) = [eOwn1, eOwn2, eOwn3, eOwn4, eOwn5] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show [radiusOf keyR1, radiusOf keyR2, radiusOf keyR3, radiusOf keyR4] = _
    rw [radius_R1, radius_R2, radius_R3, radius_R4]
  · show [radiusOf keyU1, radiusOf keyU2, radiusOf keyU3, radiusOf keyU4, radiusOf keyU5] = _
    rw [radius_U1, radius_U2, radius_U3, radius_U4, radius_U5]
  · show [radiusOf keyO1, radiusOf keyO2, radiusOf keyO3, radiusOf keyO4] = _
    rw [radius_O1, radius_O2, radius_O3, radius_O4]
  · show [radiusOf keyW1, radiusOf keyW2, radiusOf keyW3, radiusOf keyW4, radiusOf keyW5] = _
    rw [radius_W1, radius_W2, radius_W3, radius_W4, radius_W5]

/-- The same distance in positions of the group's mask code. A group has one distance: the planner's
analysis has "the mask code at the same distance" (OnBytes/Params/Group.lean, Analysis). That the
written radius of a mask message was meant so is this file's reading. -/
def maskRadiusOf (g : GroupSize) : ℕ :=
  upperRadius (analysisOfM recordSet g).mainAt.delta (wordOf g.mask).n

/-- The written radius 6130 of the index-mask message (in the own group) and of the split's mask
message (in Omega's group). -/
theorem radius_masks : maskRadiusOf keyW1 = 6130 ∧ maskRadiusOf keyO1 = 6130 := by
  decide +kernel

end Lk6.AtPlan

#print axioms Lk6.AtPlan.radii_written
#print axioms Lk6.AtPlan.radius_masks
