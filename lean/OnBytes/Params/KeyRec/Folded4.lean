-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/Folded4.lean: the turns of the iteration that solves stage 4 of the folded
row's test of a key of full size, each from its parts.

One kernel evaluation a trial of the search for m (OnBytes/Params/Fit/TurnForward.lean says why): a
module's own memory stays far below what one evaluation of a whole turn takes. The theorems are
checked one behind the other (Elab.async false), so that their memory does not add up.

Main names.
  keyU4_turn1 and so on: what each turn returns.
  ‹turn›_p‹m›: the trial of the search at m. ‹turn›_size: the group that the search sizes.
  ‹turn›_pos: the positions that follow.

Limits. Closed statements at the typed values alone. Nothing on soundness. What the whole leaves
unsaid stands in the head of OnBytes/Params/KeyRec/Folded.lean.

-/
import OnBytes.Params.KeyRec.FoldedDefs
import OnBytes.Params.KeyRec.Traces

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace OnBytes.Params

theorem keyU4_turn1_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 0)
    (tailFor 0)) 3) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn1_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 0)
    (tailFor 0)) 4) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn1_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 0)
    (tailFor 0)) 8) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn1_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 0)
    (tailFor 0)) 16) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn1_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 0)
    (tailFor 0)) 32) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn1_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 0)
    (tailFor 0)) 64) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn1_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 0)
    (tailFor 0)) 128) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn1_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 0)
    (tailFor 0)) 256) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn1_p512 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 0)
    (tailFor 0)) 512) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn1_p1024 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 0)
    (tailFor 0)) 1024) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU4_turn1_p768 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 0)
    (tailFor 0)) 768) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU4_turn1_p640 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 0)
    (tailFor 0)) 640) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU4_turn1_p576 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 0)
    (tailFor 0)) 576) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU4_turn1_p544 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 0)
    (tailFor 0)) 544) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU4_turn1_p528 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 0)
    (tailFor 0)) 528) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn1_p536 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 0)
    (tailFor 0)) 536) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU4_turn1_p532 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 0)
    (tailFor 0)) 532) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU4_turn1_p530 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 0)
    (tailFor 0)) 530) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn1_p531 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 0)
    (tailFor 0)) 531) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU4_turn1_size : sizeGroup recordSet .once (turnGroup keyUShape4 (tailFor 0) (tailFor 0))
    ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = groupOfM (turnGroup keyUShape4
    (tailFor 0) (tailFor 0)) 530 :=
  congrArg (groupOfM (turnGroup keyUShape4 (tailFor 0) (tailFor 0)))
    (trace530 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 0)
      (tailFor 0)) m) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩)
      keyU4_turn1_p3 keyU4_turn1_p4 keyU4_turn1_p8 keyU4_turn1_p16 keyU4_turn1_p32 keyU4_turn1_p64
      keyU4_turn1_p128 keyU4_turn1_p256 keyU4_turn1_p512 keyU4_turn1_p1024 keyU4_turn1_p768
      keyU4_turn1_p640 keyU4_turn1_p576 keyU4_turn1_p544 keyU4_turn1_p528 keyU4_turn1_p536
      keyU4_turn1_p532 keyU4_turn1_p530 keyU4_turn1_p531)

theorem keyU4_turn1_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyUShape4 (tailFor 0) (tailFor 0)) 530)).mainAt.agree (margin recordSet) = 49 := by
  decide +kernel

/-- Turn 1 of stage 4, from 0 positions. -/
theorem keyU4_turn1 : turn recordSet .once
    ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ keyUShape4
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨13, 512, 0, true⟩, ⟨12, 256, 0, true⟩, 4, 2, 1, .johnson, 530⟩ 49 :=
  turn_more_of (by decide +kernel) keyU4_turn1_size keyU4_turn1_p530 keyU4_turn1_pos (by decide)

theorem keyU4_turn2_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 49)
    (tailFor 49)) 3) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn2_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 49)
    (tailFor 49)) 4) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn2_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 49)
    (tailFor 49)) 8) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn2_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 49)
    (tailFor 49)) 16) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn2_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 49)
    (tailFor 49)) 32) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn2_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 49)
    (tailFor 49)) 64) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn2_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 49)
    (tailFor 49)) 128) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn2_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 49)
    (tailFor 49)) 256) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn2_p512 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 49)
    (tailFor 49)) 512) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU4_turn2_p384 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 49)
    (tailFor 49)) 384) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn2_p448 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 49)
    (tailFor 49)) 448) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn2_p480 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 49)
    (tailFor 49)) 480) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn2_p496 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 49)
    (tailFor 49)) 496) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn2_p504 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 49)
    (tailFor 49)) 504) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn2_p508 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 49)
    (tailFor 49)) 508) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn2_p510 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 49)
    (tailFor 49)) 510) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU4_turn2_p509 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 49)
    (tailFor 49)) 509) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU4_turn2_size : sizeGroup recordSet .once (turnGroup keyUShape4 (tailFor 49) (tailFor
    49)) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = groupOfM (turnGroup
    keyUShape4 (tailFor 49) (tailFor 49)) 508 :=
  congrArg (groupOfM (turnGroup keyUShape4 (tailFor 49) (tailFor 49)))
    (trace508 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 49)
      (tailFor 49)) m) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩)
      keyU4_turn2_p3 keyU4_turn2_p4 keyU4_turn2_p8 keyU4_turn2_p16 keyU4_turn2_p32 keyU4_turn2_p64
      keyU4_turn2_p128 keyU4_turn2_p256 keyU4_turn2_p512 keyU4_turn2_p384 keyU4_turn2_p448
      keyU4_turn2_p480 keyU4_turn2_p496 keyU4_turn2_p504 keyU4_turn2_p508 keyU4_turn2_p510
      keyU4_turn2_p509)

theorem keyU4_turn2_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyUShape4 (tailFor 49) (tailFor 49)) 508)).mainAt.agree (margin recordSet) = 52 := by
  decide +kernel

/-- Turn 2 of stage 4, from 49 positions. -/
theorem keyU4_turn2 : turn recordSet .once
    ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ keyUShape4
    (tailFor 49) (tailFor 49) 49 =
      .more ⟨⟨13, 512, 49, true⟩, ⟨12, 256, 49, true⟩, 4, 2, 1, .johnson, 508⟩ 52 :=
  turn_more_of (by decide +kernel) keyU4_turn2_size keyU4_turn2_p508 keyU4_turn2_pos (by decide)

theorem keyU4_turn3_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 52)
    (tailFor 52)) 3) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn3_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 52)
    (tailFor 52)) 4) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn3_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 52)
    (tailFor 52)) 8) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn3_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 52)
    (tailFor 52)) 16) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn3_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 52)
    (tailFor 52)) 32) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn3_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 52)
    (tailFor 52)) 64) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn3_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 52)
    (tailFor 52)) 128) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn3_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 52)
    (tailFor 52)) 256) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn3_p512 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 52)
    (tailFor 52)) 512) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU4_turn3_p384 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 52)
    (tailFor 52)) 384) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn3_p448 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 52)
    (tailFor 52)) 448) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn3_p480 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 52)
    (tailFor 52)) 480) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn3_p496 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 52)
    (tailFor 52)) 496) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn3_p504 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 52)
    (tailFor 52)) 504) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn3_p508 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 52)
    (tailFor 52)) 508) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn3_p510 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 52)
    (tailFor 52)) 510) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU4_turn3_p509 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 52)
    (tailFor 52)) 509) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU4_turn3_size : sizeGroup recordSet .once (turnGroup keyUShape4 (tailFor 52) (tailFor
    52)) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ = groupOfM (turnGroup
    keyUShape4 (tailFor 52) (tailFor 52)) 509 :=
  congrArg (groupOfM (turnGroup keyUShape4 (tailFor 52) (tailFor 52)))
    (trace509 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyUShape4 (tailFor 52)
      (tailFor 52)) m) ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩)
      keyU4_turn3_p3 keyU4_turn3_p4 keyU4_turn3_p8 keyU4_turn3_p16 keyU4_turn3_p32 keyU4_turn3_p64
      keyU4_turn3_p128 keyU4_turn3_p256 keyU4_turn3_p512 keyU4_turn3_p384 keyU4_turn3_p448
      keyU4_turn3_p480 keyU4_turn3_p496 keyU4_turn3_p504 keyU4_turn3_p508 keyU4_turn3_p510
      keyU4_turn3_p509)

theorem keyU4_turn3_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyUShape4 (tailFor 52) (tailFor 52)) 509)).mainAt.agree (margin recordSet) = 52 := by
  decide +kernel

/-- Turn 3 of stage 4, from 52 positions. -/
theorem keyU4_turn3 : turn recordSet .once
    ⟨stageCubeBits keyUShape4, 1, 4 + 3 * max keyU3.main.r 1024⟩ keyUShape4
    (tailFor 52) (tailFor 52) 52 =
      .settled keyU4 52 :=
  turn_settled_of (by decide +kernel) keyU4_turn3_size keyU4_turn3_p509 keyU4_turn3_pos (by decide)

end OnBytes.Params

#print axioms OnBytes.Params.keyU4_turn1
#print axioms OnBytes.Params.keyU4_turn2
#print axioms OnBytes.Params.keyU4_turn3
