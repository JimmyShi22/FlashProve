-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/Own4.lean: the turns of the iteration that solves stage 4 of the own test of a
key of full size, each from its parts.

One kernel evaluation a trial of the search for m (OnBytes/Params/Fit/TurnForward.lean says why): a
module's own memory stays far below what one evaluation of a whole turn takes. The theorems are
checked one behind the other (Elab.async false), so that their memory does not add up.

Main names.
  keyW4_turn1 and so on: what each turn returns.
  ‹turn›_p‹m›: the trial of the search at m. ‹turn›_size: the group that the search sizes.
  ‹turn›_pos: the positions that follow.

Limits. Closed statements at the typed values alone. Nothing on soundness. What the whole leaves
unsaid stands in the head of OnBytes/Params/KeyRec/Own.lean.

-/
import OnBytes.Params.KeyRec.OwnDefs
import OnBytes.Params.KeyRec.Traces

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace OnBytes.Params

theorem keyW4_turn1_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 0)
    (tailFor 0)) 3) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn1_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 0)
    (tailFor 0)) 4) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn1_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 0)
    (tailFor 0)) 8) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn1_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 0)
    (tailFor 0)) 16) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn1_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 0)
    (tailFor 0)) 32) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn1_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 0)
    (tailFor 0)) 64) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn1_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 0)
    (tailFor 0)) 128) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn1_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 0)
    (tailFor 0)) 256) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn1_p512 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 0)
    (tailFor 0)) 512) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW4_turn1_p384 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 0)
    (tailFor 0)) 384) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn1_p448 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 0)
    (tailFor 0)) 448) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn1_p480 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 0)
    (tailFor 0)) 480) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW4_turn1_p464 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 0)
    (tailFor 0)) 464) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW4_turn1_p456 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 0)
    (tailFor 0)) 456) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW4_turn1_p452 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 0)
    (tailFor 0)) 452) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW4_turn1_p450 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 0)
    (tailFor 0)) 450) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW4_turn1_p449 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 0)
    (tailFor 0)) 449) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn1_size : sizeGroup recordSet .once (turnGroup keyWShape4 (tailFor 0) (tailFor 0))
    ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = groupOfM (turnGroup keyWShape4
    (tailFor 0) (tailFor 0)) 449 :=
  congrArg (groupOfM (turnGroup keyWShape4 (tailFor 0) (tailFor 0)))
    (trace449 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 0)
      (tailFor 0)) m) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩)
      keyW4_turn1_p3 keyW4_turn1_p4 keyW4_turn1_p8 keyW4_turn1_p16 keyW4_turn1_p32 keyW4_turn1_p64
      keyW4_turn1_p128 keyW4_turn1_p256 keyW4_turn1_p512 keyW4_turn1_p384 keyW4_turn1_p448
      keyW4_turn1_p480 keyW4_turn1_p464 keyW4_turn1_p456 keyW4_turn1_p452 keyW4_turn1_p450
      keyW4_turn1_p449)

theorem keyW4_turn1_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyWShape4 (tailFor 0) (tailFor 0)) 449)).mainAt.agree (margin recordSet) = 39 := by
  decide +kernel

/-- Turn 1 of stage 4, from 0 positions. -/
theorem keyW4_turn1 : turn recordSet .once
    ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ keyWShape4
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨13, 256, 0, true⟩, ⟨13, 64, 0, true⟩, 3, 3, 1, .johnson, 449⟩ 39 :=
  turn_more_of (by decide +kernel) keyW4_turn1_size keyW4_turn1_p449 keyW4_turn1_pos (by decide)

theorem keyW4_turn2_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 39)
    (tailFor 39)) 3) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn2_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 39)
    (tailFor 39)) 4) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn2_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 39)
    (tailFor 39)) 8) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn2_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 39)
    (tailFor 39)) 16) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn2_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 39)
    (tailFor 39)) 32) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn2_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 39)
    (tailFor 39)) 64) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn2_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 39)
    (tailFor 39)) 128) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn2_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 39)
    (tailFor 39)) 256) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn2_p512 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 39)
    (tailFor 39)) 512) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW4_turn2_p384 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 39)
    (tailFor 39)) 384) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn2_p448 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 39)
    (tailFor 39)) 448) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn2_p480 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 39)
    (tailFor 39)) 480) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW4_turn2_p464 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 39)
    (tailFor 39)) 464) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn2_p472 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 39)
    (tailFor 39)) 472) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW4_turn2_p468 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 39)
    (tailFor 39)) 468) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn2_p470 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 39)
    (tailFor 39)) 470) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW4_turn2_p469 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 39)
    (tailFor 39)) 469) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn2_size : sizeGroup recordSet .once (turnGroup keyWShape4 (tailFor 39) (tailFor
    39)) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = groupOfM (turnGroup
    keyWShape4 (tailFor 39) (tailFor 39)) 469 :=
  congrArg (groupOfM (turnGroup keyWShape4 (tailFor 39) (tailFor 39)))
    (trace469 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 39)
      (tailFor 39)) m) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩)
      keyW4_turn2_p3 keyW4_turn2_p4 keyW4_turn2_p8 keyW4_turn2_p16 keyW4_turn2_p32 keyW4_turn2_p64
      keyW4_turn2_p128 keyW4_turn2_p256 keyW4_turn2_p512 keyW4_turn2_p384 keyW4_turn2_p448
      keyW4_turn2_p480 keyW4_turn2_p464 keyW4_turn2_p472 keyW4_turn2_p468 keyW4_turn2_p470
      keyW4_turn2_p469)

theorem keyW4_turn2_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyWShape4 (tailFor 39) (tailFor 39)) 469)).mainAt.agree (margin recordSet) = 41 := by
  decide +kernel

/-- Turn 2 of stage 4, from 39 positions. -/
theorem keyW4_turn2 : turn recordSet .once
    ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ keyWShape4
    (tailFor 39) (tailFor 39) 39 =
      .more ⟨⟨13, 256, 39, true⟩, ⟨13, 64, 39, true⟩, 3, 3, 1, .johnson, 469⟩ 41 :=
  turn_more_of (by decide +kernel) keyW4_turn2_size keyW4_turn2_p469 keyW4_turn2_pos (by decide)

theorem keyW4_turn3_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 41)
    (tailFor 41)) 3) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn3_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 41)
    (tailFor 41)) 4) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn3_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 41)
    (tailFor 41)) 8) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn3_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 41)
    (tailFor 41)) 16) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn3_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 41)
    (tailFor 41)) 32) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn3_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 41)
    (tailFor 41)) 64) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn3_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 41)
    (tailFor 41)) 128) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn3_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 41)
    (tailFor 41)) 256) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn3_p512 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 41)
    (tailFor 41)) 512) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW4_turn3_p384 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 41)
    (tailFor 41)) 384) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn3_p448 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 41)
    (tailFor 41)) 448) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn3_p480 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 41)
    (tailFor 41)) 480) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW4_turn3_p464 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 41)
    (tailFor 41)) 464) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn3_p472 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 41)
    (tailFor 41)) 472) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW4_turn3_p468 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 41)
    (tailFor 41)) 468) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn3_p470 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 41)
    (tailFor 41)) 470) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW4_turn3_p471 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 41)
    (tailFor 41)) 471) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW4_turn3_size : sizeGroup recordSet .once (turnGroup keyWShape4 (tailFor 41) (tailFor
    41)) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ = groupOfM (turnGroup
    keyWShape4 (tailFor 41) (tailFor 41)) 470 :=
  congrArg (groupOfM (turnGroup keyWShape4 (tailFor 41) (tailFor 41)))
    (trace470 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyWShape4 (tailFor 41)
      (tailFor 41)) m) ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩)
      keyW4_turn3_p3 keyW4_turn3_p4 keyW4_turn3_p8 keyW4_turn3_p16 keyW4_turn3_p32 keyW4_turn3_p64
      keyW4_turn3_p128 keyW4_turn3_p256 keyW4_turn3_p512 keyW4_turn3_p384 keyW4_turn3_p448
      keyW4_turn3_p480 keyW4_turn3_p464 keyW4_turn3_p472 keyW4_turn3_p468 keyW4_turn3_p470
      keyW4_turn3_p471)

theorem keyW4_turn3_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyWShape4 (tailFor 41) (tailFor 41)) 470)).mainAt.agree (margin recordSet) = 41 := by
  decide +kernel

/-- Turn 3 of stage 4, from 41 positions. -/
theorem keyW4_turn3 : turn recordSet .once
    ⟨stageCubeBits keyWShape4, 1, 4 + 3 * max keyW3.main.r 1024⟩ keyWShape4
    (tailFor 41) (tailFor 41) 41 =
      .settled keyW4 41 :=
  turn_settled_of (by decide +kernel) keyW4_turn3_size keyW4_turn3_p470 keyW4_turn3_pos (by decide)

end OnBytes.Params

#print axioms OnBytes.Params.keyW4_turn1
#print axioms OnBytes.Params.keyW4_turn2
#print axioms OnBytes.Params.keyW4_turn3
