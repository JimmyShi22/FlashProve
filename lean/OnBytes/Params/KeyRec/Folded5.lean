-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/Folded5.lean: the turns of the iteration that solves stage 5 of the folded
row's test of a key of full size, each from its parts.

One kernel evaluation a trial of the search for m (OnBytes/Params/Fit/TurnForward.lean says why): a
module's own memory stays far below what one evaluation of a whole turn takes. The theorems are
checked one behind the other (Elab.async false), so that their memory does not add up.

Main names.
  keyU5_turn1 and so on: what each turn returns.
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

theorem keyU5_turn1_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 0)
    (tailFor 0)) 3) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn1_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 0)
    (tailFor 0)) 4) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn1_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 0)
    (tailFor 0)) 8) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn1_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 0)
    (tailFor 0)) 16) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn1_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 0)
    (tailFor 0)) 32) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn1_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 0)
    (tailFor 0)) 64) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn1_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 0)
    (tailFor 0)) 128) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn1_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 0)
    (tailFor 0)) 256) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn1_p512 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 0)
    (tailFor 0)) 512) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU5_turn1_p384 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 0)
    (tailFor 0)) 384) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn1_p448 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 0)
    (tailFor 0)) 448) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn1_p480 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 0)
    (tailFor 0)) 480) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn1_p496 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 0)
    (tailFor 0)) 496) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU5_turn1_p488 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 0)
    (tailFor 0)) 488) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU5_turn1_p484 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 0)
    (tailFor 0)) 484) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU5_turn1_p482 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 0)
    (tailFor 0)) 482) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn1_p483 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 0)
    (tailFor 0)) 483) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU5_turn1_size : sizeGroup recordSet .once (turnGroup keyUShape5 (tailFor 0) (tailFor 0))
    ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = groupOfM (turnGroup keyUShape5
    (tailFor 0) (tailFor 0)) 482 :=
  congrArg (groupOfM (turnGroup keyUShape5 (tailFor 0) (tailFor 0)))
    (trace482 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 0)
      (tailFor 0)) m) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩)
      keyU5_turn1_p3 keyU5_turn1_p4 keyU5_turn1_p8 keyU5_turn1_p16 keyU5_turn1_p32 keyU5_turn1_p64
      keyU5_turn1_p128 keyU5_turn1_p256 keyU5_turn1_p512 keyU5_turn1_p384 keyU5_turn1_p448
      keyU5_turn1_p480 keyU5_turn1_p496 keyU5_turn1_p488 keyU5_turn1_p484 keyU5_turn1_p482
      keyU5_turn1_p483)

theorem keyU5_turn1_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyUShape5 (tailFor 0) (tailFor 0)) 482)).mainAt.agree (margin recordSet) = 49 := by
  decide +kernel

/-- Turn 1 of stage 5, from 0 positions. -/
theorem keyU5_turn1 : turn recordSet .once
    ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ keyUShape5
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨14, 512, 0, true⟩, ⟨14, 1024, 0, true⟩, 0, 0, 1, .johnson, 482⟩ 49 :=
  turn_more_of (by decide +kernel) keyU5_turn1_size keyU5_turn1_p482 keyU5_turn1_pos (by decide)

theorem keyU5_turn2_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 49)
    (tailFor 49)) 3) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn2_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 49)
    (tailFor 49)) 4) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn2_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 49)
    (tailFor 49)) 8) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn2_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 49)
    (tailFor 49)) 16) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn2_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 49)
    (tailFor 49)) 32) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn2_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 49)
    (tailFor 49)) 64) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn2_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 49)
    (tailFor 49)) 128) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn2_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 49)
    (tailFor 49)) 256) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn2_p512 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 49)
    (tailFor 49)) 512) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU5_turn2_p384 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 49)
    (tailFor 49)) 384) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn2_p448 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 49)
    (tailFor 49)) 448) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn2_p480 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 49)
    (tailFor 49)) 480) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn2_p496 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 49)
    (tailFor 49)) 496) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU5_turn2_p488 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 49)
    (tailFor 49)) 488) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn2_p492 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 49)
    (tailFor 49)) 492) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU5_turn2_p490 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 49)
    (tailFor 49)) 490) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU5_turn2_p489 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 49)
    (tailFor 49)) 489) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU5_turn2_size : sizeGroup recordSet .once (turnGroup keyUShape5 (tailFor 49) (tailFor
    49)) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ = groupOfM (turnGroup
    keyUShape5 (tailFor 49) (tailFor 49)) 489 :=
  congrArg (groupOfM (turnGroup keyUShape5 (tailFor 49) (tailFor 49)))
    (trace489 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyUShape5 (tailFor 49)
      (tailFor 49)) m) ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩)
      keyU5_turn2_p3 keyU5_turn2_p4 keyU5_turn2_p8 keyU5_turn2_p16 keyU5_turn2_p32 keyU5_turn2_p64
      keyU5_turn2_p128 keyU5_turn2_p256 keyU5_turn2_p512 keyU5_turn2_p384 keyU5_turn2_p448
      keyU5_turn2_p480 keyU5_turn2_p496 keyU5_turn2_p488 keyU5_turn2_p492 keyU5_turn2_p490
      keyU5_turn2_p489)

theorem keyU5_turn2_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyUShape5 (tailFor 49) (tailFor 49)) 489)).mainAt.agree (margin recordSet) = 49 := by
  decide +kernel

/-- Turn 2 of stage 5, from 49 positions. -/
theorem keyU5_turn2 : turn recordSet .once
    ⟨stageCubeBits keyUShape5, 1, 4 + 3 * max keyU4.main.r 1024⟩ keyUShape5
    (tailFor 49) (tailFor 49) 49 =
      .settled keyU5 49 :=
  turn_settled_of (by decide +kernel) keyU5_turn2_size keyU5_turn2_p489 keyU5_turn2_pos (by decide)

end OnBytes.Params

#print axioms OnBytes.Params.keyU5_turn1
#print axioms OnBytes.Params.keyU5_turn2
