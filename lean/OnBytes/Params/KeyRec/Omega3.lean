-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/Omega3.lean: the turns of the iteration that solves stage 3 of Omega's test of
a key of full size, each from its parts.

One kernel evaluation a trial of the search for m (OnBytes/Params/Fit/TurnForward.lean says why): a
module's own memory stays far below what one evaluation of a whole turn takes. The theorems are
checked one behind the other (Elab.async false), so that their memory does not add up.

Main names.
  keyO3_turn1 and so on: what each turn returns.
  ‹turn›_p‹m›: the trial of the search at m. ‹turn›_size: the group that the search sizes.
  ‹turn›_pos: the positions that follow.

Limits. Closed statements at the typed values alone. Nothing on soundness. What the whole leaves
unsaid stands in the head of OnBytes/Params/KeyRec/Omega.lean.

-/
import OnBytes.Params.KeyRec.OmegaDefs
import OnBytes.Params.KeyRec.Traces

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace OnBytes.Params

theorem keyO3_turn1_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 0)
    (tailFor 0)) 3) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn1_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 0)
    (tailFor 0)) 4) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn1_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 0)
    (tailFor 0)) 8) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn1_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 0)
    (tailFor 0)) 16) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn1_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 0)
    (tailFor 0)) 32) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn1_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 0)
    (tailFor 0)) 64) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn1_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 0)
    (tailFor 0)) 128) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn1_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 0)
    (tailFor 0)) 256) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn1_p512 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 0)
    (tailFor 0)) 512) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyO3_turn1_p384 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 0)
    (tailFor 0)) 384) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn1_p448 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 0)
    (tailFor 0)) 448) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn1_p480 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 0)
    (tailFor 0)) 480) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn1_p496 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 0)
    (tailFor 0)) 496) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyO3_turn1_p488 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 0)
    (tailFor 0)) 488) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyO3_turn1_p484 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 0)
    (tailFor 0)) 484) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyO3_turn1_p482 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 0)
    (tailFor 0)) 482) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn1_p483 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 0)
    (tailFor 0)) 483) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyO3_turn1_size : sizeGroup recordSet .once (turnGroup keyOShape3 (tailFor 0) (tailFor 0))
    ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = groupOfM (turnGroup keyOShape3
    (tailFor 0) (tailFor 0)) 482 :=
  congrArg (groupOfM (turnGroup keyOShape3 (tailFor 0) (tailFor 0)))
    (trace482 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 0)
      (tailFor 0)) m) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩)
      keyO3_turn1_p3 keyO3_turn1_p4 keyO3_turn1_p8 keyO3_turn1_p16 keyO3_turn1_p32 keyO3_turn1_p64
      keyO3_turn1_p128 keyO3_turn1_p256 keyO3_turn1_p512 keyO3_turn1_p384 keyO3_turn1_p448
      keyO3_turn1_p480 keyO3_turn1_p496 keyO3_turn1_p488 keyO3_turn1_p484 keyO3_turn1_p482
      keyO3_turn1_p483)

theorem keyO3_turn1_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyOShape3 (tailFor 0) (tailFor 0)) 482)).mainAt.agree (margin recordSet) = 49 := by
  decide +kernel

/-- Turn 1 of stage 3, from 0 positions. -/
theorem keyO3_turn1 : turn recordSet .once
    ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ keyOShape3
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨14, 1024, 0, true⟩, ⟨13, 64, 0, true⟩, 4, 3, 1, .johnson, 482⟩ 49 :=
  turn_more_of (by decide +kernel) keyO3_turn1_size keyO3_turn1_p482 keyO3_turn1_pos (by decide)

theorem keyO3_turn2_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 49)
    (tailFor 49)) 3) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn2_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 49)
    (tailFor 49)) 4) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn2_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 49)
    (tailFor 49)) 8) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn2_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 49)
    (tailFor 49)) 16) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn2_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 49)
    (tailFor 49)) 32) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn2_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 49)
    (tailFor 49)) 64) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn2_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 49)
    (tailFor 49)) 128) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn2_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 49)
    (tailFor 49)) 256) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn2_p512 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 49)
    (tailFor 49)) 512) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyO3_turn2_p384 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 49)
    (tailFor 49)) 384) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn2_p448 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 49)
    (tailFor 49)) 448) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn2_p480 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 49)
    (tailFor 49)) 480) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn2_p496 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 49)
    (tailFor 49)) 496) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyO3_turn2_p488 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 49)
    (tailFor 49)) 488) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn2_p492 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 49)
    (tailFor 49)) 492) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyO3_turn2_p490 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 49)
    (tailFor 49)) 490) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyO3_turn2_p489 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 49)
    (tailFor 49)) 489) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO3_turn2_size : sizeGroup recordSet .once (turnGroup keyOShape3 (tailFor 49) (tailFor
    49)) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ = groupOfM (turnGroup
    keyOShape3 (tailFor 49) (tailFor 49)) 489 :=
  congrArg (groupOfM (turnGroup keyOShape3 (tailFor 49) (tailFor 49)))
    (trace489 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyOShape3 (tailFor 49)
      (tailFor 49)) m) ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩)
      keyO3_turn2_p3 keyO3_turn2_p4 keyO3_turn2_p8 keyO3_turn2_p16 keyO3_turn2_p32 keyO3_turn2_p64
      keyO3_turn2_p128 keyO3_turn2_p256 keyO3_turn2_p512 keyO3_turn2_p384 keyO3_turn2_p448
      keyO3_turn2_p480 keyO3_turn2_p496 keyO3_turn2_p488 keyO3_turn2_p492 keyO3_turn2_p490
      keyO3_turn2_p489)

theorem keyO3_turn2_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyOShape3 (tailFor 49) (tailFor 49)) 489)).mainAt.agree (margin recordSet) = 49 := by
  decide +kernel

/-- Turn 2 of stage 3, from 49 positions. -/
theorem keyO3_turn2 : turn recordSet .once
    ⟨stageCubeBits keyOShape3, 1, 4 + 3 * max keyO2.main.r 1024⟩ keyOShape3
    (tailFor 49) (tailFor 49) 49 =
      .settled keyO3 49 :=
  turn_settled_of (by decide +kernel) keyO3_turn2_size keyO3_turn2_p489 keyO3_turn2_pos (by decide)

end OnBytes.Params

#print axioms OnBytes.Params.keyO3_turn1
#print axioms OnBytes.Params.keyO3_turn2
