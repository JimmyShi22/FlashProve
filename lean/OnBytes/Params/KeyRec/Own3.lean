-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/Own3.lean: the turns of the iteration that solves stage 3 of the own test of a
key of full size, each from its parts.

One kernel evaluation a trial of the search for m (OnBytes/Params/Fit/TurnForward.lean says why): a
module's own memory stays far below what one evaluation of a whole turn takes. The theorems are
checked one behind the other (Elab.async false), so that their memory does not add up.

Main names.
  keyW3_turn1 and so on: what each turn returns.
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

theorem keyW3_turn1_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 0)
    (tailFor 0)) 3) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW3_turn1_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 0)
    (tailFor 0)) 4) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW3_turn1_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 0)
    (tailFor 0)) 8) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW3_turn1_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 0)
    (tailFor 0)) 16) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW3_turn1_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 0)
    (tailFor 0)) 32) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW3_turn1_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 0)
    (tailFor 0)) 64) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW3_turn1_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 0)
    (tailFor 0)) 128) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW3_turn1_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 0)
    (tailFor 0)) 256) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW3_turn1_p512 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 0)
    (tailFor 0)) 512) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW3_turn1_p384 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 0)
    (tailFor 0)) 384) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW3_turn1_p448 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 0)
    (tailFor 0)) 448) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW3_turn1_p416 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 0)
    (tailFor 0)) 416) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW3_turn1_p432 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 0)
    (tailFor 0)) 432) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW3_turn1_p424 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 0)
    (tailFor 0)) 424) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW3_turn1_p420 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 0)
    (tailFor 0)) 420) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW3_turn1_p422 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 0)
    (tailFor 0)) 422) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW3_turn1_p421 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 0)
    (tailFor 0)) 421) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW3_turn1_size : sizeGroup recordSet .once (turnGroup keyWShape3 (tailFor 0) (tailFor 0))
    ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = groupOfM (turnGroup keyWShape3
    (tailFor 0) (tailFor 0)) 420 :=
  congrArg (groupOfM (turnGroup keyWShape3 (tailFor 0) (tailFor 0)))
    (trace420 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 0)
      (tailFor 0)) m) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩)
      keyW3_turn1_p3 keyW3_turn1_p4 keyW3_turn1_p8 keyW3_turn1_p16 keyW3_turn1_p32 keyW3_turn1_p64
      keyW3_turn1_p128 keyW3_turn1_p256 keyW3_turn1_p512 keyW3_turn1_p384 keyW3_turn1_p448
      keyW3_turn1_p416 keyW3_turn1_p432 keyW3_turn1_p424 keyW3_turn1_p420 keyW3_turn1_p422
      keyW3_turn1_p421)

theorem keyW3_turn1_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyWShape3 (tailFor 0) (tailFor 0)) 420)).mainAt.agree (margin recordSet) = 49 := by
  decide +kernel

/-- Turn 1 of stage 3, from 0 positions. -/
theorem keyW3_turn1 : turn recordSet .once
    ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ keyWShape3
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨15, 2048, 0, true⟩, ⟨14, 64, 0, true⟩, 3, 3, 1, .johnson, 420⟩ 49 :=
  turn_more_of (by decide +kernel) keyW3_turn1_size keyW3_turn1_p420 keyW3_turn1_pos (by decide)

theorem keyW3_turn2_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 49)
    (tailFor 49)) 3) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW3_turn2_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 49)
    (tailFor 49)) 4) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW3_turn2_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 49)
    (tailFor 49)) 8) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW3_turn2_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 49)
    (tailFor 49)) 16) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW3_turn2_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 49)
    (tailFor 49)) 32) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW3_turn2_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 49)
    (tailFor 49)) 64) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW3_turn2_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 49)
    (tailFor 49)) 128) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW3_turn2_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 49)
    (tailFor 49)) 256) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW3_turn2_p512 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 49)
    (tailFor 49)) 512) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW3_turn2_p384 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 49)
    (tailFor 49)) 384) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW3_turn2_p448 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 49)
    (tailFor 49)) 448) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW3_turn2_p416 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 49)
    (tailFor 49)) 416) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW3_turn2_p432 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 49)
    (tailFor 49)) 432) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW3_turn2_p424 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 49)
    (tailFor 49)) 424) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW3_turn2_p420 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 49)
    (tailFor 49)) 420) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW3_turn2_p422 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 49)
    (tailFor 49)) 422) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW3_turn2_p423 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 49)
    (tailFor 49)) 423) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW3_turn2_size : sizeGroup recordSet .once (turnGroup keyWShape3 (tailFor 49) (tailFor
    49)) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ = groupOfM (turnGroup
    keyWShape3 (tailFor 49) (tailFor 49)) 423 :=
  congrArg (groupOfM (turnGroup keyWShape3 (tailFor 49) (tailFor 49)))
    (trace423 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyWShape3 (tailFor 49)
      (tailFor 49)) m) ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩)
      keyW3_turn2_p3 keyW3_turn2_p4 keyW3_turn2_p8 keyW3_turn2_p16 keyW3_turn2_p32 keyW3_turn2_p64
      keyW3_turn2_p128 keyW3_turn2_p256 keyW3_turn2_p512 keyW3_turn2_p384 keyW3_turn2_p448
      keyW3_turn2_p416 keyW3_turn2_p432 keyW3_turn2_p424 keyW3_turn2_p420 keyW3_turn2_p422
      keyW3_turn2_p423)

theorem keyW3_turn2_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyWShape3 (tailFor 49) (tailFor 49)) 423)).mainAt.agree (margin recordSet) = 49 := by
  decide +kernel

/-- Turn 2 of stage 3, from 49 positions. -/
theorem keyW3_turn2 : turn recordSet .once
    ⟨stageCubeBits keyWShape3, 1, 4 + 3 * max keyW2.main.r 1024⟩ keyWShape3
    (tailFor 49) (tailFor 49) 49 =
      .settled keyW3 49 :=
  turn_settled_of (by decide +kernel) keyW3_turn2_size keyW3_turn2_p423 keyW3_turn2_pos (by decide)

end OnBytes.Params

#print axioms OnBytes.Params.keyW3_turn1
#print axioms OnBytes.Params.keyW3_turn2
