-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/Folded3.lean: the turns of the iteration that solves stage 3 of the folded
row's test of a key of full size, each from its parts.

One kernel evaluation a trial of the search for m (OnBytes/Params/Fit/TurnForward.lean says why): a
module's own memory stays far below what one evaluation of a whole turn takes. The theorems are
checked one behind the other (Elab.async false), so that their memory does not add up.

Main names.
  keyU3_turn1 and so on: what each turn returns.
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

theorem keyU3_turn1_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 0)
    (tailFor 0)) 3) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn1_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 0)
    (tailFor 0)) 4) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn1_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 0)
    (tailFor 0)) 8) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn1_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 0)
    (tailFor 0)) 16) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn1_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 0)
    (tailFor 0)) 32) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn1_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 0)
    (tailFor 0)) 64) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn1_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 0)
    (tailFor 0)) 128) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn1_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 0)
    (tailFor 0)) 256) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn1_p512 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 0)
    (tailFor 0)) 512) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU3_turn1_p384 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 0)
    (tailFor 0)) 384) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU3_turn1_p320 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 0)
    (tailFor 0)) 320) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU3_turn1_p288 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 0)
    (tailFor 0)) 288) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn1_p304 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 0)
    (tailFor 0)) 304) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn1_p312 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 0)
    (tailFor 0)) 312) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU3_turn1_p308 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 0)
    (tailFor 0)) 308) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU3_turn1_p306 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 0)
    (tailFor 0)) 306) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn1_p307 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 0)
    (tailFor 0)) 307) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU3_turn1_size : sizeGroup recordSet .once (turnGroup keyUShape3 (tailFor 0) (tailFor 0))
    ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = groupOfM (turnGroup keyUShape3
    (tailFor 0) (tailFor 0)) 306 :=
  congrArg (groupOfM (turnGroup keyUShape3 (tailFor 0) (tailFor 0)))
    (trace306 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 0)
      (tailFor 0)) m) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩)
      keyU3_turn1_p3 keyU3_turn1_p4 keyU3_turn1_p8 keyU3_turn1_p16 keyU3_turn1_p32 keyU3_turn1_p64
      keyU3_turn1_p128 keyU3_turn1_p256 keyU3_turn1_p512 keyU3_turn1_p384 keyU3_turn1_p320
      keyU3_turn1_p288 keyU3_turn1_p304 keyU3_turn1_p312 keyU3_turn1_p308 keyU3_turn1_p306
      keyU3_turn1_p307)

theorem keyU3_turn1_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyUShape3 (tailFor 0) (tailFor 0)) 306)).mainAt.agree (margin recordSet) = 49 := by
  decide +kernel

/-- Turn 1 of stage 3, from 0 positions. -/
theorem keyU3_turn1 : turn recordSet .once
    ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ keyUShape3
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨17, 8192, 0, true⟩, ⟨12, 256, 0, true⟩, 4, 2, 1, .johnson, 306⟩ 49 :=
  turn_more_of (by decide +kernel) keyU3_turn1_size keyU3_turn1_p306 keyU3_turn1_pos (by decide)

theorem keyU3_turn2_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 49)
    (tailFor 49)) 3) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn2_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 49)
    (tailFor 49)) 4) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn2_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 49)
    (tailFor 49)) 8) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn2_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 49)
    (tailFor 49)) 16) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn2_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 49)
    (tailFor 49)) 32) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn2_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 49)
    (tailFor 49)) 64) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn2_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 49)
    (tailFor 49)) 128) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn2_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 49)
    (tailFor 49)) 256) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn2_p512 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 49)
    (tailFor 49)) 512) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU3_turn2_p384 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 49)
    (tailFor 49)) 384) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU3_turn2_p320 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 49)
    (tailFor 49)) 320) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU3_turn2_p288 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 49)
    (tailFor 49)) 288) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn2_p304 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 49)
    (tailFor 49)) 304) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU3_turn2_p296 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 49)
    (tailFor 49)) 296) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU3_turn2_p292 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 49)
    (tailFor 49)) 292) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU3_turn2_p290 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 49)
    (tailFor 49)) 290) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn2_p291 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 49)
    (tailFor 49)) 291) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn2_size : sizeGroup recordSet .once (turnGroup keyUShape3 (tailFor 49) (tailFor
    49)) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = groupOfM (turnGroup
    keyUShape3 (tailFor 49) (tailFor 49)) 291 :=
  congrArg (groupOfM (turnGroup keyUShape3 (tailFor 49) (tailFor 49)))
    (trace291 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 49)
      (tailFor 49)) m) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩)
      keyU3_turn2_p3 keyU3_turn2_p4 keyU3_turn2_p8 keyU3_turn2_p16 keyU3_turn2_p32 keyU3_turn2_p64
      keyU3_turn2_p128 keyU3_turn2_p256 keyU3_turn2_p512 keyU3_turn2_p384 keyU3_turn2_p320
      keyU3_turn2_p288 keyU3_turn2_p304 keyU3_turn2_p296 keyU3_turn2_p292 keyU3_turn2_p290
      keyU3_turn2_p291)

theorem keyU3_turn2_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyUShape3 (tailFor 49) (tailFor 49)) 291)).mainAt.agree (margin recordSet) = 52 := by
  decide +kernel

/-- Turn 2 of stage 3, from 49 positions. -/
theorem keyU3_turn2 : turn recordSet .once
    ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ keyUShape3
    (tailFor 49) (tailFor 49) 49 =
      .more ⟨⟨17, 8192, 49, true⟩, ⟨12, 256, 49, true⟩, 4, 2, 1, .johnson, 291⟩ 52 :=
  turn_more_of (by decide +kernel) keyU3_turn2_size keyU3_turn2_p291 keyU3_turn2_pos (by decide)

theorem keyU3_turn3_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 52)
    (tailFor 52)) 3) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn3_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 52)
    (tailFor 52)) 4) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn3_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 52)
    (tailFor 52)) 8) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn3_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 52)
    (tailFor 52)) 16) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn3_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 52)
    (tailFor 52)) 32) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn3_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 52)
    (tailFor 52)) 64) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn3_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 52)
    (tailFor 52)) 128) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn3_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 52)
    (tailFor 52)) 256) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn3_p512 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 52)
    (tailFor 52)) 512) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU3_turn3_p384 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 52)
    (tailFor 52)) 384) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU3_turn3_p320 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 52)
    (tailFor 52)) 320) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU3_turn3_p288 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 52)
    (tailFor 52)) 288) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn3_p304 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 52)
    (tailFor 52)) 304) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU3_turn3_p296 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 52)
    (tailFor 52)) 296) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU3_turn3_p292 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 52)
    (tailFor 52)) 292) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU3_turn3_p294 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 52)
    (tailFor 52)) 294) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU3_turn3_p293 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 52)
    (tailFor 52)) 293) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU3_turn3_size : sizeGroup recordSet .once (turnGroup keyUShape3 (tailFor 52) (tailFor
    52)) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ = groupOfM (turnGroup
    keyUShape3 (tailFor 52) (tailFor 52)) 292 :=
  congrArg (groupOfM (turnGroup keyUShape3 (tailFor 52) (tailFor 52)))
    (trace292 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyUShape3 (tailFor 52)
      (tailFor 52)) m) ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩)
      keyU3_turn3_p3 keyU3_turn3_p4 keyU3_turn3_p8 keyU3_turn3_p16 keyU3_turn3_p32 keyU3_turn3_p64
      keyU3_turn3_p128 keyU3_turn3_p256 keyU3_turn3_p512 keyU3_turn3_p384 keyU3_turn3_p320
      keyU3_turn3_p288 keyU3_turn3_p304 keyU3_turn3_p296 keyU3_turn3_p292 keyU3_turn3_p294
      keyU3_turn3_p293)

theorem keyU3_turn3_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyUShape3 (tailFor 52) (tailFor 52)) 292)).mainAt.agree (margin recordSet) = 52 := by
  decide +kernel

/-- Turn 3 of stage 3, from 52 positions. -/
theorem keyU3_turn3 : turn recordSet .once
    ⟨stageCubeBits keyUShape3, 1, 4 + 3 * max keyU2.main.r 1024⟩ keyUShape3
    (tailFor 52) (tailFor 52) 52 =
      .settled keyU3 52 :=
  turn_settled_of (by decide +kernel) keyU3_turn3_size keyU3_turn3_p292 keyU3_turn3_pos (by decide)

end OnBytes.Params

#print axioms OnBytes.Params.keyU3_turn1
#print axioms OnBytes.Params.keyU3_turn2
#print axioms OnBytes.Params.keyU3_turn3
