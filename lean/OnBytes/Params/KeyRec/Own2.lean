-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/Own2.lean: the turns of the iteration that solves stage 2 of the own test of a
key of full size, each from its parts.

One kernel evaluation a trial of the search for m (OnBytes/Params/Fit/TurnForward.lean says why): a
module's own memory stays far below what one evaluation of a whole turn takes. The theorems are
checked one behind the other (Elab.async false), so that their memory does not add up.

Main names.
  keyW2_turn1 and so on: what each turn returns.
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

theorem keyW2_turn1_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 0)
    (tailFor 0)) 3) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW2_turn1_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 0)
    (tailFor 0)) 4) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW2_turn1_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 0)
    (tailFor 0)) 8) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW2_turn1_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 0)
    (tailFor 0)) 16) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW2_turn1_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 0)
    (tailFor 0)) 32) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW2_turn1_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 0)
    (tailFor 0)) 64) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW2_turn1_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 0)
    (tailFor 0)) 128) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW2_turn1_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 0)
    (tailFor 0)) 256) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW2_turn1_p512 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 0)
    (tailFor 0)) 512) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW2_turn1_p384 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 0)
    (tailFor 0)) 384) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW2_turn1_p320 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 0)
    (tailFor 0)) 320) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW2_turn1_p288 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 0)
    (tailFor 0)) 288) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW2_turn1_p272 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 0)
    (tailFor 0)) 272) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW2_turn1_p280 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 0)
    (tailFor 0)) 280) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW2_turn1_p276 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 0)
    (tailFor 0)) 276) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW2_turn1_p278 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 0)
    (tailFor 0)) 278) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW2_turn1_p277 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 0)
    (tailFor 0)) 277) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW2_turn1_size : sizeGroup recordSet .once (turnGroup keyWShape2 (tailFor 0) (tailFor 0))
    ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = groupOfM (turnGroup keyWShape2
    (tailFor 0) (tailFor 0)) 277 :=
  congrArg (groupOfM (turnGroup keyWShape2 (tailFor 0) (tailFor 0)))
    (trace277 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 0)
      (tailFor 0)) m) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩)
      keyW2_turn1_p3 keyW2_turn1_p4 keyW2_turn1_p8 keyW2_turn1_p16 keyW2_turn1_p32 keyW2_turn1_p64
      keyW2_turn1_p128 keyW2_turn1_p256 keyW2_turn1_p512 keyW2_turn1_p384 keyW2_turn1_p320
      keyW2_turn1_p288 keyW2_turn1_p272 keyW2_turn1_p280 keyW2_turn1_p276 keyW2_turn1_p278
      keyW2_turn1_p277)

theorem keyW2_turn1_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyWShape2 (tailFor 0) (tailFor 0)) 277)).mainAt.agree (margin recordSet) = 49 := by
  decide +kernel

/-- Turn 1 of stage 2, from 0 positions. -/
theorem keyW2_turn1 : turn recordSet .once
    ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ keyWShape2
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨18, 16384, 0, true⟩, ⟨15, 128, 0, true⟩, 4, 3, 1, .johnson, 277⟩ 49 :=
  turn_more_of (by decide +kernel) keyW2_turn1_size keyW2_turn1_p277 keyW2_turn1_pos (by decide)

theorem keyW2_turn2_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 49)
    (tailFor 49)) 3) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW2_turn2_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 49)
    (tailFor 49)) 4) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW2_turn2_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 49)
    (tailFor 49)) 8) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW2_turn2_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 49)
    (tailFor 49)) 16) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW2_turn2_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 49)
    (tailFor 49)) 32) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW2_turn2_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 49)
    (tailFor 49)) 64) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW2_turn2_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 49)
    (tailFor 49)) 128) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW2_turn2_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 49)
    (tailFor 49)) 256) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW2_turn2_p512 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 49)
    (tailFor 49)) 512) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW2_turn2_p384 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 49)
    (tailFor 49)) 384) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW2_turn2_p320 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 49)
    (tailFor 49)) 320) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW2_turn2_p288 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 49)
    (tailFor 49)) 288) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW2_turn2_p272 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 49)
    (tailFor 49)) 272) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW2_turn2_p280 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 49)
    (tailFor 49)) 280) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW2_turn2_p276 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 49)
    (tailFor 49)) 276) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW2_turn2_p278 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 49)
    (tailFor 49)) 278) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW2_turn2_p277 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 49)
    (tailFor 49)) 277) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW2_turn2_size : sizeGroup recordSet .once (turnGroup keyWShape2 (tailFor 49) (tailFor
    49)) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ = groupOfM (turnGroup
    keyWShape2 (tailFor 49) (tailFor 49)) 277 :=
  congrArg (groupOfM (turnGroup keyWShape2 (tailFor 49) (tailFor 49)))
    (trace277 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyWShape2 (tailFor 49)
      (tailFor 49)) m) ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩)
      keyW2_turn2_p3 keyW2_turn2_p4 keyW2_turn2_p8 keyW2_turn2_p16 keyW2_turn2_p32 keyW2_turn2_p64
      keyW2_turn2_p128 keyW2_turn2_p256 keyW2_turn2_p512 keyW2_turn2_p384 keyW2_turn2_p320
      keyW2_turn2_p288 keyW2_turn2_p272 keyW2_turn2_p280 keyW2_turn2_p276 keyW2_turn2_p278
      keyW2_turn2_p277)

theorem keyW2_turn2_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyWShape2 (tailFor 49) (tailFor 49)) 277)).mainAt.agree (margin recordSet) = 49 := by
  decide +kernel

/-- Turn 2 of stage 2, from 49 positions. -/
theorem keyW2_turn2 : turn recordSet .once
    ⟨stageCubeBits keyWShape2, 1, 4 + 3 * max keyW1.main.r 1024⟩ keyWShape2
    (tailFor 49) (tailFor 49) 49 =
      .settled keyW2 49 :=
  turn_settled_of (by decide +kernel) keyW2_turn2_size keyW2_turn2_p277 keyW2_turn2_pos (by decide)

end OnBytes.Params

#print axioms OnBytes.Params.keyW2_turn1
#print axioms OnBytes.Params.keyW2_turn2
