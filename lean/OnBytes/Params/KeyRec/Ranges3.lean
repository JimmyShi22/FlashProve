-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/Ranges3.lean: the turns of the iteration that solves stage 3 of the ranges'
test of a key of full size, each from its parts.

One kernel evaluation a trial of the search for m (OnBytes/Params/Fit/TurnForward.lean says why): a
module's own memory stays far below what one evaluation of a whole turn takes. The theorems are
checked one behind the other (Elab.async false), so that their memory does not add up.

Main names.
  keyR3_turn1 and so on: what each turn returns.
  ‹turn›_p‹m›: the trial of the search at m. ‹turn›_size: the group that the search sizes.
  ‹turn›_pos: the positions that follow.

Limits. Closed statements at the typed values alone. Nothing on soundness. What the whole leaves
unsaid stands in the head of OnBytes/Params/KeyRec/Ranges.lean.

-/
import OnBytes.Params.KeyRec.RangesDefs
import OnBytes.Params.KeyRec.Traces

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace OnBytes.Params

theorem keyR3_turn1_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 0)
    (tailFor 0)) 3) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR3_turn1_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 0)
    (tailFor 0)) 4) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR3_turn1_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 0)
    (tailFor 0)) 8) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR3_turn1_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 0)
    (tailFor 0)) 16) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR3_turn1_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 0)
    (tailFor 0)) 32) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR3_turn1_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 0)
    (tailFor 0)) 64) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR3_turn1_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 0)
    (tailFor 0)) 128) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR3_turn1_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 0)
    (tailFor 0)) 256) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyR3_turn1_p192 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 0)
    (tailFor 0)) 192) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR3_turn1_p224 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 0)
    (tailFor 0)) 224) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyR3_turn1_p208 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 0)
    (tailFor 0)) 208) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR3_turn1_p216 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 0)
    (tailFor 0)) 216) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyR3_turn1_p212 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 0)
    (tailFor 0)) 212) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyR3_turn1_p210 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 0)
    (tailFor 0)) 210) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyR3_turn1_p209 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 0)
    (tailFor 0)) 209) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR3_turn1_size : sizeGroup recordSet .once (turnGroup keyRShape3 (tailFor 0) (tailFor 0))
    ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = groupOfM (turnGroup keyRShape3
    (tailFor 0) (tailFor 0)) 209 :=
  congrArg (groupOfM (turnGroup keyRShape3 (tailFor 0) (tailFor 0)))
    (trace209 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 0)
      (tailFor 0)) m) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩)
      keyR3_turn1_p3 keyR3_turn1_p4 keyR3_turn1_p8 keyR3_turn1_p16 keyR3_turn1_p32 keyR3_turn1_p64
      keyR3_turn1_p128 keyR3_turn1_p256 keyR3_turn1_p192 keyR3_turn1_p224 keyR3_turn1_p208
      keyR3_turn1_p216 keyR3_turn1_p212 keyR3_turn1_p210 keyR3_turn1_p209)

theorem keyR3_turn1_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyRShape3 (tailFor 0) (tailFor 0)) 209)).mainAt.agree (margin recordSet) = 33 := by
  decide +kernel

/-- Turn 1 of stage 3, from 0 positions. -/
theorem keyR3_turn1 : turn recordSet .once
    ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ keyRShape3
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨17, 2048, 0, true⟩, ⟨17, 1024, 0, true⟩, 3, 3, 1, .johnson, 209⟩ 33 :=
  turn_more_of (by decide +kernel) keyR3_turn1_size keyR3_turn1_p209 keyR3_turn1_pos (by decide)

theorem keyR3_turn2_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 33)
    (tailFor 33)) 3) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR3_turn2_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 33)
    (tailFor 33)) 4) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR3_turn2_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 33)
    (tailFor 33)) 8) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR3_turn2_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 33)
    (tailFor 33)) 16) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR3_turn2_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 33)
    (tailFor 33)) 32) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR3_turn2_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 33)
    (tailFor 33)) 64) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR3_turn2_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 33)
    (tailFor 33)) 128) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR3_turn2_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 33)
    (tailFor 33)) 256) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyR3_turn2_p192 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 33)
    (tailFor 33)) 192) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR3_turn2_p224 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 33)
    (tailFor 33)) 224) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyR3_turn2_p208 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 33)
    (tailFor 33)) 208) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR3_turn2_p216 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 33)
    (tailFor 33)) 216) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyR3_turn2_p212 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 33)
    (tailFor 33)) 212) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyR3_turn2_p210 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 33)
    (tailFor 33)) 210) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR3_turn2_p211 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 33)
    (tailFor 33)) 211) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = false := by
  decide +kernel

theorem keyR3_turn2_size : sizeGroup recordSet .once (turnGroup keyRShape3 (tailFor 33) (tailFor
    33)) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ = groupOfM (turnGroup
    keyRShape3 (tailFor 33) (tailFor 33)) 210 :=
  congrArg (groupOfM (turnGroup keyRShape3 (tailFor 33) (tailFor 33)))
    (trace210 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyRShape3 (tailFor 33)
      (tailFor 33)) m) ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩)
      keyR3_turn2_p3 keyR3_turn2_p4 keyR3_turn2_p8 keyR3_turn2_p16 keyR3_turn2_p32 keyR3_turn2_p64
      keyR3_turn2_p128 keyR3_turn2_p256 keyR3_turn2_p192 keyR3_turn2_p224 keyR3_turn2_p208
      keyR3_turn2_p216 keyR3_turn2_p212 keyR3_turn2_p210 keyR3_turn2_p211)

theorem keyR3_turn2_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyRShape3 (tailFor 33) (tailFor 33)) 210)).mainAt.agree (margin recordSet) = 33 := by
  decide +kernel

/-- Turn 2 of stage 3, from 33 positions. -/
theorem keyR3_turn2 : turn recordSet .once
    ⟨stageCubeBits keyRShape3, 1, 4 + 3 * max keyR2.main.r 1024⟩ keyRShape3
    (tailFor 33) (tailFor 33) 33 =
      .settled keyR3 33 :=
  turn_settled_of (by decide +kernel) keyR3_turn2_size keyR3_turn2_p210 keyR3_turn2_pos (by decide)

end OnBytes.Params

#print axioms OnBytes.Params.keyR3_turn1
#print axioms OnBytes.Params.keyR3_turn2
