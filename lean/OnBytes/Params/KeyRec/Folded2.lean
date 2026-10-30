-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/Folded2.lean: the turns of the iteration that solves stage 2 of the folded
row's test of a key of full size, each from its parts.

One kernel evaluation a trial of the search for m (OnBytes/Params/Fit/TurnForward.lean says why): a
module's own memory stays far below what one evaluation of a whole turn takes. The theorems are
checked one behind the other (Elab.async false), so that their memory does not add up.

Main names.
  keyU2_turn1 and so on: what each turn returns.
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

theorem keyU2_turn1_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 0)
    (tailFor 0)) 3) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn1_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 0)
    (tailFor 0)) 4) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn1_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 0)
    (tailFor 0)) 8) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn1_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 0)
    (tailFor 0)) 16) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn1_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 0)
    (tailFor 0)) 32) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn1_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 0)
    (tailFor 0)) 64) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn1_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 0)
    (tailFor 0)) 128) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn1_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 0)
    (tailFor 0)) 256) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU2_turn1_p192 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 0)
    (tailFor 0)) 192) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU2_turn1_p160 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 0)
    (tailFor 0)) 160) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn1_p176 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 0)
    (tailFor 0)) 176) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU2_turn1_p168 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 0)
    (tailFor 0)) 168) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn1_p172 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 0)
    (tailFor 0)) 172) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU2_turn1_p170 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 0)
    (tailFor 0)) 170) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU2_turn1_p169 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 0)
    (tailFor 0)) 169) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU2_turn1_size : sizeGroup recordSet .once (turnGroup keyUShape2 (tailFor 0) (tailFor 0))
    ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = groupOfM (turnGroup keyUShape2
    (tailFor 0) (tailFor 0)) 168 :=
  congrArg (groupOfM (turnGroup keyUShape2 (tailFor 0) (tailFor 0)))
    (trace168 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 0)
      (tailFor 0)) m) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩)
      keyU2_turn1_p3 keyU2_turn1_p4 keyU2_turn1_p8 keyU2_turn1_p16 keyU2_turn1_p32 keyU2_turn1_p64
      keyU2_turn1_p128 keyU2_turn1_p256 keyU2_turn1_p192 keyU2_turn1_p160 keyU2_turn1_p176
      keyU2_turn1_p168 keyU2_turn1_p172 keyU2_turn1_p170 keyU2_turn1_p169)

theorem keyU2_turn1_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyUShape2 (tailFor 0) (tailFor 0)) 168)).mainAt.agree (margin recordSet) = 49 := by
  decide +kernel

/-- Turn 1 of stage 2, from 0 positions. -/
theorem keyU2_turn1 : turn recordSet .once
    ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ keyUShape2
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨21, 131072, 0, true⟩, ⟨12, 256, 0, true⟩, 5, 2, 1, .johnson, 168⟩ 49 :=
  turn_more_of (by decide +kernel) keyU2_turn1_size keyU2_turn1_p168 keyU2_turn1_pos (by decide)

theorem keyU2_turn2_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 49)
    (tailFor 49)) 3) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn2_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 49)
    (tailFor 49)) 4) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn2_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 49)
    (tailFor 49)) 8) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn2_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 49)
    (tailFor 49)) 16) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn2_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 49)
    (tailFor 49)) 32) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn2_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 49)
    (tailFor 49)) 64) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn2_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 49)
    (tailFor 49)) 128) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn2_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 49)
    (tailFor 49)) 256) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU2_turn2_p192 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 49)
    (tailFor 49)) 192) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU2_turn2_p160 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 49)
    (tailFor 49)) 160) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn2_p176 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 49)
    (tailFor 49)) 176) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU2_turn2_p168 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 49)
    (tailFor 49)) 168) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU2_turn2_p164 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 49)
    (tailFor 49)) 164) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn2_p166 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 49)
    (tailFor 49)) 166) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn2_p167 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 49)
    (tailFor 49)) 167) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn2_size : sizeGroup recordSet .once (turnGroup keyUShape2 (tailFor 49) (tailFor
    49)) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = groupOfM (turnGroup
    keyUShape2 (tailFor 49) (tailFor 49)) 167 :=
  congrArg (groupOfM (turnGroup keyUShape2 (tailFor 49) (tailFor 49)))
    (trace167 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 49)
      (tailFor 49)) m) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩)
      keyU2_turn2_p3 keyU2_turn2_p4 keyU2_turn2_p8 keyU2_turn2_p16 keyU2_turn2_p32 keyU2_turn2_p64
      keyU2_turn2_p128 keyU2_turn2_p256 keyU2_turn2_p192 keyU2_turn2_p160 keyU2_turn2_p176
      keyU2_turn2_p168 keyU2_turn2_p164 keyU2_turn2_p166 keyU2_turn2_p167)

theorem keyU2_turn2_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyUShape2 (tailFor 49) (tailFor 49)) 167)).mainAt.agree (margin recordSet) = 52 := by
  decide +kernel

/-- Turn 2 of stage 2, from 49 positions. -/
theorem keyU2_turn2 : turn recordSet .once
    ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ keyUShape2
    (tailFor 49) (tailFor 49) 49 =
      .more ⟨⟨21, 131072, 49, true⟩, ⟨12, 256, 49, true⟩, 5, 2, 1, .johnson, 167⟩ 52 :=
  turn_more_of (by decide +kernel) keyU2_turn2_size keyU2_turn2_p167 keyU2_turn2_pos (by decide)

theorem keyU2_turn3_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 52)
    (tailFor 52)) 3) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn3_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 52)
    (tailFor 52)) 4) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn3_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 52)
    (tailFor 52)) 8) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn3_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 52)
    (tailFor 52)) 16) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn3_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 52)
    (tailFor 52)) 32) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn3_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 52)
    (tailFor 52)) 64) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn3_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 52)
    (tailFor 52)) 128) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn3_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 52)
    (tailFor 52)) 256) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU2_turn3_p192 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 52)
    (tailFor 52)) 192) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU2_turn3_p160 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 52)
    (tailFor 52)) 160) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn3_p176 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 52)
    (tailFor 52)) 176) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU2_turn3_p168 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 52)
    (tailFor 52)) 168) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = false := by
  decide +kernel

theorem keyU2_turn3_p164 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 52)
    (tailFor 52)) 164) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn3_p166 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 52)
    (tailFor 52)) 166) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn3_p167 : groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 52)
    (tailFor 52)) 167) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = true := by
  decide +kernel

theorem keyU2_turn3_size : sizeGroup recordSet .once (turnGroup keyUShape2 (tailFor 52) (tailFor
    52)) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ = groupOfM (turnGroup
    keyUShape2 (tailFor 52) (tailFor 52)) 167 :=
  congrArg (groupOfM (turnGroup keyUShape2 (tailFor 52) (tailFor 52)))
    (trace167 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyUShape2 (tailFor 52)
      (tailFor 52)) m) ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩)
      keyU2_turn3_p3 keyU2_turn3_p4 keyU2_turn3_p8 keyU2_turn3_p16 keyU2_turn3_p32 keyU2_turn3_p64
      keyU2_turn3_p128 keyU2_turn3_p256 keyU2_turn3_p192 keyU2_turn3_p160 keyU2_turn3_p176
      keyU2_turn3_p168 keyU2_turn3_p164 keyU2_turn3_p166 keyU2_turn3_p167)

theorem keyU2_turn3_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyUShape2 (tailFor 52) (tailFor 52)) 167)).mainAt.agree (margin recordSet) = 52 := by
  decide +kernel

/-- Turn 3 of stage 2, from 52 positions. -/
theorem keyU2_turn3 : turn recordSet .once
    ⟨stageCubeBits keyUShape2, 1, 4 + 3 * max keyU1.main.r 1024⟩ keyUShape2
    (tailFor 52) (tailFor 52) 52 =
      .settled keyU2 52 :=
  turn_settled_of (by decide +kernel) keyU2_turn3_size keyU2_turn3_p167 keyU2_turn3_pos (by decide)

end OnBytes.Params

#print axioms OnBytes.Params.keyU2_turn1
#print axioms OnBytes.Params.keyU2_turn2
#print axioms OnBytes.Params.keyU2_turn3
