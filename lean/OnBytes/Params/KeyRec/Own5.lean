-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/Own5.lean: the turns of the iteration that solves stage 5 of the own test of a
key of full size, each from its parts.

One kernel evaluation a trial of the search for m (OnBytes/Params/Fit/TurnForward.lean says why): a
module's own memory stays far below what one evaluation of a whole turn takes. The theorems are
checked one behind the other (Elab.async false), so that their memory does not add up.

Main names.
  keyW5_turn1 and so on: what each turn returns.
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

theorem keyW5_turn1_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 0)
    (tailFor 0)) 3) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn1_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 0)
    (tailFor 0)) 4) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn1_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 0)
    (tailFor 0)) 8) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn1_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 0)
    (tailFor 0)) 16) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn1_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 0)
    (tailFor 0)) 32) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn1_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 0)
    (tailFor 0)) 64) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn1_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 0)
    (tailFor 0)) 128) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn1_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 0)
    (tailFor 0)) 256) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW5_turn1_p192 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 0)
    (tailFor 0)) 192) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn1_p224 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 0)
    (tailFor 0)) 224) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW5_turn1_p208 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 0)
    (tailFor 0)) 208) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW5_turn1_p200 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 0)
    (tailFor 0)) 200) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW5_turn1_p196 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 0)
    (tailFor 0)) 196) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW5_turn1_p194 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 0)
    (tailFor 0)) 194) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn1_p195 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 0)
    (tailFor 0)) 195) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn1_size : sizeGroup recordSet .once (turnGroup keyWShape5 (tailFor 0) (tailFor 0))
    ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = groupOfM (turnGroup keyWShape5
    (tailFor 0) (tailFor 0)) 195 :=
  congrArg (groupOfM (turnGroup keyWShape5 (tailFor 0) (tailFor 0)))
    (trace195 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 0)
      (tailFor 0)) m) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩)
      keyW5_turn1_p3 keyW5_turn1_p4 keyW5_turn1_p8 keyW5_turn1_p16 keyW5_turn1_p32 keyW5_turn1_p64
      keyW5_turn1_p128 keyW5_turn1_p256 keyW5_turn1_p192 keyW5_turn1_p224 keyW5_turn1_p208
      keyW5_turn1_p200 keyW5_turn1_p196 keyW5_turn1_p194 keyW5_turn1_p195)

theorem keyW5_turn1_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyWShape5 (tailFor 0) (tailFor 0)) 195)).mainAt.agree (margin recordSet) = 28 := by
  decide +kernel

/-- Turn 1 of stage 5, from 0 positions. -/
theorem keyW5_turn1 : turn recordSet .once
    ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ keyWShape5
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨15, 256, 0, true⟩, ⟨15, 256, 0, true⟩, 0, 0, 1, .johnson, 195⟩ 28 :=
  turn_more_of (by decide +kernel) keyW5_turn1_size keyW5_turn1_p195 keyW5_turn1_pos (by decide)

theorem keyW5_turn2_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 28)
    (tailFor 28)) 3) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn2_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 28)
    (tailFor 28)) 4) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn2_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 28)
    (tailFor 28)) 8) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn2_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 28)
    (tailFor 28)) 16) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn2_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 28)
    (tailFor 28)) 32) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn2_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 28)
    (tailFor 28)) 64) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn2_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 28)
    (tailFor 28)) 128) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn2_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 28)
    (tailFor 28)) 256) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW5_turn2_p192 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 28)
    (tailFor 28)) 192) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn2_p224 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 28)
    (tailFor 28)) 224) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW5_turn2_p208 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 28)
    (tailFor 28)) 208) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW5_turn2_p200 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 28)
    (tailFor 28)) 200) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn2_p204 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 28)
    (tailFor 28)) 204) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW5_turn2_p202 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 28)
    (tailFor 28)) 202) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW5_turn2_p201 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 28)
    (tailFor 28)) 201) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn2_size : sizeGroup recordSet .once (turnGroup keyWShape5 (tailFor 28) (tailFor
    28)) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = groupOfM (turnGroup
    keyWShape5 (tailFor 28) (tailFor 28)) 201 :=
  congrArg (groupOfM (turnGroup keyWShape5 (tailFor 28) (tailFor 28)))
    (trace201 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 28)
      (tailFor 28)) m) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩)
      keyW5_turn2_p3 keyW5_turn2_p4 keyW5_turn2_p8 keyW5_turn2_p16 keyW5_turn2_p32 keyW5_turn2_p64
      keyW5_turn2_p128 keyW5_turn2_p256 keyW5_turn2_p192 keyW5_turn2_p224 keyW5_turn2_p208
      keyW5_turn2_p200 keyW5_turn2_p204 keyW5_turn2_p202 keyW5_turn2_p201)

theorem keyW5_turn2_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyWShape5 (tailFor 28) (tailFor 28)) 201)).mainAt.agree (margin recordSet) = 29 := by
  decide +kernel

/-- Turn 2 of stage 5, from 28 positions. -/
theorem keyW5_turn2 : turn recordSet .once
    ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ keyWShape5
    (tailFor 28) (tailFor 28) 28 =
      .more ⟨⟨15, 256, 28, true⟩, ⟨15, 256, 28, true⟩, 0, 0, 1, .johnson, 201⟩ 29 :=
  turn_more_of (by decide +kernel) keyW5_turn2_size keyW5_turn2_p201 keyW5_turn2_pos (by decide)

theorem keyW5_turn3_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 29)
    (tailFor 29)) 3) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn3_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 29)
    (tailFor 29)) 4) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn3_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 29)
    (tailFor 29)) 8) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn3_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 29)
    (tailFor 29)) 16) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn3_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 29)
    (tailFor 29)) 32) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn3_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 29)
    (tailFor 29)) 64) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn3_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 29)
    (tailFor 29)) 128) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn3_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 29)
    (tailFor 29)) 256) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW5_turn3_p192 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 29)
    (tailFor 29)) 192) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn3_p224 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 29)
    (tailFor 29)) 224) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW5_turn3_p208 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 29)
    (tailFor 29)) 208) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW5_turn3_p200 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 29)
    (tailFor 29)) 200) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn3_p204 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 29)
    (tailFor 29)) 204) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW5_turn3_p202 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 29)
    (tailFor 29)) 202) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = false := by
  decide +kernel

theorem keyW5_turn3_p201 : groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 29)
    (tailFor 29)) 201) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = true := by
  decide +kernel

theorem keyW5_turn3_size : sizeGroup recordSet .once (turnGroup keyWShape5 (tailFor 29) (tailFor
    29)) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ = groupOfM (turnGroup
    keyWShape5 (tailFor 29) (tailFor 29)) 201 :=
  congrArg (groupOfM (turnGroup keyWShape5 (tailFor 29) (tailFor 29)))
    (trace201 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyWShape5 (tailFor 29)
      (tailFor 29)) m) ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩)
      keyW5_turn3_p3 keyW5_turn3_p4 keyW5_turn3_p8 keyW5_turn3_p16 keyW5_turn3_p32 keyW5_turn3_p64
      keyW5_turn3_p128 keyW5_turn3_p256 keyW5_turn3_p192 keyW5_turn3_p224 keyW5_turn3_p208
      keyW5_turn3_p200 keyW5_turn3_p204 keyW5_turn3_p202 keyW5_turn3_p201)

theorem keyW5_turn3_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyWShape5 (tailFor 29) (tailFor 29)) 201)).mainAt.agree (margin recordSet) = 29 := by
  decide +kernel

/-- Turn 3 of stage 5, from 29 positions. -/
theorem keyW5_turn3 : turn recordSet .once
    ⟨stageCubeBits keyWShape5, 1, 4 + 3 * max keyW4.main.r 1024⟩ keyWShape5
    (tailFor 29) (tailFor 29) 29 =
      .settled keyW5 29 :=
  turn_settled_of (by decide +kernel) keyW5_turn3_size keyW5_turn3_p201 keyW5_turn3_pos (by decide)

end OnBytes.Params

#print axioms OnBytes.Params.keyW5_turn1
#print axioms OnBytes.Params.keyW5_turn2
#print axioms OnBytes.Params.keyW5_turn3
