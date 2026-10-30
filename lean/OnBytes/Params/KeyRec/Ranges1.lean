-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/Ranges1.lean: the turns of the iteration that solves stage 1 of the ranges'
test of a key of full size, each from its parts.

One kernel evaluation a trial of the search for m (OnBytes/Params/Fit/TurnForward.lean says why): a
module's own memory stays far below what one evaluation of a whole turn takes. The theorems are
checked one behind the other (Elab.async false), so that their memory does not add up.

Main names.
  keyR1_turn1 and so on: what each turn returns.
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

theorem keyR1_turn1_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id 0))
    (tailFor 0)) 3) ⟨23, 1, 981⟩ = true := by
  decide +kernel

theorem keyR1_turn1_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id 0))
    (tailFor 0)) 4) ⟨23, 1, 981⟩ = true := by
  decide +kernel

theorem keyR1_turn1_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id 0))
    (tailFor 0)) 8) ⟨23, 1, 981⟩ = true := by
  decide +kernel

theorem keyR1_turn1_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    0)) (tailFor 0)) 16) ⟨23, 1, 981⟩ = true := by
  decide +kernel

theorem keyR1_turn1_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    0)) (tailFor 0)) 32) ⟨23, 1, 981⟩ = true := by
  decide +kernel

theorem keyR1_turn1_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    0)) (tailFor 0)) 64) ⟨23, 1, 981⟩ = true := by
  decide +kernel

theorem keyR1_turn1_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    0)) (tailFor 0)) 128) ⟨23, 1, 981⟩ = true := by
  decide +kernel

theorem keyR1_turn1_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    0)) (tailFor 0)) 256) ⟨23, 1, 981⟩ = false := by
  decide +kernel

theorem keyR1_turn1_p192 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    0)) (tailFor 0)) 192) ⟨23, 1, 981⟩ = false := by
  decide +kernel

theorem keyR1_turn1_p160 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    0)) (tailFor 0)) 160) ⟨23, 1, 981⟩ = false := by
  decide +kernel

theorem keyR1_turn1_p144 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    0)) (tailFor 0)) 144) ⟨23, 1, 981⟩ = false := by
  decide +kernel

theorem keyR1_turn1_p136 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    0)) (tailFor 0)) 136) ⟨23, 1, 981⟩ = false := by
  decide +kernel

theorem keyR1_turn1_p132 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    0)) (tailFor 0)) 132) ⟨23, 1, 981⟩ = false := by
  decide +kernel

theorem keyR1_turn1_p130 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    0)) (tailFor 0)) 130) ⟨23, 1, 981⟩ = false := by
  decide +kernel

theorem keyR1_turn1_p129 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    0)) (tailFor 0)) 129) ⟨23, 1, 981⟩ = false := by
  decide +kernel

theorem keyR1_turn1_size : sizeGroup recordSet .once (turnGroup keyRShape1 (tailFor (id 0)) (tailFor
    0)) ⟨23, 1, 981⟩ = groupOfM (turnGroup keyRShape1 (tailFor (id 0)) (tailFor 0)) 128 :=
  congrArg (groupOfM (turnGroup keyRShape1 (tailFor (id 0)) (tailFor 0)))
    (trace128 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id 0))
      (tailFor 0)) m) ⟨23, 1, 981⟩)
      keyR1_turn1_p3 keyR1_turn1_p4 keyR1_turn1_p8 keyR1_turn1_p16 keyR1_turn1_p32 keyR1_turn1_p64
      keyR1_turn1_p128 keyR1_turn1_p256 keyR1_turn1_p192 keyR1_turn1_p160 keyR1_turn1_p144
      keyR1_turn1_p136 keyR1_turn1_p132 keyR1_turn1_p130 keyR1_turn1_p129)

theorem keyR1_turn1_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyRShape1 (tailFor (id 0)) (tailFor 0)) 128)).mainAt.agree (margin recordSet) = 49 := by
  decide +kernel

/-- Turn 1 of the first group, from 0 positions. -/
theorem keyR1_turn1 : turn recordSet .once ⟨23, 1, 981⟩ keyRShape1
    (tailFor (id 0)) (tailFor 0) 0 =
      .more ⟨⟨22, 262144, 0, false⟩, ⟨16, 4096, 0, true⟩, 4, 4, 1, .johnson, 128⟩ 49 :=
  turn_more_of (by decide +kernel) keyR1_turn1_size keyR1_turn1_p128 keyR1_turn1_pos (by decide)

theorem keyR1_turn2_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    49)) (tailFor 49)) 3) ⟨23, 1, 981⟩ = true := by
  decide +kernel

theorem keyR1_turn2_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    49)) (tailFor 49)) 4) ⟨23, 1, 981⟩ = true := by
  decide +kernel

theorem keyR1_turn2_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    49)) (tailFor 49)) 8) ⟨23, 1, 981⟩ = true := by
  decide +kernel

theorem keyR1_turn2_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    49)) (tailFor 49)) 16) ⟨23, 1, 981⟩ = true := by
  decide +kernel

theorem keyR1_turn2_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    49)) (tailFor 49)) 32) ⟨23, 1, 981⟩ = true := by
  decide +kernel

theorem keyR1_turn2_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    49)) (tailFor 49)) 64) ⟨23, 1, 981⟩ = true := by
  decide +kernel

theorem keyR1_turn2_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    49)) (tailFor 49)) 128) ⟨23, 1, 981⟩ = true := by
  decide +kernel

theorem keyR1_turn2_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    49)) (tailFor 49)) 256) ⟨23, 1, 981⟩ = false := by
  decide +kernel

theorem keyR1_turn2_p192 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    49)) (tailFor 49)) 192) ⟨23, 1, 981⟩ = false := by
  decide +kernel

theorem keyR1_turn2_p160 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    49)) (tailFor 49)) 160) ⟨23, 1, 981⟩ = false := by
  decide +kernel

theorem keyR1_turn2_p144 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    49)) (tailFor 49)) 144) ⟨23, 1, 981⟩ = false := by
  decide +kernel

theorem keyR1_turn2_p136 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    49)) (tailFor 49)) 136) ⟨23, 1, 981⟩ = true := by
  decide +kernel

theorem keyR1_turn2_p140 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    49)) (tailFor 49)) 140) ⟨23, 1, 981⟩ = false := by
  decide +kernel

theorem keyR1_turn2_p138 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    49)) (tailFor 49)) 138) ⟨23, 1, 981⟩ = true := by
  decide +kernel

theorem keyR1_turn2_p139 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id
    49)) (tailFor 49)) 139) ⟨23, 1, 981⟩ = false := by
  decide +kernel

theorem keyR1_turn2_size : sizeGroup recordSet .once (turnGroup keyRShape1 (tailFor (id 49))
    (tailFor 49)) ⟨23, 1, 981⟩ = groupOfM (turnGroup keyRShape1 (tailFor (id 49)) (tailFor 49)) 138
    :=
  congrArg (groupOfM (turnGroup keyRShape1 (tailFor (id 49)) (tailFor 49)))
    (trace138 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyRShape1 (tailFor (id 49))
      (tailFor 49)) m) ⟨23, 1, 981⟩)
      keyR1_turn2_p3 keyR1_turn2_p4 keyR1_turn2_p8 keyR1_turn2_p16 keyR1_turn2_p32 keyR1_turn2_p64
      keyR1_turn2_p128 keyR1_turn2_p256 keyR1_turn2_p192 keyR1_turn2_p160 keyR1_turn2_p144
      keyR1_turn2_p136 keyR1_turn2_p140 keyR1_turn2_p138 keyR1_turn2_p139)

theorem keyR1_turn2_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyRShape1 (tailFor (id 49)) (tailFor 49)) 138)).mainAt.agree (margin recordSet) = 49 := by
  decide +kernel

/-- Turn 2 of the first group, from 49 positions. -/
theorem keyR1_turn2 : turn recordSet .once ⟨23, 1, 981⟩ keyRShape1
    (tailFor (id 49)) (tailFor 49) 49 =
      .settled keyR1 49 :=
  turn_settled_of (by decide +kernel) keyR1_turn2_size keyR1_turn2_p138 keyR1_turn2_pos (by decide)

end OnBytes.Params

#print axioms OnBytes.Params.keyR1_turn1
#print axioms OnBytes.Params.keyR1_turn2
