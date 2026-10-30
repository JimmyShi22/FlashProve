-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/Ranges4.lean: the turns of the iteration that solves stage 4 of the ranges'
test of a key of full size, each from its parts.

One kernel evaluation a trial of the search for m (OnBytes/Params/Fit/TurnForward.lean says why): a
module's own memory stays far below what one evaluation of a whole turn takes. The theorems are
checked one behind the other (Elab.async false), so that their memory does not add up.

Main names.
  keyR4_turn1 and so on: what each turn returns.
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

theorem keyR4_turn1_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 0)
    (tailFor 0)) 3) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR4_turn1_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 0)
    (tailFor 0)) 4) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR4_turn1_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 0)
    (tailFor 0)) 8) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR4_turn1_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 0)
    (tailFor 0)) 16) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR4_turn1_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 0)
    (tailFor 0)) 32) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR4_turn1_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 0)
    (tailFor 0)) 64) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR4_turn1_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 0)
    (tailFor 0)) 128) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyR4_turn1_p96 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 0)
    (tailFor 0)) 96) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyR4_turn1_p80 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 0)
    (tailFor 0)) 80) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR4_turn1_p88 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 0)
    (tailFor 0)) 88) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR4_turn1_p92 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 0)
    (tailFor 0)) 92) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyR4_turn1_p90 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 0)
    (tailFor 0)) 90) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR4_turn1_p91 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 0)
    (tailFor 0)) 91) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR4_turn1_size : sizeGroup recordSet .once (turnGroup keyRShape4 (tailFor 0) (tailFor 0))
    ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = groupOfM (turnGroup keyRShape4
    (tailFor 0) (tailFor 0)) 91 :=
  congrArg (groupOfM (turnGroup keyRShape4 (tailFor 0) (tailFor 0)))
    (trace91 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 0)
      (tailFor 0)) m) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩)
      keyR4_turn1_p3 keyR4_turn1_p4 keyR4_turn1_p8 keyR4_turn1_p16 keyR4_turn1_p32 keyR4_turn1_p64
      keyR4_turn1_p128 keyR4_turn1_p96 keyR4_turn1_p80 keyR4_turn1_p88 keyR4_turn1_p92
      keyR4_turn1_p90 keyR4_turn1_p91)

theorem keyR4_turn1_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyRShape4 (tailFor 0) (tailFor 0)) 91)).mainAt.agree (margin recordSet) = 25 := by
  decide +kernel

/-- Turn 1 of stage 4, from 0 positions. -/
theorem keyR4_turn1 : turn recordSet .once
    ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ keyRShape4
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨20, 2048, 0, true⟩, ⟨20, 4096, 0, true⟩, 0, 0, 1, .johnson, 91⟩ 25 :=
  turn_more_of (by decide +kernel) keyR4_turn1_size keyR4_turn1_p91 keyR4_turn1_pos (by decide)

theorem keyR4_turn2_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 25)
    (tailFor 25)) 3) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR4_turn2_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 25)
    (tailFor 25)) 4) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR4_turn2_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 25)
    (tailFor 25)) 8) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR4_turn2_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 25)
    (tailFor 25)) 16) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR4_turn2_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 25)
    (tailFor 25)) 32) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR4_turn2_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 25)
    (tailFor 25)) 64) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR4_turn2_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 25)
    (tailFor 25)) 128) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyR4_turn2_p96 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 25)
    (tailFor 25)) 96) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyR4_turn2_p80 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 25)
    (tailFor 25)) 80) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR4_turn2_p88 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 25)
    (tailFor 25)) 88) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR4_turn2_p92 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 25)
    (tailFor 25)) 92) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyR4_turn2_p90 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 25)
    (tailFor 25)) 90) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR4_turn2_p91 : groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 25)
    (tailFor 25)) 91) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyR4_turn2_size : sizeGroup recordSet .once (turnGroup keyRShape4 (tailFor 25) (tailFor
    25)) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ = groupOfM (turnGroup
    keyRShape4 (tailFor 25) (tailFor 25)) 91 :=
  congrArg (groupOfM (turnGroup keyRShape4 (tailFor 25) (tailFor 25)))
    (trace91 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyRShape4 (tailFor 25)
      (tailFor 25)) m) ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩)
      keyR4_turn2_p3 keyR4_turn2_p4 keyR4_turn2_p8 keyR4_turn2_p16 keyR4_turn2_p32 keyR4_turn2_p64
      keyR4_turn2_p128 keyR4_turn2_p96 keyR4_turn2_p80 keyR4_turn2_p88 keyR4_turn2_p92
      keyR4_turn2_p90 keyR4_turn2_p91)

theorem keyR4_turn2_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyRShape4 (tailFor 25) (tailFor 25)) 91)).mainAt.agree (margin recordSet) = 25 := by
  decide +kernel

/-- Turn 2 of stage 4, from 25 positions. -/
theorem keyR4_turn2 : turn recordSet .once
    ⟨stageCubeBits keyRShape4, 1, 4 + 3 * max keyR3.main.r 1024⟩ keyRShape4
    (tailFor 25) (tailFor 25) 25 =
      .settled keyR4 25 :=
  turn_settled_of (by decide +kernel) keyR4_turn2_size keyR4_turn2_p91 keyR4_turn2_pos (by decide)

end OnBytes.Params

#print axioms OnBytes.Params.keyR4_turn1
#print axioms OnBytes.Params.keyR4_turn2
