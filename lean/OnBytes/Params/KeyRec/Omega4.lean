-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/Omega4.lean: the turns of the iteration that solves stage 4 of Omega's test of
a key of full size, each from its parts.

One kernel evaluation a trial of the search for m (OnBytes/Params/Fit/TurnForward.lean says why): a
module's own memory stays far below what one evaluation of a whole turn takes. The theorems are
checked one behind the other (Elab.async false), so that their memory does not add up.

Main names.
  keyO4_turn1 and so on: what each turn returns.
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

theorem keyO4_turn1_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 0)
    (tailFor 0)) 3) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO4_turn1_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 0)
    (tailFor 0)) 4) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO4_turn1_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 0)
    (tailFor 0)) 8) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO4_turn1_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 0)
    (tailFor 0)) 16) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO4_turn1_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 0)
    (tailFor 0)) 32) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO4_turn1_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 0)
    (tailFor 0)) 64) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO4_turn1_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 0)
    (tailFor 0)) 128) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO4_turn1_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 0)
    (tailFor 0)) 256) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO4_turn1_p512 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 0)
    (tailFor 0)) 512) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyO4_turn1_p384 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 0)
    (tailFor 0)) 384) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyO4_turn1_p320 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 0)
    (tailFor 0)) 320) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO4_turn1_p352 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 0)
    (tailFor 0)) 352) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyO4_turn1_p336 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 0)
    (tailFor 0)) 336) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO4_turn1_p344 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 0)
    (tailFor 0)) 344) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyO4_turn1_p340 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 0)
    (tailFor 0)) 340) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO4_turn1_p342 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 0)
    (tailFor 0)) 342) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyO4_turn1_p341 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 0)
    (tailFor 0)) 341) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO4_turn1_size : sizeGroup recordSet .once (turnGroup keyOShape4 (tailFor 0) (tailFor 0))
    ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = groupOfM (turnGroup keyOShape4
    (tailFor 0) (tailFor 0)) 341 :=
  congrArg (groupOfM (turnGroup keyOShape4 (tailFor 0) (tailFor 0)))
    (trace341 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 0)
      (tailFor 0)) m) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩)
      keyO4_turn1_p3 keyO4_turn1_p4 keyO4_turn1_p8 keyO4_turn1_p16 keyO4_turn1_p32 keyO4_turn1_p64
      keyO4_turn1_p128 keyO4_turn1_p256 keyO4_turn1_p512 keyO4_turn1_p384 keyO4_turn1_p320
      keyO4_turn1_p352 keyO4_turn1_p336 keyO4_turn1_p344 keyO4_turn1_p340 keyO4_turn1_p342
      keyO4_turn1_p341)

theorem keyO4_turn1_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyOShape4 (tailFor 0) (tailFor 0)) 341)).mainAt.agree (margin recordSet) = 39 := by
  decide +kernel

/-- Turn 1 of stage 4, from 0 positions. -/
theorem keyO4_turn1 : turn recordSet .once
    ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ keyOShape4
    (tailFor 0) (tailFor 0) 0 =
      .more ⟨⟨15, 1024, 0, true⟩, ⟨15, 512, 0, true⟩, 0, 0, 1, .johnson, 341⟩ 39 :=
  turn_more_of (by decide +kernel) keyO4_turn1_size keyO4_turn1_p341 keyO4_turn1_pos (by decide)

theorem keyO4_turn2_p3 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 39)
    (tailFor 39)) 3) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO4_turn2_p4 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 39)
    (tailFor 39)) 4) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO4_turn2_p8 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 39)
    (tailFor 39)) 8) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO4_turn2_p16 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 39)
    (tailFor 39)) 16) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO4_turn2_p32 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 39)
    (tailFor 39)) 32) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO4_turn2_p64 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 39)
    (tailFor 39)) 64) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO4_turn2_p128 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 39)
    (tailFor 39)) 128) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO4_turn2_p256 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 39)
    (tailFor 39)) 256) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO4_turn2_p512 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 39)
    (tailFor 39)) 512) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyO4_turn2_p384 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 39)
    (tailFor 39)) 384) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyO4_turn2_p320 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 39)
    (tailFor 39)) 320) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO4_turn2_p352 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 39)
    (tailFor 39)) 352) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyO4_turn2_p336 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 39)
    (tailFor 39)) 336) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO4_turn2_p344 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 39)
    (tailFor 39)) 344) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO4_turn2_p348 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 39)
    (tailFor 39)) 348) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyO4_turn2_p346 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 39)
    (tailFor 39)) 346) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = false := by
  decide +kernel

theorem keyO4_turn2_p345 : groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 39)
    (tailFor 39)) 345) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = true := by
  decide +kernel

theorem keyO4_turn2_size : sizeGroup recordSet .once (turnGroup keyOShape4 (tailFor 39) (tailFor
    39)) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ = groupOfM (turnGroup
    keyOShape4 (tailFor 39) (tailFor 39)) 345 :=
  congrArg (groupOfM (turnGroup keyOShape4 (tailFor 39) (tailFor 39)))
    (trace345 (fun m => groupHolds recordSet .once (groupOfM (turnGroup keyOShape4 (tailFor 39)
      (tailFor 39)) m) ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩)
      keyO4_turn2_p3 keyO4_turn2_p4 keyO4_turn2_p8 keyO4_turn2_p16 keyO4_turn2_p32 keyO4_turn2_p64
      keyO4_turn2_p128 keyO4_turn2_p256 keyO4_turn2_p512 keyO4_turn2_p384 keyO4_turn2_p320
      keyO4_turn2_p352 keyO4_turn2_p336 keyO4_turn2_p344 keyO4_turn2_p348 keyO4_turn2_p346
      keyO4_turn2_p345)

theorem keyO4_turn2_pos : scopePositions recordSet .once (analysis recordSet (groupOfM (turnGroup
    keyOShape4 (tailFor 39) (tailFor 39)) 345)).mainAt.agree (margin recordSet) = 39 := by
  decide +kernel

/-- Turn 2 of stage 4, from 39 positions. -/
theorem keyO4_turn2 : turn recordSet .once
    ⟨stageCubeBits keyOShape4, 1, 4 + 3 * max keyO3.main.r 1024⟩ keyOShape4
    (tailFor 39) (tailFor 39) 39 =
      .settled keyO4 39 :=
  turn_settled_of (by decide +kernel) keyO4_turn2_size keyO4_turn2_p345 keyO4_turn2_pos (by decide)

end OnBytes.Params

#print axioms OnBytes.Params.keyO4_turn1
#print axioms OnBytes.Params.keyO4_turn2
