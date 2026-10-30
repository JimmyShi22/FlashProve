-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/Once2x.lean: one sizing of one group in a turn of the iteration over the three
groups of the test on the table of a key of full size (keyTurn2_x), from its parts.

One kernel evaluation a trial of the search for m (OnBytes/Params/Fit/TurnForward.lean says why): a
module's own memory stays far below what one evaluation of a whole turn takes. The theorems are
checked one behind the other (Elab.async false), so that their memory does not add up.

Main names.
  keyTurn2_x: what Params.sizeOne returns there.
  keyTurn2_x_p‹m›, keyTurn2_x_size, keyTurn2_x_pos: the trials, the sized group, the positions.

Limits. A closed statement at the typed values alone. Nothing on soundness. What the whole leaves
unsaid stands in the head of OnBytes/Params/KeyRec/Once.lean.

-/
import OnBytes.Params.KeyRec.OnceDefs
import OnBytes.Params.KeyRec.Traces

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace OnBytes.Params

/-- The group of this sizing: the shape with the two numbers of random entries. -/
abbrev keyTurn2_x_g : GroupSize := turnGroup keyGroups.foldedShape (tailFor keyX0.t) (tailFor
    (keyX0.t + keyY0.t))

/-- What the group bears. -/
abbrev keyTurn2_x_load : GroupLoad := ⟨stageCubeBits keyTurn2_x_g, 2, keyGroups.foldedRows⟩

theorem keyTurn2_x_p3 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn2_x_g 3)
    keyTurn2_x_load = true := by
  decide +kernel

theorem keyTurn2_x_p4 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn2_x_g 4)
    keyTurn2_x_load = true := by
  decide +kernel

theorem keyTurn2_x_p8 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn2_x_g 8)
    keyTurn2_x_load = true := by
  decide +kernel

theorem keyTurn2_x_p16 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn2_x_g 16)
    keyTurn2_x_load = true := by
  decide +kernel

theorem keyTurn2_x_p32 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn2_x_g 32)
    keyTurn2_x_load = true := by
  decide +kernel

theorem keyTurn2_x_p64 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn2_x_g 64)
    keyTurn2_x_load = true := by
  decide +kernel

theorem keyTurn2_x_p128 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn2_x_g 128)
    keyTurn2_x_load = true := by
  decide +kernel

theorem keyTurn2_x_p256 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn2_x_g 256)
    keyTurn2_x_load = false := by
  decide +kernel

theorem keyTurn2_x_p192 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn2_x_g 192)
    keyTurn2_x_load = false := by
  decide +kernel

theorem keyTurn2_x_p160 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn2_x_g 160)
    keyTurn2_x_load = true := by
  decide +kernel

theorem keyTurn2_x_p176 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn2_x_g 176)
    keyTurn2_x_load = true := by
  decide +kernel

theorem keyTurn2_x_p184 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn2_x_g 184)
    keyTurn2_x_load = false := by
  decide +kernel

theorem keyTurn2_x_p180 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn2_x_g 180)
    keyTurn2_x_load = true := by
  decide +kernel

theorem keyTurn2_x_p182 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn2_x_g 182)
    keyTurn2_x_load = true := by
  decide +kernel

theorem keyTurn2_x_p183 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn2_x_g 183)
    keyTurn2_x_load = false := by
  decide +kernel

theorem keyTurn2_x_size : sizeGroup recordSet keyGroups.shared keyTurn2_x_g keyTurn2_x_load =
    groupOfM keyTurn2_x_g 182 :=
  congrArg (groupOfM keyTurn2_x_g)
    (trace182 (fun m => groupHolds recordSet keyGroups.shared (groupOfM keyTurn2_x_g m)
      keyTurn2_x_load)
      keyTurn2_x_p3 keyTurn2_x_p4 keyTurn2_x_p8 keyTurn2_x_p16 keyTurn2_x_p32 keyTurn2_x_p64
      keyTurn2_x_p128 keyTurn2_x_p256 keyTurn2_x_p192 keyTurn2_x_p160 keyTurn2_x_p176
      keyTurn2_x_p184 keyTurn2_x_p180 keyTurn2_x_p182 keyTurn2_x_p183)

theorem keyTurn2_x_pos : scopePositions recordSet keyGroups.shared (analysis recordSet (groupOfM
    keyTurn2_x_g 182)).mainAt.agree (margin recordSet) = 97 := by
  decide +kernel

theorem keyTurn2_x : sizeOne recordSet keyGroups.foldedShape keyLin.folded keyGroups.shared
    keyX0.t (keyX0.t + keyY0.t) keyGroups.foldedRows keyX0 = some keyX1 :=
  sizeOne_serves (by decide +kernel) keyTurn2_x_size keyTurn2_x_p182
    keyTurn2_x_pos
    (by decide)

end OnBytes.Params

#print axioms OnBytes.Params.keyTurn2_x
