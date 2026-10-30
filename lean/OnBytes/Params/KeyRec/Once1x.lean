-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/Once1x.lean: one sizing of one group in a turn of the iteration over the three
groups of the test on the table of a key of full size (keyTurn1_x), from its parts.

One kernel evaluation a trial of the search for m (OnBytes/Params/Fit/TurnForward.lean says why): a
module's own memory stays far below what one evaluation of a whole turn takes. The theorems are
checked one behind the other (Elab.async false), so that their memory does not add up.

Main names.
  keyTurn1_x: what Params.sizeOne returns there.
  keyTurn1_x_p‹m›, keyTurn1_x_size, keyTurn1_x_pos: the trials, the sized group, the positions.

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
abbrev keyTurn1_x_g : GroupSize := turnGroup keyGroups.foldedShape (tailFor ({} : Sizing).t)
    (tailFor (({} : Sizing).t + ({} : Sizing).t))

/-- What the group bears. -/
abbrev keyTurn1_x_load : GroupLoad := ⟨stageCubeBits keyTurn1_x_g, 2, keyGroups.foldedRows⟩

theorem keyTurn1_x_p3 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_x_g 3)
    keyTurn1_x_load = true := by
  decide +kernel

theorem keyTurn1_x_p4 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_x_g 4)
    keyTurn1_x_load = true := by
  decide +kernel

theorem keyTurn1_x_p8 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_x_g 8)
    keyTurn1_x_load = true := by
  decide +kernel

theorem keyTurn1_x_p16 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_x_g 16)
    keyTurn1_x_load = true := by
  decide +kernel

theorem keyTurn1_x_p32 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_x_g 32)
    keyTurn1_x_load = true := by
  decide +kernel

theorem keyTurn1_x_p64 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_x_g 64)
    keyTurn1_x_load = true := by
  decide +kernel

theorem keyTurn1_x_p128 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_x_g 128)
    keyTurn1_x_load = true := by
  decide +kernel

theorem keyTurn1_x_p256 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_x_g 256)
    keyTurn1_x_load = false := by
  decide +kernel

theorem keyTurn1_x_p192 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_x_g 192)
    keyTurn1_x_load = false := by
  decide +kernel

theorem keyTurn1_x_p160 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_x_g 160)
    keyTurn1_x_load = true := by
  decide +kernel

theorem keyTurn1_x_p176 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_x_g 176)
    keyTurn1_x_load = true := by
  decide +kernel

theorem keyTurn1_x_p184 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_x_g 184)
    keyTurn1_x_load = false := by
  decide +kernel

theorem keyTurn1_x_p180 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_x_g 180)
    keyTurn1_x_load = true := by
  decide +kernel

theorem keyTurn1_x_p182 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_x_g 182)
    keyTurn1_x_load = true := by
  decide +kernel

theorem keyTurn1_x_p183 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_x_g 183)
    keyTurn1_x_load = false := by
  decide +kernel

theorem keyTurn1_x_size : sizeGroup recordSet keyGroups.shared keyTurn1_x_g keyTurn1_x_load =
    groupOfM keyTurn1_x_g 182 :=
  congrArg (groupOfM keyTurn1_x_g)
    (trace182 (fun m => groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_x_g m)
      keyTurn1_x_load)
      keyTurn1_x_p3 keyTurn1_x_p4 keyTurn1_x_p8 keyTurn1_x_p16 keyTurn1_x_p32 keyTurn1_x_p64
      keyTurn1_x_p128 keyTurn1_x_p256 keyTurn1_x_p192 keyTurn1_x_p160 keyTurn1_x_p176
      keyTurn1_x_p184 keyTurn1_x_p180 keyTurn1_x_p182 keyTurn1_x_p183)

theorem keyTurn1_x_pos : scopePositions recordSet keyGroups.shared (analysis recordSet (groupOfM
    keyTurn1_x_g 182)).mainAt.agree (margin recordSet) = 97 := by
  decide +kernel

theorem keyTurn1_x : sizeOne recordSet keyGroups.foldedShape keyLin.folded keyGroups.shared
    ({} : Sizing).t (({} : Sizing).t + ({} : Sizing).t) keyGroups.foldedRows {} = some keyX0 :=
  sizeOne_serves (by decide +kernel) keyTurn1_x_size keyTurn1_x_p182
    keyTurn1_x_pos
    (by decide)

end OnBytes.Params

#print axioms OnBytes.Params.keyTurn1_x
