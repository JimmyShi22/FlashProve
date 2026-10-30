-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/Once1y.lean: one sizing of one group in a turn of the iteration over the three
groups of the test on the table of a key of full size (keyTurn1_y), from its parts.

One kernel evaluation a trial of the search for m (OnBytes/Params/Fit/TurnForward.lean says why): a
module's own memory stays far below what one evaluation of a whole turn takes. The theorems are
checked one behind the other (Elab.async false), so that their memory does not add up.

Main names.
  keyTurn1_y: what Params.sizeOne returns there.
  keyTurn1_y_p‹m›, keyTurn1_y_size, keyTurn1_y_pos: the trials, the sized group, the positions.

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
abbrev keyTurn1_y_g : GroupSize := turnGroup keyGroups.omegaShape (tailFor (({} : Sizing).t +
    keyLin.requests * ({} : Sizing).t)) (tailFor (({} : Sizing).t + ({} : Sizing).t))

/-- What the group bears. -/
abbrev keyTurn1_y_load : GroupLoad := ⟨stageCubeBits keyTurn1_y_g, 2, (1 + 2 * recordSet.samples)⟩

theorem keyTurn1_y_p3 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_y_g 3)
    keyTurn1_y_load = true := by
  decide +kernel

theorem keyTurn1_y_p4 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_y_g 4)
    keyTurn1_y_load = true := by
  decide +kernel

theorem keyTurn1_y_p8 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_y_g 8)
    keyTurn1_y_load = true := by
  decide +kernel

theorem keyTurn1_y_p16 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_y_g 16)
    keyTurn1_y_load = true := by
  decide +kernel

theorem keyTurn1_y_p32 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_y_g 32)
    keyTurn1_y_load = true := by
  decide +kernel

theorem keyTurn1_y_p64 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_y_g 64)
    keyTurn1_y_load = true := by
  decide +kernel

theorem keyTurn1_y_p128 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_y_g 128)
    keyTurn1_y_load = true := by
  decide +kernel

theorem keyTurn1_y_p256 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_y_g 256)
    keyTurn1_y_load = false := by
  decide +kernel

theorem keyTurn1_y_p192 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_y_g 192)
    keyTurn1_y_load = false := by
  decide +kernel

theorem keyTurn1_y_p160 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_y_g 160)
    keyTurn1_y_load = false := by
  decide +kernel

theorem keyTurn1_y_p144 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_y_g 144)
    keyTurn1_y_load = true := by
  decide +kernel

theorem keyTurn1_y_p152 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_y_g 152)
    keyTurn1_y_load = true := by
  decide +kernel

theorem keyTurn1_y_p156 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_y_g 156)
    keyTurn1_y_load = true := by
  decide +kernel

theorem keyTurn1_y_p158 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_y_g 158)
    keyTurn1_y_load = true := by
  decide +kernel

theorem keyTurn1_y_p159 : groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_y_g 159)
    keyTurn1_y_load = false := by
  decide +kernel

theorem keyTurn1_y_size : sizeGroup recordSet keyGroups.shared keyTurn1_y_g keyTurn1_y_load =
    groupOfM keyTurn1_y_g 158 :=
  congrArg (groupOfM keyTurn1_y_g)
    (trace158 (fun m => groupHolds recordSet keyGroups.shared (groupOfM keyTurn1_y_g m)
      keyTurn1_y_load)
      keyTurn1_y_p3 keyTurn1_y_p4 keyTurn1_y_p8 keyTurn1_y_p16 keyTurn1_y_p32 keyTurn1_y_p64
      keyTurn1_y_p128 keyTurn1_y_p256 keyTurn1_y_p192 keyTurn1_y_p160 keyTurn1_y_p144
      keyTurn1_y_p152 keyTurn1_y_p156 keyTurn1_y_p158 keyTurn1_y_p159)

theorem keyTurn1_y_pos : scopePositions recordSet keyGroups.shared (analysis recordSet (groupOfM
    keyTurn1_y_g 158)).mainAt.agree (margin recordSet) = 49 := by
  decide +kernel

theorem keyTurn1_y : sizeOne recordSet keyGroups.omegaShape keyLin.omega keyGroups.shared
    (({} : Sizing).t + keyLin.requests * ({} : Sizing).t) (({} : Sizing).t + ({} : Sizing).t)
    (1 + 2 * recordSet.samples) {} = some keyY0 :=
  sizeOne_serves (by decide +kernel) keyTurn1_y_size keyTurn1_y_p158
    keyTurn1_y_pos
    (by decide)

end OnBytes.Params

#print axioms OnBytes.Params.keyTurn1_y
