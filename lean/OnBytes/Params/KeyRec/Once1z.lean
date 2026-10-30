-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/Once1z.lean: one sizing of one group in a turn of the iteration over the three
groups of the test on the table of a key of full size (keyTurn1_z), from its parts.

One kernel evaluation a trial of the search for m (OnBytes/Params/Fit/TurnForward.lean says why): a
module's own memory stays far below what one evaluation of a whole turn takes. The theorems are
checked one behind the other (Elab.async false), so that their memory does not add up.

Main names.
  keyTurn1_z: what Params.sizeOne returns there.
  keyTurn1_z_p‹m›, keyTurn1_z_size, keyTurn1_z_pos: the trials, the sized group, the positions.

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
abbrev keyTurn1_z_g : GroupSize := turnGroup keyGroups.ownShape (tailFor (({} : Sizing).t +
    keyLin.requests * ({} : Sizing).t)) (tailFor ({} : Sizing).t)

/-- What the group bears. -/
abbrev keyTurn1_z_load : GroupLoad := ⟨stageCubeBits keyTurn1_z_g, 2, (2 + 3 * recordSet.samples)⟩

theorem keyTurn1_z_p3 : groupHolds recordSet keyGroups.request (groupOfM keyTurn1_z_g 3)
    keyTurn1_z_load = true := by
  decide +kernel

theorem keyTurn1_z_p4 : groupHolds recordSet keyGroups.request (groupOfM keyTurn1_z_g 4)
    keyTurn1_z_load = true := by
  decide +kernel

theorem keyTurn1_z_p8 : groupHolds recordSet keyGroups.request (groupOfM keyTurn1_z_g 8)
    keyTurn1_z_load = true := by
  decide +kernel

theorem keyTurn1_z_p16 : groupHolds recordSet keyGroups.request (groupOfM keyTurn1_z_g 16)
    keyTurn1_z_load = true := by
  decide +kernel

theorem keyTurn1_z_p32 : groupHolds recordSet keyGroups.request (groupOfM keyTurn1_z_g 32)
    keyTurn1_z_load = true := by
  decide +kernel

theorem keyTurn1_z_p64 : groupHolds recordSet keyGroups.request (groupOfM keyTurn1_z_g 64)
    keyTurn1_z_load = true := by
  decide +kernel

theorem keyTurn1_z_p128 : groupHolds recordSet keyGroups.request (groupOfM keyTurn1_z_g 128)
    keyTurn1_z_load = true := by
  decide +kernel

theorem keyTurn1_z_p256 : groupHolds recordSet keyGroups.request (groupOfM keyTurn1_z_g 256)
    keyTurn1_z_load = false := by
  decide +kernel

theorem keyTurn1_z_p192 : groupHolds recordSet keyGroups.request (groupOfM keyTurn1_z_g 192)
    keyTurn1_z_load = false := by
  decide +kernel

theorem keyTurn1_z_p160 : groupHolds recordSet keyGroups.request (groupOfM keyTurn1_z_g 160)
    keyTurn1_z_load = false := by
  decide +kernel

theorem keyTurn1_z_p144 : groupHolds recordSet keyGroups.request (groupOfM keyTurn1_z_g 144)
    keyTurn1_z_load = true := by
  decide +kernel

theorem keyTurn1_z_p152 : groupHolds recordSet keyGroups.request (groupOfM keyTurn1_z_g 152)
    keyTurn1_z_load = true := by
  decide +kernel

theorem keyTurn1_z_p156 : groupHolds recordSet keyGroups.request (groupOfM keyTurn1_z_g 156)
    keyTurn1_z_load = true := by
  decide +kernel

theorem keyTurn1_z_p158 : groupHolds recordSet keyGroups.request (groupOfM keyTurn1_z_g 158)
    keyTurn1_z_load = true := by
  decide +kernel

theorem keyTurn1_z_p159 : groupHolds recordSet keyGroups.request (groupOfM keyTurn1_z_g 159)
    keyTurn1_z_load = false := by
  decide +kernel

theorem keyTurn1_z_size : sizeGroup recordSet keyGroups.request keyTurn1_z_g keyTurn1_z_load =
    groupOfM keyTurn1_z_g 158 :=
  congrArg (groupOfM keyTurn1_z_g)
    (trace158 (fun m => groupHolds recordSet keyGroups.request (groupOfM keyTurn1_z_g m)
      keyTurn1_z_load)
      keyTurn1_z_p3 keyTurn1_z_p4 keyTurn1_z_p8 keyTurn1_z_p16 keyTurn1_z_p32 keyTurn1_z_p64
      keyTurn1_z_p128 keyTurn1_z_p256 keyTurn1_z_p192 keyTurn1_z_p160 keyTurn1_z_p144
      keyTurn1_z_p152 keyTurn1_z_p156 keyTurn1_z_p158 keyTurn1_z_p159)

theorem keyTurn1_z_pos : scopePositions recordSet keyGroups.request (analysis recordSet (groupOfM
    keyTurn1_z_g 158)).mainAt.agree (margin recordSet) = 49 := by
  decide +kernel

theorem keyTurn1_z : sizeOne recordSet keyGroups.ownShape keyLin.own keyGroups.request
    (({} : Sizing).t + keyLin.requests * ({} : Sizing).t) ({} : Sizing).t
    (2 + 3 * recordSet.samples) {} = some keyZ0 :=
  sizeOne_serves (by decide +kernel) keyTurn1_z_size keyTurn1_z_p158
    keyTurn1_z_pos
    (by decide)

end OnBytes.Params

#print axioms OnBytes.Params.keyTurn1_z
