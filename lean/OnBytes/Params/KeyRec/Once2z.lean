-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/Once2z.lean: one sizing of one group in a turn of the iteration over the three
groups of the test on the table of a key of full size (keyTurn2_z), from its parts.

One kernel evaluation a trial of the search for m (OnBytes/Params/Fit/TurnForward.lean says why): a
module's own memory stays far below what one evaluation of a whole turn takes. The theorems are
checked one behind the other (Elab.async false), so that their memory does not add up.

Main names.
  keyTurn2_z: what Params.sizeOne returns there.
  keyTurn2_z_p‹m›, keyTurn2_z_size, keyTurn2_z_pos: the trials, the sized group, the positions.

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
abbrev keyTurn2_z_g : GroupSize := turnGroup keyGroups.ownShape (tailFor (keyY0.t + keyLin.requests
    * keyZ0.t)) (tailFor keyZ0.t)

/-- What the group bears. -/
abbrev keyTurn2_z_load : GroupLoad := ⟨stageCubeBits keyTurn2_z_g, 2, (2 + 3 * recordSet.samples)⟩

theorem keyTurn2_z_p3 : groupHolds recordSet keyGroups.request (groupOfM keyTurn2_z_g 3)
    keyTurn2_z_load = true := by
  decide +kernel

theorem keyTurn2_z_p4 : groupHolds recordSet keyGroups.request (groupOfM keyTurn2_z_g 4)
    keyTurn2_z_load = true := by
  decide +kernel

theorem keyTurn2_z_p8 : groupHolds recordSet keyGroups.request (groupOfM keyTurn2_z_g 8)
    keyTurn2_z_load = true := by
  decide +kernel

theorem keyTurn2_z_p16 : groupHolds recordSet keyGroups.request (groupOfM keyTurn2_z_g 16)
    keyTurn2_z_load = true := by
  decide +kernel

theorem keyTurn2_z_p32 : groupHolds recordSet keyGroups.request (groupOfM keyTurn2_z_g 32)
    keyTurn2_z_load = true := by
  decide +kernel

theorem keyTurn2_z_p64 : groupHolds recordSet keyGroups.request (groupOfM keyTurn2_z_g 64)
    keyTurn2_z_load = true := by
  decide +kernel

theorem keyTurn2_z_p128 : groupHolds recordSet keyGroups.request (groupOfM keyTurn2_z_g 128)
    keyTurn2_z_load = true := by
  decide +kernel

theorem keyTurn2_z_p256 : groupHolds recordSet keyGroups.request (groupOfM keyTurn2_z_g 256)
    keyTurn2_z_load = false := by
  decide +kernel

theorem keyTurn2_z_p192 : groupHolds recordSet keyGroups.request (groupOfM keyTurn2_z_g 192)
    keyTurn2_z_load = false := by
  decide +kernel

theorem keyTurn2_z_p160 : groupHolds recordSet keyGroups.request (groupOfM keyTurn2_z_g 160)
    keyTurn2_z_load = false := by
  decide +kernel

theorem keyTurn2_z_p144 : groupHolds recordSet keyGroups.request (groupOfM keyTurn2_z_g 144)
    keyTurn2_z_load = true := by
  decide +kernel

theorem keyTurn2_z_p152 : groupHolds recordSet keyGroups.request (groupOfM keyTurn2_z_g 152)
    keyTurn2_z_load = true := by
  decide +kernel

theorem keyTurn2_z_p156 : groupHolds recordSet keyGroups.request (groupOfM keyTurn2_z_g 156)
    keyTurn2_z_load = true := by
  decide +kernel

theorem keyTurn2_z_p158 : groupHolds recordSet keyGroups.request (groupOfM keyTurn2_z_g 158)
    keyTurn2_z_load = true := by
  decide +kernel

theorem keyTurn2_z_p159 : groupHolds recordSet keyGroups.request (groupOfM keyTurn2_z_g 159)
    keyTurn2_z_load = false := by
  decide +kernel

theorem keyTurn2_z_size : sizeGroup recordSet keyGroups.request keyTurn2_z_g keyTurn2_z_load =
    groupOfM keyTurn2_z_g 158 :=
  congrArg (groupOfM keyTurn2_z_g)
    (trace158 (fun m => groupHolds recordSet keyGroups.request (groupOfM keyTurn2_z_g m)
      keyTurn2_z_load)
      keyTurn2_z_p3 keyTurn2_z_p4 keyTurn2_z_p8 keyTurn2_z_p16 keyTurn2_z_p32 keyTurn2_z_p64
      keyTurn2_z_p128 keyTurn2_z_p256 keyTurn2_z_p192 keyTurn2_z_p160 keyTurn2_z_p144
      keyTurn2_z_p152 keyTurn2_z_p156 keyTurn2_z_p158 keyTurn2_z_p159)

theorem keyTurn2_z_pos : scopePositions recordSet keyGroups.request (analysis recordSet (groupOfM
    keyTurn2_z_g 158)).mainAt.agree (margin recordSet) = 49 := by
  decide +kernel

theorem keyTurn2_z : sizeOne recordSet keyGroups.ownShape keyLin.own keyGroups.request
    (keyY0.t + keyLin.requests * keyZ0.t) keyZ0.t (2 + 3 * recordSet.samples) keyZ0 =
      some keyZ1 :=
  sizeOne_serves (by decide +kernel) keyTurn2_z_size keyTurn2_z_p158
    keyTurn2_z_pos
    (by decide)

end OnBytes.Params

#print axioms OnBytes.Params.keyTurn2_z
