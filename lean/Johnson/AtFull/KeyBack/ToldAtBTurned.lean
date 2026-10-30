-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/ToldAtBTurned.lean: TWO CONTROLS OF ToldAtB.lean ON THE ORDER INSIDE A
TENANT's LIST OF GROUPS. At the shared chain's trees number 1 and 2 a tenant joins two groups: [250,
300] and [250, 200] (Johnson/HB/LLHARD/KB4/Told.lean). Here each list is turned round, and at the
very term of `told_B` the kernel's evaluation comes out the other way. By evaluations in Lean's
kernel (`decide +kernel`).
  `told_B_bent_turned_one`: [300, 250] at tree number 1. `told_B_bent_turned_two`: [200, 250] at
    tree number 2.
The two follow from `told_B` too, and add nothing to it: they show that the decision reads the order
of a tenant's groups. That each right side parts from the written table in that list alone:
`base_B_turned_one`, `base_B_turned_two` (ToldBentBases.lean).
Limits. Two closed facts on the written sendings, the typed sizes and another file's written table:
they name no m and no public file. That the list of groups is what `Key.groupsAtLabel` gives at the
sendings' labels is not said here. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.ToldAtB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G (ChainSends Sending keySends0 keySends1 keySends2)
open Johnson.G.OfPlan
open VerifiableInference.Desc.Key
open Lk6.AtPlan (keyFull)

theorem told_B_bent_turned_one :
    ¬ toldRun keySends1 groupsB 0 masksB (heldMask keyFull.once.shape) =
      Johnson.KB4.told2.take 1 ++ [⟨22, 36, [⟨36, 0, 3, true, [300, 250]⟩]⟩] ++
        Johnson.KB4.told2.drop 2 := by
  decide +kernel

theorem told_B_bent_turned_two :
    ¬ toldRun keySends1 groupsB 0 masksB (heldMask keyFull.once.shape) =
      Johnson.KB4.told2.take 2 ++ [⟨13, 3, [⟨0, 3, 1, true, [200, 250]⟩]⟩] ++
        Johnson.KB4.told2.drop 3 := by
  decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.told_B_bent_turned_one
#print axioms Johnson.AtFull.KeyBack.told_B_bent_turned_two
