-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/ToldAtB.lean: ONE CLOSED FACT, AND CONTROLS: what is told of the trees of the
key file's shared chain, run at the written sendings and the written groups (`toldRun`,
ToldRun.lean; ToldGroups.lean), is `Johnson.KB4.told2` (Johnson/HB/LLHARD/KB4/Told.lean). By an
evaluation in Lean's kernel (`decide +kernel`).
  `told_B`: the fact.
  `told_B_bent_group`, `told_B_bent_order`: at the very term the kernel's evaluation comes out the
    other way: the first tree's first tenant's group bent (200 to 201); the two trees that go in one
    round (numbers 1 and 2) changed about. The controls follow from the fact too, and add nothing to
    it.
Limits. A closed fact on the written sendings, the typed sizes and another file's written table: it
names no m and no public file. That the list of groups is what `Key.groupsAtLabel` gives at the
sendings' labels is not said here. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.ToldRun
import Johnson.AtFull.KeyBack.ToldGroups
import Johnson.G.SendsWritten
import Johnson.HB.LLHARD.KB4.Told
import Johnson.AtFull.KeyBack.FitsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G (ChainSends Sending keySends0 keySends1 keySends2)
open Johnson.G.OfPlan
open VerifiableInference.Desc.Key
open Lk6.AtPlan (keyFull)

theorem told_B :
    toldRun keySends1 groupsB 0 masksB (heldMask keyFull.once.shape) = Johnson.KB4.told2 := by
  decide +kernel

theorem told_B_bent_group :
    ¬ toldRun keySends1 groupsB 0 masksB (heldMask keyFull.once.shape) =
      ⟨24, 324, [⟨321, 0, 3, true, [201]⟩, ⟨0, 3, 1, false, []⟩]⟩ :: Johnson.KB4.told2.tail := by
  decide +kernel

theorem told_B_bent_order :
    ¬ toldRun keySends1 groupsB 0 masksB (heldMask keyFull.once.shape) =
      Johnson.KB4.told2.take 1 ++ [⟨13, 3, [⟨0, 3, 1, true, [250, 200]⟩]⟩,
        ⟨22, 36, [⟨36, 0, 3, true, [250, 300]⟩]⟩] ++ Johnson.KB4.told2.drop 3 := by decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.told_B
#print axioms Johnson.AtFull.KeyBack.told_B_bent_group
#print axioms Johnson.AtFull.KeyBack.told_B_bent_order
