-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/ToldAtA.lean: ONE CLOSED FACT, AND CONTROLS: what is told of the trees of the
key file's first chain, run at the written sendings and the written groups (`toldRun`, ToldRun.lean;
ToldGroups.lean), is `Johnson.KB4.told1` (Johnson/HB/LLHARD/KB4/Told.lean). By an evaluation in
Lean's kernel (`decide +kernel`).
  `told_A`: the fact.
  `told_A_bent_group`, `told_A_bent_order`: at the very term the kernel's evaluation comes out the
    other way: the first tree's tenant's group bent (300 to 301); the six trees in the reverse
    order. The controls follow from the fact too, and add nothing to it.
Limits. A closed fact on the written sendings, the typed sizes and another file's written table: it
names no m and no public file. That the list of groups is what `Key.groupsAtLabel` gives at the
sendings' labels is not said here. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.ToldRun
import Johnson.AtFull.KeyBack.ToldGroups
import Johnson.G.SendsWritten
import Johnson.HB.LLHARD.KB4.Told

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G (ChainSends Sending keySends0 keySends1 keySends2)
open Johnson.G.OfPlan
open VerifiableInference.Desc.Key

theorem told_A : toldRun keySends0 groupsA 1 [] none = Johnson.KB4.told1 := by decide +kernel

theorem told_A_bent_group :
    ¬ toldRun keySends0 groupsA 1 [] none =
      ⟨13, 3, [⟨0, 3, 1, true, [301]⟩]⟩ :: Johnson.KB4.told1.tail := by decide +kernel

theorem told_A_bent_order :
    ¬ toldRun keySends0 groupsA 1 [] none =
      Johnson.KB4.told1.reverse := by decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.told_A
#print axioms Johnson.AtFull.KeyBack.told_A_bent_group
#print axioms Johnson.AtFull.KeyBack.told_A_bent_order
