-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/ToldAtC.lean: ONE CLOSED FACT, AND A CONTROL: what is told of the trees of
the key file's second chain, run at the written sendings and the written groups (`toldRun`,
ToldRun.lean; ToldGroups.lean), is `Johnson.KB4.told3` (Johnson/HB/LLHARD/KB4/Told.lean). By an
evaluation in Lean's kernel (`decide +kernel`).
  `told_C`: the fact.
  `told_C_bent_group`: at the very term the kernel's evaluation comes out the other way: the first
    tree's first tenant's group bent (301 to 302). The control follows from the fact too, and adds
    nothing to it.
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

theorem told_C : toldRun keySends2 groupsC 0 [] none = Johnson.KB4.told3 := by decide +kernel

theorem told_C_bent_group :
    ¬ toldRun keySends2 groupsC 0 [] none =
      ⟨18, 96, [⟨48, 24, 3, true, [302]⟩, ⟨0, 24, 1, false, []⟩]⟩ :: Johnson.KB4.told3.tail := by
  decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.told_C
#print axioms Johnson.AtFull.KeyBack.told_C_bent_group
