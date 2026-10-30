-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/OwnABFact.lean: ONE CLOSED FACT, AND A CONTROL: `OwnAB` (TreeProps.lean)
holds: the first opening of the own test reads the first chain's trees number 0 and 5 and the shared
chain's tree number 1, each taken over. The trees are rewritten to the form that the kernel can run
(`trees_A`, `trees_B`, TreesAtKey.lean); then by an evaluation in Lean's kernel (`decide +kernel`).
  `own_AB`: the fact.
  `own_AB_bent`: at the very term, with one number bent (12 to 13), the kernel's evaluation comes
    out the other way. The control follows from the fact too, and adds nothing to it.
Limits. A closed fact on the written sendings and the typed sizes: it names no m and no public file.
That a key file's chains bear these sendings is not said here.
Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.TreeProps
import Johnson.AtFull.KeyBack.TreesAtKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G (ChainSends keySends0 keySends1 keySends2)
open Johnson.G.OfPlan
open VerifiableInference.Desc.Key
open Lk6.AtPlan (keyFull)

theorem own_AB : OwnAB := by
  unfold OwnAB
  rw [show treesA = runA from trees_A, show treesB = runB from trees_B]
  decide +kernel

theorem own_AB_bent :
    ¬ ownFirst keyFull.once.shape treesA treesB =
      [(⟨13, 3, false, 0⟩, .taken 0 0), (⟨22, 13, false, 5⟩, .taken 0 5),
        (⟨22, 36, false, 1⟩, .taken 1 1)] := by
  rw [show treesA = runA from trees_A, show treesB = runB from trees_B]
  decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.own_AB
#print axioms Johnson.AtFull.KeyBack.own_AB_bent
