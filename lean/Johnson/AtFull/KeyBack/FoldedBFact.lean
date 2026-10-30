-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/FoldedBFact.lean: ONE CLOSED FACT, AND A CONTROL: `FoldedB` (TreeProps.lean)
holds: the first opening of the test on the folded row's group reads the shared chain's trees number
0 and 2. The trees are rewritten to the form that the kernel can run (`trees_B`, TreesAtKey.lean);
then by an evaluation in Lean's kernel (`decide +kernel`).
  `folded_B`: the fact.
  `folded_B_bent`: at the very term, with one number bent (324 to 325), the kernel's evaluation
    comes out the other way. The control follows from the fact too, and adds nothing to it.
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

theorem folded_B : FoldedB := by
  unfold FoldedB
  rw [show treesB = runB from trees_B]
  decide +kernel

theorem folded_B_bent :
    ¬ foldedFirst keyFull.once.shape treesB =
      [(⟨24, 325, false, 0⟩, .own 0), (⟨13, 3, false, 2⟩, .own 2)] := by
  rw [show treesB = runB from trees_B]
  decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.folded_B
#print axioms Johnson.AtFull.KeyBack.folded_B_bent
