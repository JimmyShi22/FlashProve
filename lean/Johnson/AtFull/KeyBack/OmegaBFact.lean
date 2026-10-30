-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/OmegaBFact.lean: ONE CLOSED FACT, AND A CONTROL: `OmegaB` (TreeProps.lean)
holds: the first opening of the test on Omega's group reads the shared chain's trees number 1 and 2.
The trees are rewritten to the form that the kernel can run (`trees_B`, TreesAtKey.lean); then
by an evaluation in Lean's kernel (`decide +kernel`).
  `omega_B`: the fact.
  `omega_B_bent`: at the very term, with one number bent (36 to 37), the kernel's evaluation comes
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

theorem omega_B : OmegaB := by
  unfold OmegaB
  rw [show treesB = runB from trees_B]
  decide +kernel

theorem omega_B_bent :
    ¬ ((sharedOpens keyFull.once.shape treesB)[2 + (switchOpens 0 .folded treesB).length]?).map
        (fun x => (x.1.dropLast, 0)) =
      some ([(⟨22, 37, false, 1⟩, .own 1), (⟨13, 3, false, 2⟩, .own 2)], 0) := by
  rw [show treesB = runB from trees_B]
  decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.omega_B
#print axioms Johnson.AtFull.KeyBack.omega_B_bent
