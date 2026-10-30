-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/FirstAFact.lean: ONE CLOSED FACT, AND CONTROLS: `FirstA` (TreeProps.lean)
holds: the first opening of the ranges' test reads the first chain's tree number 1, of depth 22 and
77 words a column. The trees are rewritten to the form that the kernel can run (`trees_A`,
TreesAtKey.lean); then by an evaluation in Lean's kernel (`decide +kernel`).
  `first_A`: the fact.
  `first_A_bent`, `first_A_bent_depth`, `first_A_bent_tree`, `first_A_bent_source`: at the very
    term, with one part of a tree bent each time (the words: 78; the depth: 23; the tree's number:
    2; the source: own 2), the kernel's evaluation comes out the other way. The controls follow from
    the fact too, and add nothing to it.
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

theorem first_A : FirstA := by
  unfold FirstA
  rw [show treesA = runA from trees_A]
  decide +kernel

theorem first_A_bent :
    ¬ rangesFirst treesA = [(⟨22, 78, false, 1⟩, .own 1)] := by
  rw [show treesA = runA from trees_A]
  decide +kernel

theorem first_A_bent_depth :
    ¬ rangesFirst treesA = [(⟨23, 77, false, 1⟩, .own 1)] := by
  rw [show treesA = runA from trees_A]
  decide +kernel

theorem first_A_bent_tree :
    ¬ rangesFirst treesA = [(⟨22, 77, false, 2⟩, .own 1)] := by
  rw [show treesA = runA from trees_A]
  decide +kernel

theorem first_A_bent_source :
    ¬ rangesFirst treesA = [(⟨22, 77, false, 1⟩, .own 2)] := by
  rw [show treesA = runA from trees_A]
  decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.first_A
#print axioms Johnson.AtFull.KeyBack.first_A_bent
#print axioms Johnson.AtFull.KeyBack.first_A_bent_depth
#print axioms Johnson.AtFull.KeyBack.first_A_bent_tree
#print axioms Johnson.AtFull.KeyBack.first_A_bent_source
