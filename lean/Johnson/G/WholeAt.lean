-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/WholeAt.lean: a third twin of `OnBytes.Three.Whole.of`, which takes the numbers of trees
of the first two chains and the list of all openings as arguments, with the proof that it equals
`Whole.of` where these are the computed ones.

In `Whole.of` the list of all openings is used once for every tree's shape and once for every row of
the table of trees. Where the list is written out, and one evaluation shows that it is the computed
one, the later uses look into a short written list. Definitions and proofs.
Main names:
  `wholeW t₁ t₂ all R₁ R₂ R₃`: `wholeE` (Johnson/G/WholeEager.lean) with the three as arguments.
  `whole_eqW`: from `rootsE 0 R₁ = t₁`, `rootsE 0 R₂ = t₂` and "the three chains' openings in a row
    are `all`": `Three.Whole.of R₁ R₂ R₃ = wholeW t₁ t₂ all R₁ R₂ R₃`.
Limits: general; no value is treated. Nothing on soundness.

-/
import Johnson.G.WholeEager

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G

open OnBytes.Three
open OnBytes.Params (Rounds)

/-- `wholeE` with the two numbers of trees and the list of all openings as arguments. -/
def wholeW (t₁ t₂ : Nat) (all : List (Nat × Fmt.Shape × Nat × Nat)) (R₁ R₂ R₃ : Rounds) : Whole :=
  let ds₁ := rdsE all t₁ t₂ 0 0 0 0 R₁
  let ds₂ := rdsE all t₁ t₂ 1 t₁ 0 0 R₂
  let ds₃ := rdsE all t₁ t₂ 2 (t₁ + t₂) (first₃ t₁) 0 R₃
  ⟨ds₁, ds₂, ds₃,
    treesE all 0 0 ds₁ ++ (treesE all 1 t₁ ds₂ ++ treesE all 2 (t₁ + t₂) ds₃),
    t₁, t₂, rootsE 0 R₃, all⟩

theorem whole_eqW {t₁ t₂ : Nat} {all : List (Nat × Fmt.Shape × Nat × Nat)} {R₁ R₂ R₃ : Rounds}
    (h1 : rootsE 0 R₁ = t₁) (h2 : rootsE 0 R₂ = t₂)
    (ha : opensE t₁ t₂ 0 0 R₁ ++ (opensE t₁ t₂ 1 0 R₂ ++ opensE t₁ t₂ 2 0 R₃) = all) :
    Whole.of R₁ R₂ R₃ = wholeW t₁ t₂ all R₁ R₂ R₃ := by
  subst h1 h2 ha
  rw [whole_eqE]
  unfold wholeE wholeW
  simp only [force_eq]

end Johnson.G

#print axioms Johnson.G.whole_eqW
