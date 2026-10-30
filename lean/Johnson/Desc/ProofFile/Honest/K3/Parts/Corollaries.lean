-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/Corollaries.lean: the honest side of the kind "lookup" (K3):
what follows at once from Honest/K3/Parts/Proof.lean and Numbered.lean. Theorems with
proofs; no definition.

  `lawfulP_of_fit`         CONDITIONAL ON `Fit R` AND `SpecAtP R N w`: the specification's summands
                           at several parts are lawful: the premise on the numbering of
                           challenges is paid
  `numbered_of_numberedP`  the facts on numbering at every part give those at one part
                           (Honest/K3/Law/SpecLawful.lean's `Numbered`)
  `numbered_of_fit'`       CONDITIONAL ON `Fit R` ALONE: `Numbered R`: no premise on the number of
                           parts, and no closed form of the number of rounds in front of a stage

Limits. A member of `Fit R` and `SpecAtP R N w`: Honest/K3/Parts/Member.lean, by evaluation.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K3.Parts.Proof
import Johnson.Desc.ProofFile.Honest.K3.Parts.Numbered

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.Spec (Numbered planesOf)

/-- **CONDITIONAL ON `Fit R` AND `SpecAtP R N w`: the specification's summands at several parts of
keys are lawful.** A member of both, by evaluation: Honest/K3/Parts/Member.lean. -/
theorem lawfulP_of_fit {P : Type} (N : KE → TwV.Nums P KE) (w : Hidden) (R : Course Ask)
    (hF : Fit R)
    (hS : SpecAtP R N w) :
    Lawful R (planesOf (dataAt N w R.pts)) (keysOfP (dataP N R.f.parts R.f.orders w R.pts)) :=
  lawfulSpecP P N w R hF (numberedP_of_fit R hF) hS

/-- The facts on numbering at every part give those at one part. -/
theorem numbered_of_numberedP {W : Type} (R : Course W) (h : NumberedP R) : Numbered R where
  same := fun s hs => by
    have := h.same s hs
    cases s <;> first | exact this | exact trivial
  len := h.len
  key := fun m hm => by
    cases hp : R.f.parts with
    | nil =>
      rw [hp] at hm
      exact absurd hm (Nat.not_lt_zero _)
    | cons v l =>
      rw [hp] at hm
      exact h.key (v, 0) (by rw [hp]; simp) m hm
  tab := h.tab
  zb0 := h.zb0
  zb1 := h.zb1
  masks := h.masks

/-- **CONDITIONAL ON `Fit R` ALONE: `Numbered R`.** -/
theorem numbered_of_fit' {W : Type} (R : Course W) (hF : Fit R) : Numbered R :=
  numbered_of_numberedP R (numberedP_of_fit R hF)

#print axioms ProofFile.Honest.K3.Parts.lawfulP_of_fit
#print axioms ProofFile.Honest.K3.Parts.numbered_of_numberedP
#print axioms ProofFile.Honest.K3.Parts.numbered_of_fit'

end ProofFile.Honest.K3.Parts
