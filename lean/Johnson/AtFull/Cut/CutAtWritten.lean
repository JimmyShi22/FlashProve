-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Cut/CutAtWritten.lean: THE FIRST CHAIN's TABLE OF STRETCHES AT THE WRITTEN ROUNDS OF
THE FULL SIZE's PROOF FILE IS THE WRITTEN TABLE: `cutOf (dryProofFull.1.map (·.1.entry)) = some
cutWritten`. One decision of Lean's kernel, at the eager twin; the law of the twin carries it to
`cutOf` itself.

  `cutK_written`: `cutOfK ‹the entries› = some cutWritten`: by `decide +kernel`
    (Johnson/AtFull/Cut/CutEager.lean · CutWrittenLit.lean).
  **`cut_written`**: the same of `cutOf` (Johnson/Desc/First/Driver/Cut.lean): by `cutOfK_eq`.
  `cut_isSome`: so a table is returned.
`Cut` derives no decidable equality in its own file: `cutDecEq` gives one, as an instance in this
file alone.
Limits. The full size alone. It speaks of the WRITTEN rounds (Johnson/G/DryProofLit.lean): that
these are the planner's at any public files is not said here. What a row is worth is `cutOf`'s own
file's to say. Nothing on soundness. On hiding nothing.

-/
import Johnson.G.DryProofLit
import Johnson.AtFull.Cut.CutEager
import Johnson.AtFull.Cut.CutWrittenLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Cut
open VerifiableInference.Desc.First
open Johnson.G (dryProofFull)

/-- Equality of rows is decidable. A definition with a name, an instance IN THIS FILE ALONE: whoever
imports the file gets the three theorems and no new instance on `Cut`. -/
@[reducible] def cutDecEq : DecidableEq Cut
  | ⟨a₁, a₂, a₃, a₄, a₅⟩, ⟨b₁, b₂, b₃, b₄, b₅⟩ =>
    if h₁ : a₁ = b₁ then
      if h₂ : a₂ = b₂ then
        if h₃ : a₃ = b₃ then
          if h₄ : a₄ = b₄ then
            if h₅ : a₅ = b₅ then isTrue (by rw [h₁, h₂, h₃, h₄, h₅])
            else isFalse fun h => h₅ (congrArg Cut.take h)
          else isFalse fun h => h₄ (congrArg Cut.kind h)
        else isFalse fun h => h₃ (congrArg Cut.place h)
      else isFalse fun h => h₂ (congrArg Cut.step h)
    else isFalse fun h => h₁ (congrArg Cut.look h)

attribute [local instance] cutDecEq

set_option maxRecDepth 1000000 in
/-- The eager twin at the written rounds' entries. -/
theorem cutK_written : cutOfK (dryProofFull.1.map (·.1.entry)) = some cutWritten := by
  decide +kernel

/-- **THE TABLE AT THE WRITTEN ROUNDS.** -/
theorem cut_written : cutOf (dryProofFull.1.map (·.1.entry)) = some cutWritten :=
  (cutOfK_eq _).symm.trans cutK_written

theorem cut_isSome : (cutOf (dryProofFull.1.map (·.1.entry))).isSome = true := by
  rw [cut_written]
  rfl

end Johnson.AtFull.Cut

#print axioms Johnson.AtFull.Cut.cutK_written
#print axioms Johnson.AtFull.Cut.cut_written
#print axioms Johnson.AtFull.Cut.cut_isSome
