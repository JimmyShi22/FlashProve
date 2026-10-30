-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstFull.lean: the one test under which the release's configuration's
own "held" is typed (fullShapeB, Johnson/Desc/Sound/PlanAsk.lean: the index's shape and the matrix's
two numbers are the full size's), evaluated by Lean's kernel at the typed shape of a proof file.
  full_real: the yes: decide +kernel
  full_of_shape: so at every shape that is the typed one
  full_no: a negative test: at the typed shape with one row more it says no

What is not claimed. That the parameters at a seat are the typed ones. Nothing on soundness, on an
honest prover or on hiding.

-/
import Johnson.Desc.Sound.PlanAsk
import Johnson.Goal.Numbers.K14CondAt
import Johnson.Goal.Numbers.WrittenAtZ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Johnson.G
open VerifiableInference.Desc.K1 (realSized)

theorem full_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧
    fullShapeB x.shape = true := by
  obtain ⟨x, a1, -, -⟩ := k14_real
  have h : (realSized.any fun p => fullShapeB p.1.shape) = true := by decide +kernel
  rw [a1, Option.any_some] at h
  exact ⟨x, a1, h⟩

/-- At every shape that is the typed one. -/
theorem full_of_shape {S : LinShape} {x : LinSized} (hx : realSized = some (x, codesFull2))
    (h : S = x.shape) : fullShapeB S = true := by
  obtain ⟨x', a1, hf⟩ := full_real
  obtain rfl := sized_one hx a1
  rw [h]
  exact hf

/-- **It can say no.** -/
theorem full_no : (realSized.any fun p =>
    fullShapeB { p.1.shape with matrixRows := p.1.shape.matrixRows + 1 }) = false := by
  decide +kernel

end Desc.K14.Law

#print axioms Desc.K14.Law.full_real
#print axioms Desc.K14.Law.full_of_shape
#print axioms Desc.K14.Law.full_no
