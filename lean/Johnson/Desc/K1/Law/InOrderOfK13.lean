-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- A copy of a working file of this project that is not in this repository. Its second theorem
-- (inOrder_of_fillK13) is left out: it reads the conjunct off fillK13 by name, which does not lay it.
/-
Johnson/Desc/K1/Law/InOrderOfK13.lean: the Bool `inOrderK13` (Johnson/Desc/K13/Law/FillK13.lean), a
conjunct of "in order" at a meaning that the layer `fillK13Plus` has filled, gives `InOrder` of the
record's statement (Johnson/Desc/Means/Order.lean).

Main name: `inOrder_of_k13`.

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K13.Law.FillK13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes
open OnBytes.Means (InOrder)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.K13.Law (inOrderK13)

/-- The Bool's yes gives that the statement is in order. -/
theorem inOrder_of_k13 (codes : Codes) (shape : Params.ReqShape) (layout : Params.ReqLayout) (s : S)
    (h : inOrderK13 codes shape layout s = true) : InOrder s.st := by
  unfold inOrderK13 at h
  simp only [Bool.and_eq_true] at h
  exact (OnBytes.Means.tidy4B_iff.1 h.1.1.1).inOrder

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.inOrder_of_k13
