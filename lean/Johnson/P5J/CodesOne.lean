--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/CodesOne.lean: where the proof file's value is laid (`P5J.LaidAt`,
Johnson/P5J/LaidOpens.lean), the codes of the first chain's parameters are the codes that the
planner sized. One call of Johnson/Desc/Sound/CodesOneAtOpen.lean at two fields of `LaidAt`: its
opening of the maker and its test on the plan, which speak of one description and one public part.

Main statements, at every `o` and at all three public files, from `LaidAt` alone:
  `At.codesOne`: `Zp.first.codes = Zp.p.chains.made.sized.proof.codes`.
  `At.reqShapeOne`: `Zp.first.shape = Zp.p.chains.made.sized.proof.request`.

Limits. That the value is laid is a premise. Nothing on `Zp.first.lin`. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.LaidOpens
import Johnson.Desc.Sound.CodesOneAtOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)

variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **The codes as read back are the codes as sized, where the value is laid.** -/
theorem codesOne (L : P5J.LaidAt o pol lay KL D r Zp Np cF) :
    Zp.first.codes = Zp.p.chains.made.sized.proof.codes := by
  obtain ⟨Bs, base, O⟩ := L.opened
  exact Desc.CodesOne.codes_one_open O L.planOk

/-- The same for the request's shape. -/
theorem reqShapeOne (L : P5J.LaidAt o pol lay KL D r Zp Np cF) :
    Zp.first.shape = Zp.p.chains.made.sized.proof.request := by
  obtain ⟨Bs, base, O⟩ := L.opened
  exact Desc.CodesOne.shape_one_open O L.planOk

end P5J.At

#print axioms P5J.At.codesOne
#print axioms P5J.At.reqShapeOne
