-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5PadsOfOffC.lean: kind K5: A PAYMENT BENEATH THE KIND's FROZEN NAMED CONDITION (K5CondAt, K5LeftOfCond.lean): ITS FIELD pads := PadsAll h (K5RestCells.lean) FROM THE NAMED TEST WITH CODE AtMg.offC (Johnson/P5J/HidBearsAtMg.lean) AT THE CONSTANT's OWN LETTERS.

Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)


Main names:
  `pads_of_offC`: **h.toAtMg.offC = true → PadsAll h**: ONE CALL of AtMg.placesOff (Johnson/P5J/HidBearsAtMg.lean: offC := placesOffC at At.cs Zp · At.arr Zp · At.ms Zp Z.lay · At.N Zp cF · At.X Zp · sizesOf · At.layout Zp · At.num Zp).
    THAT THE CALL TYPE-CHECKS IS LEAN's OWN WORD THAT PadsAll's LETTERS (h.𝔇.sent.codes · h.𝔇.arr · h.𝔇.ms · h.𝔇.N · h.𝔇.sent.layout) ARE THE CONSTANT's, BY UNFOLDING.
  `cellsOwn_of_offC`: so, with the frozen per-group field: offC · K5CellsCond h a x₁ idx → K5CellsOwn h g a x₁ idx.
Is it empty here? offC = true IS SHOWN AT NOTHING IN LEAN: a Bool on public data: a run's matter. As reported (an evaluation at the full-size public files, at the constant's letters; evidence, no proof; its print not
shown here) placesOffC says yes at all 25 lists, and no at two bent inputs.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5CellsOfOwn
import Johnson.P5J.HidBearsAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open P5J (AtMgA TS)

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA o Z D r Zp Np cF x)

/-- **The condition's field pads, from the named test offC at the constant's own letters.** -/
theorem pads_of_offC (hC : h.toAtMg.offC = true) : PadsAll h := h.toAtMg.placesOff hC

/-- With the frozen per-group field: the four that the field cells spends. -/
theorem cellsOwn_of_offC (hC : h.toAtMg.offC = true) (g : ℕ) {a : Attention.Plan} {x₁ : Look.Place} {idx : ℕ → ℕ}
    (C : K5CellsCond h a x₁ idx) : K5CellsOwn h g a x₁ idx := own_of_pads h (pads_of_offC h hC) g C

end

end H2K5.Door

#print axioms H2K5.Door.pads_of_offC
#print axioms H2K5.Door.cellsOwn_of_offC
