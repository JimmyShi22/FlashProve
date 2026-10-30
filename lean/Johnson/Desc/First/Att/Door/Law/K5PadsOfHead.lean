-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Desc/First/Att/Door/Law/K5PadsOfHead.lean: kind K5: A PAYMENT BENEATH THE KIND's FROZEN NAMED CONDITION (K5CondAt, K5LeftOfCond.lean): ITS FIELD pads := PadsAll h (K5RestCells.lean) FROM THE HEAD ALONE, AT THE FORMAT's CONCRETE SECOND HASH FUNCTION.

Compiled with the whole library.

(Where this and lean/THEOREM.md differ, the page holds.)

Why. K5PadsOfOffC.lean has pads from the named test offC (Johnson/P5J/HidBearsAtMg.lean). Another file shows that test under the head and the pin on what the planner made (Johnson/Top/H0/K2Ties/OffHead.lean: offC_head; the test accepts at the written values by a decision of Lean's kernel,
K2Ties/OffAt.lean: off_written); and the head's own entry tests give the pin (Johnson/P5T/FenceAtMg.lean: AtMg.pins; Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean: pinnedAt_of_row). Here: three calls.

Main names (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x):
  `pads_of_pin`: madePinnedAt … = true → PadsAll h.
  `pads_of_head`: **PadsAll h: NO PREMISE BUT THE HEAD.**
  `cellsOwn_of_head`: so the frozen per-group field gives what K5Rest's field cells spends: K5CellsCond h a x₁ idx → K5CellsOwn h g a x₁ idx.
Limits. AT OnBytes.secondHashFunction ALONE, not at every hash. The full size alone (the limit of Johnson/Top/H0/K2Ties/OffAt.lean). ONLY OVER A VERSION OF THE LIBRARY's FILES WHOSE HEAD's ENTRY TESTS ASK THE PIN (AtMg.pins).
Is it empty here? A MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE
LIBRARY AtFullSide/Top/).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5PadsOfOffC
import Johnson.Top.H0.K2Ties.OffHead
import Johnson.P5T.FenceAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.PlanWritten (madePinnedAt pinnedAt_of_row)
open P5J (AtMgA TS)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- The condition's field pads, under the pin on what the planner made. -/
theorem pads_of_pin (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) : PadsAll h :=
  pads_of_offC h (VerifiableInference.Desc.First.K2Ties.offC_head h.toAtMg hy)

/-- **The condition's field pads, from the head alone.** -/
theorem pads_of_head : PadsAll h :=
  pads_of_pin h (pinnedAt_of_row (by rw [h.toAtMg.pins.1, Bool.or_true]))

/-- The frozen per-group field gives the four that the field cells spends. -/
theorem cellsOwn_of_head (g : ℕ) {a : Attention.Plan} {x₁ : Look.Place} {idx : ℕ → ℕ} (C : K5CellsCond h a x₁ idx) :
    K5CellsOwn h g a x₁ idx := own_of_pads h (pads_of_head h) g C

end

end H2K5.Door

#print axioms H2K5.Door.pads_of_pin
#print axioms H2K5.Door.pads_of_head
#print axioms H2K5.Door.cellsOwn_of_head
