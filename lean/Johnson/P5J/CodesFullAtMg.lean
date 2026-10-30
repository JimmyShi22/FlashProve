-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/CodesFullAtMg.lean: AT THE CONSTANT's OWN STRUCTURE (`AtMg`, AtMg.lean) THE CONSTANT's
THREE LETTERS FOR THE FIRST CHAIN's PARAMETERS ARE THE WRITTEN VALUES: At.cs Zp = codesFull2 ·
At.shape Zp = shapeFull · At.layout Zp = layoutFull. The third sibling of ShapeFullAtMg.lean's two,
and these two again at the constant's own letters. Theorems: calls; at every letter o for the
second hash function.

By: AtMg.pins (Johnson/P5T/FenceAtMg.lean) · pinnedAt_of_row · first_written_in_scope
(Johnson/Goal/Numbers/MadeInScope.lean: its first equation: the codes as read back are the written
sizes') · one closed fact, by the kernel: codes_written
(Johnson/Desc/Ok/PlanWritten/SizedTestLaws.lean: the written sizes' codes are codesFull2). At.cs Zp,
At.shape Zp, At.layout Zp ARE Zp.first's fields by definition (Johnson/P5J/LettersAt.lean;
Johnson/Desc/ProofFile/Pub.lean).

Why. K10's typed group and its payers stand at the literal codesFull2; the constant's letters at
At.cs Zp.

Limits. AtMg is a premise. Nothing on soundness.

-/
import Johnson.P5J.ShapeFullAtMg
import Johnson.Desc.Ok.PlanWritten.SizedTestLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference
open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (pinnedAt_of_row)
open VerifiableInference.PlanWritten.Joined (first_written_in_scope)
open OnBytes.Maker (WholeD)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **THE CONSTANT's CODES ARE THE WRITTEN ONES.** -/
theorem AtMg.codes_full (h : AtMg o Z D r Zp Np cF) : At.cs Zp = Johnson.G.codesFull2 := by
  have hZ : ProofFile.pureRoad.pub o Z.pol Z.lay Z.KL = .ok Zp := h.laid.pub
  exact (first_written_in_scope h.scope hZ
    (pinnedAt_of_row (by rw [h.pins.1, Bool.or_true]))).1.trans
    VerifiableInference.PlanWritten.codes_written

/-- The shape, at the constant's own letter. -/
theorem AtMg.shapeAt_full (h : AtMg o Z D r Zp Np cF) :
    At.shape Zp = VerifiableInference.Desc.ReqLit.shapeFull := h.shape_full

/-- The layout, at the constant's own letter. -/
theorem AtMg.layoutAt_full (h : AtMg o Z D r Zp Np cF) :
    At.layout Zp = Johnson.G.layoutFull := h.layout_full

end P5J

#print axioms P5J.AtMg.codes_full
#print axioms P5J.AtMg.shapeAt_full
#print axioms P5J.AtMg.layoutAt_full
