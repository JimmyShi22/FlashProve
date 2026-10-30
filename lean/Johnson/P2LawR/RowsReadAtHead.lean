-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/RowsReadAtHead.lean: UNDER THE HEAD OF THE CLOSED CONSTANT THE NAMED CONDITION
P5J.rowsRead Z (Johnson/Goal/Skeleton/RowsRead.lean) HOLDS. One theorem: one call each of
rows_at_head (Johnson/IMR/RadAtHead.lean: under the head the maker of the
sendings' rows returns: off the head's own field plan.radii) and of rowsRead_iff_returns_laid
(Johnson/P2LawR/RowsReadIsReturn.lean).
Why. A kind's law that takes rowsRead Z beside the head can be fed from the head.
  **AtMg.rowsRead_at_head**   see its statement.
Limits. IT DOES NOT MEET THE TOPS' CONDITION "owed": AT THE NAME THE HEAD IS ITSELF MADE WITH
rowsRead Z (Johnson/Goal/Skeleton/CondsOfLaid.lean: nine_of_laid): so this says only that whoever
has a head has the condition again: true as an implication, no payment in front of the head. NO
MEMBER: that a head can be had is not said. At OnBytes.secondHashFunction alone. Nothing on soundness.

-/
import Johnson.P2LawR.RowsReadIsReturn
import Johnson.IMR.RadAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)

/-- **UNDER THE HEAD THE NAMED CONDITION HOLDS.** -/
theorem AtMg.rowsRead_at_head {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    rowsRead Z := by
  obtain ⟨R, hR, -⟩ := IM.Seats.rows_at_head h
  exact (rowsRead_iff_returns_laid h.scope h.laid).2 ⟨R, hR⟩

end P5J

#print axioms P5J.AtMg.rowsRead_at_head
